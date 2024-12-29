// Constants for memory layout and configuration
const WORD_SIZE = 8;
const PAGE_SIZE = 4096;
const MIN_ALLOC = 16;
const GENERATIONS = 3;
const ALIGNMENT = 8;

// Bit manipulation helpers
const align = x => (x + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1);
const setBit = (n, pos) => n | (1 << pos);
const clearBit = (n, pos) => n & ~(1 << pos);
const getBit = (n, pos) => (n >> pos) & 1;
const mask = bits => (1 << bits) - 1;

// Memory block header layout
const HEADER = {
  SIZE: 0,      // 24 bits
  GEN: 24,      // 2 bits
  FREE: 26,     // 1 bit
  MARKED: 27,   // 1 bit
  PINNED: 28,   // 1 bit
  NEXT: 32,     // 32 bits
};

// Block operations using TypedArrays
class Block {
  static headerSize = 8;

  constructor(buffer, offset = 0) {
    this.view = new DataView(buffer, offset);
  }

  get size() {
    return this.view.getUint32(HEADER.SIZE) & mask(24);
  }

  set size(value) {
    const current = this.view.getUint32(HEADER.SIZE);
    this.view.setUint32(HEADER.SIZE,
      (current & ~mask(24)) | (value & mask(24))
    );
  }

  get generation() {
    return (this.view.getUint32(HEADER.SIZE) >> HEADER.GEN) & mask(2);
  }

  set generation(value) {
    const current = this.view.getUint32(HEADER.SIZE);
    this.view.setUint32(HEADER.SIZE,
      (current & ~(mask(2) << HEADER.GEN)) |
      ((value & mask(2)) << HEADER.GEN)
    );
  }

  get isFree() {
    return getBit(this.view.getUint32(HEADER.SIZE), HEADER.FREE);
  }

  set isFree(value) {
    const current = this.view.getUint32(HEADER.SIZE);
    this.view.setUint32(HEADER.SIZE,
      value ? setBit(current, HEADER.FREE)
            : clearBit(current, HEADER.FREE)
    );
  }

  get isMarked() {
    return getBit(this.view.getUint32(HEADER.SIZE), HEADER.MARKED);
  }

  set isMarked(value) {
    const current = this.view.getUint32(HEADER.SIZE);
    this.view.setUint32(HEADER.SIZE,
      value ? setBit(current, HEADER.MARKED)
            : clearBit(current, HEADER.MARKED)
    );
  }

  get isPinned() {
    return getBit(this.view.getUint32(HEADER.SIZE), HEADER.PINNED);
  }

  set isPinned(value) {
    const current = this.view.getUint32(HEADER.SIZE);
    this.view.setUint32(HEADER.SIZE,
      value ? setBit(current, HEADER.PINNED)
            : clearBit(current, HEADER.PINNED)
    );
  }

  get next() {
    return this.view.getUint32(HEADER.NEXT);
  }

  set next(value) {
    this.view.setUint32(HEADER.NEXT, value);
  }

  get data() {
    return new Uint8Array(
      this.view.buffer,
      this.view.byteOffset + Block.headerSize,
      this.size - Block.headerSize
    );
  }
}

// Arena management
class Arena {
  constructor(size = PAGE_SIZE) {
    this.buffer = new ArrayBuffer(size);
    this.view = new DataView(this.buffer);
    this.freeList = new Array(GENERATIONS).fill(null)
      .map(() => new Array(32).fill(null));
    this.allocated = new Map();
    this.stats = {
      totalAllocated: 0,
      totalFreed: 0,
      collections: 0
    };

    // Initialize first free block
    const block = new Block(this.buffer);
    block.size = size;
    block.isFree = true;
    this.addToFreeList(block, 0);
  }

  // Allocation with size classes
  allocate(size) {
    size = align(size + Block.headerSize);
    if (size < MIN_ALLOC) size = MIN_ALLOC;

    // Find size class
    const sizeClass = Math.ceil(Math.log2(size));

    // Try to find free block in each generation
    for (let gen = 0; gen < GENERATIONS; gen++) {
      let block = this.findFreeBlock(size, sizeClass, gen);
      if (block) {
        this.removeFromFreeList(block, gen);
        return this.splitBlock(block, size, gen);
      }
    }

    // No suitable block found, trigger GC
    this.collectGarbage();

    // Try again after GC
    for (let gen = 0; gen < GENERATIONS; gen++) {
      let block = this.findFreeBlock(size, sizeClass, gen);
      if (block) {
        this.removeFromFreeList(block, gen);
        return this.splitBlock(block, size, gen);
      }
    }

    throw new Error('Out of memory');
  }

  // Free a block
  free(offset) {
    const block = new Block(this.buffer, offset);
    block.isFree = true;
    this.stats.totalFreed += block.size;

    // Coalesce with neighbors if possible
    const coalesced = this.coalesce(block);
    this.addToFreeList(coalesced, coalesced.generation);
  }

  // Find suitable free block
  findFreeBlock(size, sizeClass, generation) {
    // Look in size class and larger
    for (let sc = sizeClass; sc < 32; sc++) {
      const block = this.freeList[generation][sc];
      if (block && block.size >= size) {
        return block;
      }
    }
    return null;
  }

  // Split block if necessary
  splitBlock(block, size, generation) {
    const remaining = block.size - size;

    if (remaining >= MIN_ALLOC) {
      // Create new block from remainder
      const newBlock = new Block(
        this.buffer,
        block.view.byteOffset + size
      );
      newBlock.size = remaining;
      newBlock.generation = generation;
      newBlock.isFree = true;

      // Update original block
      block.size = size;
      this.addToFreeList(newBlock, generation);
    }

    block.isFree = false;
    block.generation = generation;
    this.stats.totalAllocated += block.size;
    return block.view.byteOffset;
  }

  // Add block to free list
  addToFreeList(block, generation) {
    const sizeClass = Math.ceil(Math.log2(block.size));
    block.next = this.freeList[generation][sizeClass]?.view.byteOffset ?? 0;
    this.freeList[generation][sizeClass] = block;
  }

  // Remove block from free list
  removeFromFreeList(block, generation) {
    const sizeClass = Math.ceil(Math.log2(block.size));
    if (this.freeList[generation][sizeClass] === block) {
      this.freeList[generation][sizeClass] =
        block.next ? new Block(this.buffer, block.next) : null;
    } else {
      let current = this.freeList[generation][sizeClass];
      while (current && current.next) {
        const next = new Block(this.buffer, current.next);
        if (next === block) {
          current.next = next.next;
          break;
        }
        current = next;
      }
    }
  }

  // Coalesce adjacent free blocks
  coalesce(block) {
    let result = block;
    let offset = block.view.byteOffset;

    // Try to coalesce with previous block
    if (offset > 0) {
      const prev = new Block(this.buffer, offset - Block.headerSize);
      if (prev.isFree) {
        this.removeFromFreeList(prev, prev.generation);
        prev.size += block.size;
        result = prev;
      }
    }

    // Try to coalesce with next block
    offset = result.view.byteOffset + result.size;
    if (offset < this.buffer.byteLength) {
      const next = new Block(this.buffer, offset);
      if (next.isFree) {
        this.removeFromFreeList(next, next.generation);
        result.size += next.size;
      }
    }

    return result;
  }

  // Generational garbage collection
  collectGarbage() {
    this.stats.collections++;

    // Mark phase
    this.markRoots();

    // Sweep phase for each generation
    for (let gen = 0; gen < GENERATIONS; gen++) {
      this.sweepGeneration(gen);
    }

    // Promote surviving objects
    this.promote();
  }

  // Mark from root set
  markRoots() {
    // Root set would be maintained elsewhere
    // This is just a placeholder
    for (const [offset, ref] of this.allocated) {
      const block = new Block(this.buffer, offset);
      if (!block.isFree && !block.isMarked) {
        this.markBlock(block);
      }
    }
  }

  // Mark single block and its references
  markBlock(block) {
    if (block.isMarked) return;
    block.isMarked = true;

    // Would traverse references here
    // This is just a placeholder
    const data = block.data;
    // ... traverse references in data
  }

  // Sweep a generation
  sweepGeneration(generation) {
    let offset = 0;
    while (offset < this.buffer.byteLength) {
      const block = new Block(this.buffer, offset);

      if (!block.isFree && block.generation === generation) {
        if (!block.isMarked && !block.isPinned) {
          this.free(offset);
        } else {
          block.isMarked = false;
        }
      }

      offset += block.size;
    }
  }

  // Promote surviving objects to older generation
  promote() {
    let offset = 0;
    while (offset < this.buffer.byteLength) {
      const block = new Block(this.buffer, offset);

      if (!block.isFree && block.generation < GENERATIONS - 1) {
        block.generation++;
      }

      offset += block.size;
    }
  }
}

// Example usage
const arena = new Arena(1024 * 1024);  // 1MB arena

// Allocate some blocks
const block1 = arena.allocate(100);
const block2 = arena.allocate(200);
const block3 = arena.allocate(300);

// Free some blocks
arena.free(block2);

// Trigger GC
arena.collectGarbage();
