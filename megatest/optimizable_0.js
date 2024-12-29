// @ts-check
// This program creates opportunities for:
// - Method inlining
// - Class hierarchy analysis and vtable optimization
// - Monomorphization of generic data structures
// - Type inference and bounds checking elimination
// - Loop invariant code motion
// - Dead code elimination
// - Array bounds check elimination
// - Object shape analysis and property access optimization

// Type definitions to aid compiler
/** @typedef {{x: number, y: number, z: number}} Vector3D */
/** @typedef {number} Timestamp */
/** @typedef {{pos: Vector3D, vel: Vector3D, mass: number}} Particle */

// Generic tree node that can be monomorphized
class TreeNode {
  /** @type {T} */ value;
  /** @type {TreeNode<T>[]} */ children;

  /**
   * @template T
   * @param {T} value
   */
  constructor(value) {
      this.value = value;
      this.children = [];
  }

  /**
   * @template T
   * @param {(value: T) => boolean} predicate
   * @returns {TreeNode<T> | null}
   */
  find(predicate) {
      if (predicate(this.value)) return this;
      for (const child of this.children) {
          const result = child.find(predicate);
          if (result) return result;
      }
      return null;
  }
}

// Class hierarchy for virtual method optimization
class Shape {
  /** @type {Vector3D} */ pos;

  /** @returns {number} */
  get volume() { throw new Error("Abstract"); }

  /** @returns {number} */
  get surfaceArea() { throw new Error("Abstract"); }
}

class Sphere extends Shape {
  /** @type {number} */ radius;

  /**
   * @param {number} radius
   * @param {Vector3D} pos
   */
  constructor(radius, pos) {
      super();
      this.radius = radius;
      this.pos = pos;
  }

  get volume() {
      return (4/3) * Math.PI * Math.pow(this.radius, 3);
  }

  get surfaceArea() {
      return 4 * Math.PI * Math.pow(this.radius, 2);
  }
}

class Box extends Shape {
  /** @type {Vector3D} */ dimensions;

  /**
   * @param {Vector3D} dimensions
   * @param {Vector3D} pos
   */
  constructor(dimensions, pos) {
      super();
      this.dimensions = dimensions;
      this.pos = pos;
  }

  get volume() {
      return this.dimensions.x * this.dimensions.y * this.dimensions.z;
  }

  get surfaceArea() {
      const {x, y, z} = this.dimensions;
      return 2 * (x*y + y*z + x*z);
  }
}

// Particle system simulation with vectorized operations
class ParticleSystem {
  /** @type {Particle[]} */ particles;
  /** @type {number} */ dt;

  constructor() {
      this.particles = [];
      this.dt = 0.016; // 60fps
  }

  /** @param {Particle} p */
  addParticle(p) {
      this.particles.push(p);
  }

  // Update all particles - vectorizable loop
  update() {
      const dt = this.dt;
      for (let i = 0; i < this.particles.length; i++) {
          const p = this.particles[i];
          // Update position
          p.pos.x += p.vel.x * dt;
          p.pos.y += p.vel.y * dt;
          p.pos.z += p.vel.z * dt;

          // Apply simple gravity
          p.vel.y -= 9.81 * dt;
      }
  }

  // Complex particle interaction - opportunity for loop optimization
  /** @returns {number} */
  calculateTotalEnergy() {
      let total = 0;

      for (let i = 0; i < this.particles.length; i++) {
          const p = this.particles[i];
          // Kinetic energy
          const v2 = p.vel.x * p.vel.x + p.vel.y * p.vel.y + p.vel.z * p.vel.z;
          total += 0.5 * p.mass * v2;

          // Potential energy
          total += p.mass * 9.81 * p.pos.y;
      }

      return total;
  }
}

// Main simulation loop with multiple optimization opportunities
function runSimulation() {
  // Create shape hierarchy for virtual method optimization
  /** @type {Shape[]} */ const shapes = [
      new Sphere(1.0, {x: 0, y: 0, z: 0}),
      new Box({x: 2, y: 2, z: 2}, {x: 3, y: 0, z: 0})
  ];

  // Create particle system
  const system = new ParticleSystem();

  // Add particles near each shape
  for (const shape of shapes) {
      const pos = shape.pos;
      const numParticles = shape.volume > 10 ? 1000 : 500;

      for (let i = 0; i < numParticles; i++) {
          system.addParticle({
              pos: {
                  x: pos.x + Math.random() - 0.5,
                  y: pos.y + Math.random() - 0.5,
                  z: pos.z + Math.random() - 0.5
              },
              vel: {
                  x: Math.random() - 0.5,
                  y: Math.random() * 2,
                  z: Math.random() - 0.5
              },
              mass: 0.1
          });
      }
  }

  // Create tree structure for monomorphization
  const root = new TreeNode(system);

  // Run simulation steps
  const numSteps = 1000;
  /** @type {number[]} */ const energyHistory = new Array(numSteps);

  for (let step = 0; step < numSteps; step++) {
      system.update();
      energyHistory[step] = system.calculateTotalEnergy();

      // Complex tree operation that can be optimized
      const highEnergyNode = root.find(sys => sys.calculateTotalEnergy() > 1000);
      if (highEnergyNode) {
          // Do something with high energy state
          const energy = highEnergyNode.value.calculateTotalEnergy();
          console.log(`High energy state detected: ${energy}`);
      }
  }

  return energyHistory;
}

// Run the simulation
const results = runSimulation();
console.log(`Final energy: ${results[results.length - 1]}`);
