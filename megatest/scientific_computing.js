// @ts-check

/**
 * @typedef {Float64Array} Vector
 * @typedef {Float64Array} Matrix
 *
 * @typedef {{
*   x: number,
*   y: number,
*   z: number,
*   vx: number,
*   vy: number,
*   vz: number,
*   mass: number,
*   radius: number
* }} Particle
*/

/**
* N-body particle simulation with spatial partitioning
* Compiler hints:
* - All numeric operations use f64
* - Particles array is fixed-length
* - Grid cells are independent and can be parallelized
* - Inner loops are vectorizable
* - No dynamic memory allocation in main loop
*/
class ParticleSimulation {
 /**
  * @param {number} numParticles
  * @param {number} gridSize
  */
 constructor(numParticles, gridSize) {
   // Pre-allocate all buffers
   /** @type {Particle[]} */
   this.particles = new Array(numParticles);

   /** @type {number[][][]} */
   this.grid = Array(gridSize).fill(0).map(() =>
     Array(gridSize).fill(0).map(() =>
       Array(gridSize).fill(0)
     )
   );

   /** @type {Float64Array} */
   this.forces = new Float64Array(numParticles * 3);

   // Constants
   /** @const {number} */
   this.dt = 0.001;
   /** @const {number} */
   this.G = 6.67430e-11;
   /** @const {number} */
   this.softening = 1e-20;
 }

 /**
  * Update particle positions using velocity verlet integration
  * Compiler hints:
  * - Inner loops are independent
  * - Force calculations can be vectorized
  * - No branches in inner loop
  * @param {number} steps
  */
 simulate(steps) {
   for (let step = 0; step < steps; step++) {
     // Clear grid
     for (let i = 0; i < this.grid.length; i++) {
       for (let j = 0; j < this.grid.length; j++) {
         for (let k = 0; k < this.grid.length; k++) {
           this.grid[i][j][k] = 0;
         }
       }
     }

     // Assign particles to grid cells
     for (let i = 0; i < this.particles.length; i++) {
       const p = this.particles[i];
       const gx = Math.floor(p.x / this.grid.length);
       const gy = Math.floor(p.y / this.grid.length);
       const gz = Math.floor(p.z / this.grid.length);
       if (gx >= 0 && gx < this.grid.length &&
           gy >= 0 && gy < this.grid.length &&
           gz >= 0 && gz < this.grid.length) {
         this.grid[gx][gy][gz]++;
       }
     }

     // Calculate forces between particles in neighboring cells
     for (let i = 0; i < this.particles.length; i++) {
       const p1 = this.particles[i];
       const gx = Math.floor(p1.x / this.grid.length);
       const gy = Math.floor(p1.y / this.grid.length);
       const gz = Math.floor(p1.z / this.grid.length);

       // Clear forces for this particle
       this.forces[i * 3] = 0;
       this.forces[i * 3 + 1] = 0;
       this.forces[i * 3 + 2] = 0;

       // Check neighboring cells
       for (let dx = -1; dx <= 1; dx++) {
         for (let dy = -1; dy <= 1; dy++) {
           for (let dz = -1; dz <= 1; dz++) {
             const nx = gx + dx;
             const ny = gy + dy;
             const nz = gz + dz;

             if (nx >= 0 && nx < this.grid.length &&
                 ny >= 0 && ny < this.grid.length &&
                 nz >= 0 && nz < this.grid.length) {
               for (let j = 0; j < this.particles.length; j++) {
                 if (i === j) continue;
                 const p2 = this.particles[j];

                 // Check if p2 is in the neighboring cell
                 const p2x = Math.floor(p2.x / this.grid.length);
                 const p2y = Math.floor(p2.y / this.grid.length);
                 const p2z = Math.floor(p2.z / this.grid.length);

                 if (p2x === nx && p2y === ny && p2z === nz) {
                   const dx = p2.x - p1.x;
                   const dy = p2.y - p1.y;
                   const dz = p2.z - p1.z;

                   const distSqr = dx * dx + dy * dy + dz * dz + this.softening;
                   const dist = Math.sqrt(distSqr);

                   const force = this.G * p1.mass * p2.mass / (distSqr * dist);

                   this.forces[i * 3] += force * dx;
                   this.forces[i * 3 + 1] += force * dy;
                   this.forces[i * 3 + 2] += force * dz;
                 }
               }
             }
           }
         }
       }
     }

     // Update velocities and positions
     for (let i = 0; i < this.particles.length; i++) {
       const p = this.particles[i];
       const fx = this.forces[i * 3];
       const fy = this.forces[i * 3 + 1];
       const fz = this.forces[i * 3 + 2];

       // Update velocities (half step)
       const ax = fx / p.mass;
       const ay = fy / p.mass;
       const az = fz / p.mass;

       p.vx += ax * this.dt * 0.5;
       p.vy += ay * this.dt * 0.5;
       p.vz += az * this.dt * 0.5;

       // Update positions
       p.x += p.vx * this.dt;
       p.y += p.vy * this.dt;
       p.z += p.vz * this.dt;

       // Update velocities (half step)
       p.vx += ax * this.dt * 0.5;
       p.vy += ay * this.dt * 0.5;
       p.vz += az * this.dt * 0.5;
     }
   }
 }
}

/**
* Fast Fourier Transform implementation
* Compiler hints:
* - All arrays are power-of-two length
* - Complex numbers are represented as pairs of f64
* - Butterfly operations are vectorizable
* - No dynamic allocation in recursive calls
* @param {Float64Array} real
* @param {Float64Array} imag
* @param {boolean} inverse
*/
function fft(real, imag, inverse = false) {
 const n = real.length;

 // Base case
 if (n <= 1) return;

 // Split into even and odd
 const evenReal = new Float64Array(n / 2);
 const evenImag = new Float64Array(n / 2);
 const oddReal = new Float64Array(n / 2);
 const oddImag = new Float64Array(n / 2);

 for (let i = 0; i < n / 2; i++) {
   evenReal[i] = real[2 * i];
   evenImag[i] = imag[2 * i];
   oddReal[i] = real[2 * i + 1];
   oddImag[i] = imag[2 * i + 1];
 }

 // Recursive FFT on even/odd parts
 fft(evenReal, evenImag, inverse);
 fft(oddReal, oddImag, inverse);

 // Combine results
 const angle = (inverse ? 2 : -2) * Math.PI / n;
 let wr = 1;  // Real part of twiddle factor
 let wi = 0;  // Imaginary part of twiddle factor

 /** @const {number} */
 const cs = Math.cos(angle);
 /** @const {number} */
 const sn = Math.sin(angle);

 for (let i = 0; i < n / 2; i++) {
   const oddRealTemp = oddReal[i] * wr - oddImag[i] * wi;
   const oddImagTemp = oddReal[i] * wi + oddImag[i] * wr;

   real[i] = evenReal[i] + oddRealTemp;
   imag[i] = evenImag[i] + oddImagTemp;

   real[i + n/2] = evenReal[i] - oddRealTemp;
   imag[i + n/2] = evenImag[i] - oddImagTemp;

   // Update twiddle factor
   const wrNew = wr * cs - wi * sn;
   wi = wr * sn + wi * cs;
   wr = wrNew;
 }
}

/**
* Matrix multiplication optimized for cache and vectorization
* Compiler hints:
* - Matrix dimensions are compile-time constants
* - Matrices are stored in row-major order
* - Inner loops are vectorizable
* - Blocks are sized to fit in cache
* @param {Matrix} a
* @param {Matrix} b
* @param {Matrix} c
* @param {number} n
*/
function matrixMultiply(a, b, c, n) {
 /** @const {number} */
 const BLOCK_SIZE = 32;  // Tune based on cache size

 for (let i0 = 0; i0 < n; i0 += BLOCK_SIZE) {
   for (let j0 = 0; j0 < n; j0 += BLOCK_SIZE) {
     for (let k0 = 0; k0 < n; k0 += BLOCK_SIZE) {
       // Block multiplication
       const iLimit = Math.min(i0 + BLOCK_SIZE, n);
       const jLimit = Math.min(j0 + BLOCK_SIZE, n);
       const kLimit = Math.min(k0 + BLOCK_SIZE, n);

       for (let i = i0; i < iLimit; i++) {
         for (let j = j0; j < jLimit; j++) {
           let sum = 0;
           // This inner loop can be vectorized
           for (let k = k0; k < kLimit; k++) {
             sum += a[i * n + k] * b[k * n + j];
           }
           c[i * n + j] += sum;
         }
       }
     }
   }
 }
}

/**
* Conjugate Gradient solver for sparse matrices
* Compiler hints:
* - Sparse matrix in CSR format
* - All vectors are same fixed length
* - Inner products are vectorizable
* - No dynamic allocation in main loop
* @param {Float64Array} values - Non-zero values
* @param {Int32Array} colIndices - Column indices
* @param {Int32Array} rowPtr - Row pointers
* @param {Vector} b - Right-hand side
* @param {Vector} x - Solution vector
* @param {number} maxIter
* @param {number} tolerance
* @returns {number} - Number of iterations
*/
function conjugateGradient(values, colIndices, rowPtr, b, x, maxIter, tolerance) {
 const n = b.length;

 // Allocate vectors
 const r = new Float64Array(n);  // Residual
 const p = new Float64Array(n);  // Search direction
 const Ap = new Float64Array(n); // Matrix-vector product

 // r = b - Ax
 sparseMatrixVector(values, colIndices, rowPtr, x, Ap);
 for (let i = 0; i < n; i++) {
   r[i] = b[i] - Ap[i];
   p[i] = r[i];
 }

 let rsold = dotProduct(r, r);

 for (let iter = 0; iter < maxIter; iter++) {
   // Ap = A * p
   sparseMatrixVector(values, colIndices, rowPtr, p, Ap);

   // alpha = rsold / (p · Ap)
   const pAp = dotProduct(p, Ap);
   const alpha = rsold / pAp;

   // x = x + alpha * p
   // r = r - alpha * Ap
   for (let i = 0; i < n; i++) {
     x[i] += alpha * p[i];
     r[i] -= alpha * Ap[i];
   }

   const rsnew = dotProduct(r, r);
   if (Math.sqrt(rsnew) < tolerance) {
     return iter + 1;
   }

   // p = r + (rsnew / rsold) * p
   const beta = rsnew / rsold;
   for (let i = 0; i < n; i++) {
     p[i] = r[i] + beta * p[i];
   }

   rsold = rsnew;
 }

 return maxIter;
}

/**
* Sparse matrix-vector multiplication
* @param {Float64Array} values
* @param {Int32Array} colIndices
* @param {Int32Array} rowPtr
* @param {Vector} x
* @param {Vector} y
*/
function sparseMatrixVector(values, colIndices, rowPtr, x, y) {
 const n = rowPtr.length - 1;
 for (let i = 0; i < n; i++) {
   let sum = 0;
   for (let j = rowPtr[i]; j < rowPtr[i + 1]; j++) {
     sum += values[j] * x[colIndices[j]];
   }
   y[i] = sum;
 }
}

/**
* Vector dot product
* Compiler hint: Vectorizable reduction
* @param {Vector} a
* @param {Vector} b
* @returns {number}
*/
function dotProduct(a, b) {
 let sum = 0;
 for (let i = 0; i < a.length; i++) {
   sum += a[i] * b[i];
 }
 return sum;
}
