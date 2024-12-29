"use strict";

/**
 * ------------------------------
 * Type Hints (Comments Only)
 * ------------------------------
 *
 * @typedef {number | string} NumOrStr       // Example union type
 *
 * @typedef {Object} Point2D
 * @property {number} x
 * @property {number} y
 *
 * @typedef {Object} ComplexNumber
 * @property {number} real
 * @property {number} imag
 *
 * @typedef {("Red" | "Green" | "Blue")} ColorEnum
 * A pseudo-enum to represent color values.
 */

/** @type {NumOrStr} */
let globalVar = 42;  // Could also be "hello world", testing union type usage

/**
 * A helper function to demonstrate default parameters, rest/spread,
 * destructuring, and typed arrays.
 */

/**
 * @param {Point2D}  start    - Start of the line
 * @param {Point2D}  end      - End of the line
 * @param {number}   [factor=2] - Optional scaling factor
 * @param {...number} offsets - Extra offsets to be added to x and y
 * @returns {Point2D}         - A new point after scaling and offset
 */
function transformPoint({ x: sx, y: sy }, { x: ex, y: ey }, factor = 2, ...offsets) {
  let dx = (ex - sx) * factor;
  let dy = (ey - sy) * factor;

  // Summation of all offsets
  let offsetSum = 0;
  for (const offset of offsets) {
    offsetSum += offset;
  }

  return {
    x: sx + dx + offsetSum,
    y: sy + dy + offsetSum
  };
}

/**
 * Demonstrate usage of a typed array (Int32Array).
 * This function sums the elements of a typed array.
 *
 * @param {Int32Array} arr
 * @returns {number}
 */
function sumInt32Array(arr) {
  let sum = 0;
  for (let i = 0; i < arr.length; i++) {
    sum += arr[i];
  }
  return sum;
}

/**
 * Demonstrate usage of big integer operations.
 * Note: Must be in a modern JS environment that supports BigInt.
 *
 * @param {bigint} a
 * @param {bigint} b
 * @returns {bigint}
 */
function multiplyBigInt(a, b) {
  return a * b;
}

/**
 * Example of a constructor function + vtable-like structure
 * for more “native” OOP usage.
 *
 * @param {number} real
 * @param {number} imag
 * @constructor
 */
function Complex(real, imag) {
  /** @type {ComplexNumber} */
  this._value = { real: real, imag: imag };
}

/**
 * Add a method via prototype (simulating a "vtable entry").
 * @param {Complex} other
 * @returns {Complex}
 */
Complex.prototype.add = function (other) {
  this._value.real += other._value.real;
  this._value.imag += other._value.imag;
  return this;
};

/**
 * Example class that extends another class.
 * Demonstrates class syntax, inheritance, and method overriding.
 */
class ColoredComplex extends Complex {
  /**
   * @param {number} real
   * @param {number} imag
   * @param {ColorEnum} color
   */
  constructor(real, imag, color) {
    super(real, imag);
    // Illustrates union-type usage as well as enumerations.
    /** @type {ColorEnum} */
    this.color = color;
  }

  /**
   * Overridden add method that also logs color changes.
   * @param {Complex} other
   * @returns {ColoredComplex}
   */
  add(other) {
    super.add(other);
    // Just a contrived usage of color (no real effect).
    if (this.color === "Red") {
      this._value.real += 0.1;  // tiny tweak if Red
    }
    return this;
  }
}

/**
 * A function that might never be used (tests dead code elimination).
 */
function unusedFunction() {
  return "I'm never called!";
}

/**
 * Showcases arrow functions, closures, and partial type hints.
 *
 * @param {number} base
 * @returns {(x: number) => number}
 */
const makeAdder = (base /* : number */) => {
  return (x) => base + x;
};

/**
 * Simple factorial to demonstrate recursion.
 *
 * @param {number} n
 * @returns {number}
 */
function factorial(n) {
  if (n <= 1) return 1;
  return n * factorial(n - 1);
}

/**
 * Main test function to tie everything together.
 */
function main() {
  // 1) Destructuring and default param usage
  const p1 = { x: 1, y: 1 };
  const p2 = { x: 3, y: 4 };
  const newPoint = transformPoint(p1, p2, 3, 5, -2);
  console.log("Transformed Point:", newPoint);

  // 2) Summation with typed array
  const intArray = new Int32Array([1, 2, 3, 4, 5]);
  console.log("Sum of Int32Array:", sumInt32Array(intArray));

  // 3) BigInt usage
  const big1 = 1234567890123456789n;
  const big2 = 9876543210987654321n;
  console.log("BigInt multiplication:", multiplyBigInt(big1, big2));

  // 4) Complex usage
  const c1 = new Complex(1, 2);
  const c2 = new Complex(3, 4);
  c1.add(c2);
  console.log("Complex c1 after add:", c1._value);

  // 5) ColoredComplex usage
  const cc1 = new ColoredComplex(1, 2, "Red");
  cc1.add(new Complex(3, 4));
  console.log("ColoredComplex cc1 after add:", cc1._value, "color =", cc1.color);

  // 6) Factorial recursion
  console.log("Factorial of 5:", factorial(5));

  // 7) Closures with arrow functions
  const addTen = makeAdder(10);
  console.log("10 + 5:", addTen(5));

  // 8) Optional chaining demonstration
  // If globalVar is a string, call .toUpperCase()
  // If globalVar is a number, optional chain toString, else undefined if it's not available
  let maybeString = typeof globalVar === "string" ? globalVar.toUpperCase?.() : globalVar?.toString?.();
  console.log("Optional chain result for globalVar:", maybeString);
}

// Execute main to run the tests
main();
