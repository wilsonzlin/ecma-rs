// Minimal manual test for the Node.js bindings. Run after building the native addon.

const assert = require("assert");
const { minify } = require("./index.js");

const result = minify("global", Buffer.from("let x = 1;", "utf8"));

assert(Buffer.isBuffer(result), "minify should return a Buffer");
assert.strictEqual(result.toString("utf8"), "let x=1;");

console.log("minify returned UTF-8 Buffer output:", result.toString("utf8"));
