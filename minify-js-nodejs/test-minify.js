// Minimal manual test for the Node.js bindings. Run after building the native addon.

const assert = require("assert");
const { minify } = require("./index.js");

const result = minify("global", Buffer.from("let x = 1;", "utf8"));

assert(Buffer.isBuffer(result), "minify should return a Buffer");
assert.strictEqual(result.toString("utf8"), "let x=1;");

console.log("minify returned UTF-8 Buffer output:", result.toString("utf8"));

try {
  minify("global", "bad");
  assert.fail("minify should throw on invalid input");
} catch (err) {
  assert(err instanceof Error, "error should be an Error");
  assert(
    Array.isArray(err.diagnostics),
    "error should include a diagnostics array",
  );
  assert(
    err.message.includes("PARSE"),
    "error message should include a PARSE code",
  );
}

console.log("minify threw with diagnostics for invalid input");
