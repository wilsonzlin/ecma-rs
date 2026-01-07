const assert = require("assert");
const { minify } = require("./index.js");

const utf8 = (buf) => buf.toString("utf8");

const expectMinify = (mode, src, expected) => {
  const srcBuffer = Buffer.from(src, "utf8");
  const resultFromBuffer = minify(mode, srcBuffer);
  const resultFromString = minify(mode, src);

  assert(Buffer.isBuffer(resultFromBuffer), "minify should return a Buffer");
  assert(Buffer.isBuffer(resultFromString), "minify should return a Buffer");
  assert.strictEqual(utf8(resultFromBuffer), expected);
  assert.strictEqual(utf8(resultFromString), expected);
};

assert.strictEqual(typeof minify, "function", "minify export should be a function");

expectMinify("global", "let x = 1;", "let x=1;");
expectMinify("module", "export default 1;", "export default 1;");
expectMinify(
  "module",
  "const enum E { A = 1 } export const x = E.A;",
  "export const x=1;",
);

// Preserve const enums at runtime when requested.
const preservedConstEnum = utf8(
  minify("module", 'eval("x");const enum E{A=1}export const x=E.A;', {
    dialect: "ts",
    preserveConstEnums: true,
  }),
);
assert(
  preservedConstEnum.includes("var E") || preservedConstEnum.includes("let E"),
  `expected preserve mode to emit runtime enum scaffolding, got: ${preservedConstEnum}`,
);
assert(
  preservedConstEnum.includes("export const x=E.A"),
  `expected preserve mode to keep enum member access, got: ${preservedConstEnum}`,
);

// Legacy option name should continue to work.
const preservedConstEnumLegacy = utf8(
  minify("module", 'eval("x");const enum E{A=1}export const x=E.A;', {
    dialect: "ts",
    tsPreserveConstEnums: true,
  }),
);
assert(
  preservedConstEnumLegacy.includes("var E") ||
    preservedConstEnumLegacy.includes("let E"),
  `expected legacy option to emit runtime enum scaffolding, got: ${preservedConstEnumLegacy}`,
);
assert(
  preservedConstEnumLegacy.includes("export const x=E.A"),
  `expected legacy option to keep enum member access, got: ${preservedConstEnumLegacy}`,
);

// Passing both option names with conflicting values should throw.
assert.throws(
  () =>
    minify("module", 'eval("x");const enum E{A=1}export const x=E.A;', {
      dialect: "ts",
      preserveConstEnums: true,
      tsPreserveConstEnums: false,
    }),
  (err) => err instanceof TypeError && err.message.includes("must match"),
);

// Invalid JavaScript should surface deterministic diagnostics.
try {
  minify("global", "let x = ;");
  assert.fail("minify should throw on invalid JS input");
} catch (err) {
  assert(err instanceof Error, "error should be an Error");
  assert(Array.isArray(err.diagnostics), "error should include a diagnostics array");
  assert(err.diagnostics.length > 0, "error should include at least one diagnostic");
  assert.strictEqual(
    err.diagnostics[0].code,
    "PS0002",
    "first diagnostic code should match the parse error code for this fixture",
  );
  assert(
    err.message.includes(err.diagnostics[0].code),
    "error message should include the diagnostic code",
  );
}

// Argument validation should be surfaced as TypeError.
assert.throws(
  () => minify("invalid", "let x = 1;"),
  (err) => err instanceof TypeError && err.message.includes("top-level mode"),
);
assert.throws(
  () => minify("global", 123),
  (err) => err instanceof TypeError && err.message.includes("src must be"),
);

console.log("minify-js-nodejs: all tests passed");
