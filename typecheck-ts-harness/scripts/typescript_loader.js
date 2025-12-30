const fs = require("fs");
const path = require("path");
const { createRequire } = require("module");

function formatAttempt(label, basePath, err) {
  const suffix = err ? `: ${err.message ?? String(err)}` : "";
  return `- ${label} (${basePath})${suffix}`;
}

function loadTypeScript() {
  const attempts = [];

  const envDir = process.env.TYPECHECK_TS_HARNESS_TYPESCRIPT_DIR;
  if (envDir) {
    const basePath = path.resolve(envDir, "package.json");
    try {
      return createRequire(basePath)("typescript");
    } catch (err) {
      attempts.push(formatAttempt("env TYPECHECK_TS_HARNESS_TYPESCRIPT_DIR", basePath, err));
    }
  }

  const harnessRoot = path.resolve(__dirname, "..");
  const harnessPkg = path.join(harnessRoot, "package.json");
  if (fs.existsSync(harnessPkg)) {
    try {
      return createRequire(harnessPkg)("typescript");
    } catch (err) {
      attempts.push(formatAttempt("typecheck-ts-harness/package.json", harnessPkg, err));
    }
  } else {
    attempts.push(formatAttempt("typecheck-ts-harness/package.json missing", harnessPkg, null));
  }

  const repoRoot = path.resolve(__dirname, "..", "..");
  const tsSubmodulePkg = path.join(
    repoRoot,
    "parse-js",
    "tests",
    "TypeScript",
    "package.json",
  );
  if (fs.existsSync(tsSubmodulePkg)) {
    try {
      return createRequire(tsSubmodulePkg)("typescript");
    } catch (err) {
      attempts.push(formatAttempt("parse-js/tests/TypeScript/package.json", tsSubmodulePkg, err));
    }
  } else {
    attempts.push(formatAttempt("parse-js/tests/TypeScript/package.json missing", tsSubmodulePkg, null));
  }

  try {
    return require("typescript");
  } catch (err) {
    attempts.push(formatAttempt("default Node resolution", "require('typescript')", err));
  }

  const help = [
    "Cannot load the TypeScript compiler (`typescript` npm package).",
    "",
    "Install it locally (recommended):",
    "  cd typecheck-ts-harness && npm ci",
    "",
    "Or point the harness at an existing install:",
    "  export TYPECHECK_TS_HARNESS_TYPESCRIPT_DIR=/path/to/dir/with/node_modules",
    "",
    "Load attempts:",
    ...attempts,
  ].join("\n");

  throw new Error(help);
}

module.exports = { loadTypeScript };

