#!/usr/bin/env node
const path = require("path");
const { loadTypeScript } = require("./typescript_loader");
let ts;
try {
  ts = loadTypeScript();
} catch (err) {
  console.error(err?.message ?? String(err));
  process.exit(1);
}

function categoryToString(category) {
  switch (category) {
    case ts.DiagnosticCategory.Message:
      return "message";
    case ts.DiagnosticCategory.Warning:
      return "warning";
    case ts.DiagnosticCategory.Suggestion:
      return "suggestion";
    case ts.DiagnosticCategory.Error:
    default:
      return "error";
  }
}

function formatMessage(messageText) {
  return ts.flattenDiagnosticMessageText(messageText, "\n");
}

function serializeDiagnostic(diagnostic) {
  const start = diagnostic.start ?? 0;
  const end = (diagnostic.start ?? 0) + (diagnostic.length ?? 0);
  return {
    code: diagnostic.code,
    category: categoryToString(diagnostic.category),
    file: diagnostic.file
      ? path.relative(process.cwd(), diagnostic.file.fileName)
      : null,
    start,
    end,
    message: formatMessage(diagnostic.messageText),
  };
}

function loadHarnessOptions() {
  const raw = process.env.HARNESS_OPTIONS;
  if (!raw) {
    return {};
  }

  try {
    const parsed = JSON.parse(raw);
    const converted = ts.convertCompilerOptionsFromJson(parsed, process.cwd(), undefined);
    if (converted.errors && converted.errors.length) {
      converted.errors.forEach((d) => {
        console.error(formatMessage(d.messageText));
      });
      process.exit(1);
    }
    return converted.options || {};
  } catch (err) {
    console.error("failed to parse HARNESS_OPTIONS", err);
    process.exit(1);
  }
}

function main() {
  const files = process.argv.slice(2);
  if (files.length === 0) {
    console.error("tsc_wrapper: expected at least one file argument");
    process.exit(1);
  }

  const options = {
    noEmit: true,
    pretty: false,
    skipLibCheck: true,
    ...loadHarnessOptions(),
  };

  const program = ts.createProgram({ rootNames: files, options });
  const diagnostics = ts.getPreEmitDiagnostics(program);
  const serialized = diagnostics.map(serializeDiagnostic);
  const payload = { diagnostics: serialized };
  process.stdout.write(JSON.stringify(payload));
}

main();
