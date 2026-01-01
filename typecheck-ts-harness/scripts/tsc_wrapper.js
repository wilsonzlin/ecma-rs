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

function utf16ToUtf8ByteOffset(text, utf16Pos) {
  if (!text || utf16Pos <= 0) {
    return 0;
  }
  const target = Math.min(utf16Pos, text.length);
  let bytes = 0;
  let idx = 0;
  while (idx < target) {
    const code = text.charCodeAt(idx);
    if (code < 0x80) {
      bytes += 1;
      idx += 1;
      continue;
    }
    if (code < 0x800) {
      bytes += 2;
      idx += 1;
      continue;
    }
    if (code >= 0xd800 && code <= 0xdbff && idx + 1 < text.length) {
      const next = text.charCodeAt(idx + 1);
      if (next >= 0xdc00 && next <= 0xdfff && idx + 1 < target) {
        bytes += 4;
        idx += 2;
        continue;
      }
    }
    bytes += 3;
    idx += 1;
  }
  return bytes;
}

function utf8ByteOffsetToUtf16(text, bytePos) {
  if (!text || bytePos <= 0) {
    return 0;
  }

  let utf16Pos = 0;
  let bytes = 0;
  const target = Math.max(0, bytePos);
  while (utf16Pos < text.length && bytes < target) {
    const code = text.charCodeAt(utf16Pos);
    let charBytes = 0;
    let charLen = 1;
    if (code < 0x80) {
      charBytes = 1;
    } else if (code < 0x800) {
      charBytes = 2;
    } else if (code >= 0xd800 && code <= 0xdbff && utf16Pos + 1 < text.length) {
      const next = text.charCodeAt(utf16Pos + 1);
      if (next >= 0xdc00 && next <= 0xdfff) {
        charBytes = 4;
        charLen = 2;
      } else {
        charBytes = 3;
      }
    } else {
      charBytes = 3;
    }

    if (bytes + charBytes > target) {
      return utf16Pos;
    }
    bytes += charBytes;
    utf16Pos += charLen;
  }
  return utf16Pos;
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
  const startUtf16 = diagnostic.start ?? 0;
  const endUtf16 = (diagnostic.start ?? 0) + (diagnostic.length ?? 0);
  const text = diagnostic.file?.text;
  const start = text ? utf16ToUtf8ByteOffset(text, startUtf16) : startUtf16;
  const end = text ? utf16ToUtf8ByteOffset(text, endUtf16) : endUtf16;
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
