#!/usr/bin/env node
// Minimal NDJSON TypeScript runner for the Rust harness.
const path = require("path");
const readline = require("readline");
const { loadTypeScript } = require("./typescript_loader");
let ts;
try {
  ts = loadTypeScript();
} catch (err) {
  process.stderr.write(`${err?.message ?? String(err)}\n`);
  process.exit(1);
}

const VIRTUAL_ROOT = "/";
const SCHEMA_VERSION = 2;

function normalizePath(fileName) {
  return path.posix.normalize(fileName.replace(/\\/g, "/"));
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
    // Surrogate pair (UTF-16 uses 2 code units, UTF-8 uses 4 bytes).
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

function toAbsolute(fileName) {
  const normalized = normalizePath(fileName);
  return path.posix.isAbsolute(normalized)
    ? normalized
    : path.posix.join(VIRTUAL_ROOT, normalized);
}

function collectVirtualDirectories(fileNames) {
  const dirs = new Set([VIRTUAL_ROOT]);
  for (const fileName of fileNames) {
    let dir = path.posix.dirname(fileName);
    while (dir && !dirs.has(dir)) {
      dirs.add(dir);
      const parent = path.posix.dirname(dir);
      if (parent === dir) {
        break;
      }
      dir = parent;
    }
  }
  return dirs;
}

function listVirtualSubdirectories(dirName, virtualDirectories) {
  const dir = dirName.endsWith("/") ? dirName : `${dirName}/`;
  const children = new Set();
  for (const candidate of virtualDirectories) {
    if (!candidate.startsWith(dir) || candidate === dirName) {
      continue;
    }
    const remainder = candidate.slice(dir.length);
    if (!remainder) {
      continue;
    }
    const next = remainder.split("/")[0];
    if (next) {
      children.add(path.posix.join(dirName, next));
    }
  }
  return Array.from(children);
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

function flattenMessage(messageText) {
  return ts.flattenDiagnosticMessageText(messageText, "\n");
}

function computeLineStarts(text) {
  const starts = [0];
  for (let idx = 0; idx < text.length; idx++) {
    const ch = text.charCodeAt(idx);
    if (ch === 13 /* \r */) {
      if (text.charCodeAt(idx + 1) === 10 /* \n */) {
        idx++;
      }
      starts.push(idx + 1);
    } else if (ch === 10 /* \n */) {
      starts.push(idx + 1);
    }
  }
  return starts;
}

function collectTypeQueries(files) {
  const queries = [];
  for (const [rawName, text] of Object.entries(files || {})) {
    const normalized = normalizePath(rawName);
    const lineStarts = computeLineStarts(text);
    const lines = text.split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      let search = line.indexOf("^?");
      while (search !== -1) {
        const before = line.slice(0, search);
        const hasCodeBefore =
          before.trim().length > 0 && !before.trim().startsWith("//");
        const targetLine = hasCodeBefore ? i : i - 1;
        if (targetLine >= 0) {
          const startUtf16 = lineStarts[targetLine] ?? 0;
          const endUtf16 = lineStarts[targetLine + 1] ?? text.length;
          const columnUtf16 = Math.min(search, endUtf16 - startUtf16);
          const offsetUtf16 = startUtf16 + columnUtf16;
          const offset = utf16ToUtf8ByteOffset(text, offsetUtf16);
          const startBytes = utf16ToUtf8ByteOffset(text, startUtf16);
          const column = offset - startBytes;
          queries.push({
            file: normalized,
            offset,
            line: targetLine,
            column,
          });
        }
        search = line.indexOf("^?", search + 2);
      }
    }
  }
  return queries;
}

function splitTopLevel(raw, delim) {
  const parts = [];
  let start = 0;
  let depthParen = 0;
  let depthBrace = 0;
  let depthBracket = 0;
  let depthAngle = 0;
  for (let idx = 0; idx < raw.length; idx++) {
    const ch = raw[idx];
    switch (ch) {
      case "(":
        depthParen++;
        break;
      case ")":
        depthParen--;
        break;
      case "{":
        depthBrace++;
        break;
      case "}":
        depthBrace--;
        break;
      case "[":
        depthBracket++;
        break;
      case "]":
        depthBracket--;
        break;
      case "<":
        depthAngle++;
        break;
      case ">":
        depthAngle--;
        break;
      default:
    }
    if (
      ch === delim &&
      depthParen === 0 &&
      depthBrace === 0 &&
      depthBracket === 0 &&
      depthAngle === 0
    ) {
      parts.push(raw.slice(start, idx).trim());
      start = idx + 1;
    }
  }
  if (parts.length === 0) {
    return null;
  }
  parts.push(raw.slice(start).trim());
  return parts;
}

function stripParamNames(params) {
  const parts = [];
  let start = 0;
  let depthParen = 0;
  let depthBrace = 0;
  let depthBracket = 0;
  let depthAngle = 0;
  for (let idx = 0; idx < params.length; idx++) {
    const ch = params[idx];
    switch (ch) {
      case "(":
        depthParen++;
        break;
      case ")":
        depthParen--;
        break;
      case "{":
        depthBrace++;
        break;
      case "}":
        depthBrace--;
        break;
      case "[":
        depthBracket++;
        break;
      case "]":
        depthBracket--;
        break;
      case "<":
        depthAngle++;
        break;
      case ">":
        depthAngle--;
        break;
      case ",":
        if (
          depthParen === 0 &&
          depthBrace === 0 &&
          depthBracket === 0 &&
          depthAngle === 0
        ) {
          parts.push(params.slice(start, idx).trim());
          start = idx + 1;
        }
        break;
      default:
    }
  }
  parts.push(params.slice(start).trim());

  const normalized = [];
  for (const part of parts) {
    if (!part) continue;
    let depthP = 0;
    let depthB = 0;
    let depthBr = 0;
    let depthA = 0;
    let colon = -1;
    for (let idx = 0; idx < part.length; idx++) {
      const ch = part[idx];
      switch (ch) {
        case "(":
          depthP++;
          break;
        case ")":
          depthP--;
          break;
        case "{":
          depthB++;
          break;
        case "}":
          depthB--;
          break;
        case "[":
          depthBr++;
          break;
        case "]":
          depthBr--;
          break;
        case "<":
          depthA++;
          break;
        case ">":
          depthA--;
          break;
        case ":":
          if (
            depthP === 0 &&
            depthB === 0 &&
            depthBr === 0 &&
            depthA === 0
          ) {
            colon = idx;
            idx = part.length;
          }
          break;
        default:
      }
    }
    if (colon === -1) {
      normalized.push(part.trim());
      continue;
    }
    const rest = part.slice(colon + 1).trim();
    const isRest = part.trimStart().startsWith("...");
    normalized.push(isRest ? `...${rest}` : rest);
  }

  return normalized.join(", ");
}

function normalizeTypeString(raw) {
  const collapsed = raw.split(/\s+/).join(" ").trim();
  const union = splitTopLevel(collapsed, "|");
  if (union && union.length) {
    const normalized = union
      .filter(Boolean)
      .map((part) => normalizeTypeString(part));
    normalized.sort();
    return Array.from(new Set(normalized)).join(" | ");
  }
  const intersections = splitTopLevel(collapsed, "&");
  if (intersections && intersections.length) {
    const normalized = intersections
      .filter(Boolean)
      .map((part) => normalizeTypeString(part));
    normalized.sort();
    return Array.from(new Set(normalized)).join(" & ");
  }

  const arrowIdx = collapsed.indexOf("=>");
  if (arrowIdx !== -1) {
    const paramsPart = collapsed.slice(0, arrowIdx).trimEnd();
    const retPart = collapsed.slice(arrowIdx + 2).trimStart();
    const startParen = paramsPart.lastIndexOf("(");
    if (startParen !== -1 && paramsPart.endsWith(")")) {
      const params = paramsPart.slice(startParen + 1, paramsPart.length - 1);
      const before = paramsPart.slice(0, startParen).trim();
      const stripped = stripParamNames(params);
      const ret = normalizeTypeString(retPart);
      return `${before ? `${before}` : ""}(${stripped}) => ${ret}`;
    }
  }

  return collapsed;
}

const TYPE_FORMAT_FLAGS =
  ts.TypeFormatFlags.NoTruncation | ts.TypeFormatFlags.WriteArrowStyleSignature;

function renderType(checker, type, context) {
  return normalizeTypeString(
    checker.typeToString(type, context, TYPE_FORMAT_FLAGS),
  );
}

function collectExportTypes(checker, sourceFile) {
  const moduleSymbol = checker.getSymbolAtLocation(sourceFile);
  if (!moduleSymbol) {
    return [];
  }
  const exports = checker.getExportsOfModule(moduleSymbol) || [];
  const facts = [];
  for (const sym of exports) {
    const target =
      sym.getFlags() & ts.SymbolFlags.Alias
        ? checker.getAliasedSymbol(sym)
        : sym;
    if ((target.getFlags() & ts.SymbolFlags.Value) === 0) {
      continue;
    }
    const decl =
      target.valueDeclaration ||
      (target.declarations && target.declarations[0]) ||
      sourceFile;
    const type = checker.getTypeOfSymbolAtLocation(target, decl);
    const typeStr = renderType(checker, type, decl);
    facts.push({
      file: path.posix.relative(VIRTUAL_ROOT, normalizePath(sourceFile.fileName)),
      name: sym.getName(),
      type: typeStr,
    });
  }
  return facts;
}

function collectMarkerTypes(checker, markers, sourceFiles) {
  const facts = [];
  for (const marker of markers) {
    const absName = toAbsolute(marker.file);
    const sf = sourceFiles.get(absName);
    if (!sf) continue;
    const offsetUtf16 = utf8ByteOffsetToUtf16(sf.text, marker.offset);
    const node =
      ts.findPrecedingToken(offsetUtf16, sf) ??
      ts.getTokenAtPosition(sf, offsetUtf16);
    if (!node) continue;
    const type = checker.getTypeAtLocation(node);
    const typeStr = renderType(checker, type, node);
    facts.push({
      file: path.posix.relative(VIRTUAL_ROOT, normalizePath(sf.fileName)),
      offset: marker.offset,
      line: marker.line,
      column: marker.column,
      type: typeStr,
    });
  }
  return facts;
}

function collectTypeFacts(program, checker, markers, requestFiles) {
  const sourceFiles = new Map();
  for (const sf of program.getSourceFiles()) {
    sourceFiles.set(normalizePath(sf.fileName), sf);
  }
  const exports = [];
  const requestNames = Object.keys(requestFiles || {}).slice().sort();
  for (const rawName of requestNames) {
    const absName = toAbsolute(rawName);
    const sf = sourceFiles.get(absName);
    if (!sf) continue;
    exports.push(...collectExportTypes(checker, sf));
  }
  const markerFacts = collectMarkerTypes(checker, markers, sourceFiles);
  if (exports.length === 0 && markerFacts.length === 0) {
    return null;
  }

  exports.sort((a, b) =>
    [
      (a.file ?? "").localeCompare(b.file ?? ""),
      (a.name ?? "").localeCompare(b.name ?? ""),
      (a.type ?? "").localeCompare(b.type ?? ""),
    ].find((value) => value !== 0) ?? 0,
  );
  markerFacts.sort((a, b) =>
    [
      (a.file ?? "").localeCompare(b.file ?? ""),
      (a.offset ?? 0) - (b.offset ?? 0),
      (a.type ?? "").localeCompare(b.type ?? ""),
    ].find((value) => value !== 0) ?? 0,
  );
  return { exports, markers: markerFacts };
}

function serializeDiagnostic(diagnostic) {
  const startUtf16 = diagnostic.start ?? 0;
  const endUtf16 = (diagnostic.start ?? 0) + (diagnostic.length ?? 0);
  const fileName = diagnostic.file ? toAbsolute(diagnostic.file.fileName) : null;
  const relative = fileName ? path.posix.relative(VIRTUAL_ROOT, fileName) : null;
  const text = diagnostic.file?.text;
  const start = text ? utf16ToUtf8ByteOffset(text, startUtf16) : startUtf16;
  const end = text ? utf16ToUtf8ByteOffset(text, endUtf16) : endUtf16;

  return {
    code: diagnostic.code,
    category: categoryToString(diagnostic.category),
    file: relative,
    start,
    end,
    message: flattenMessage(diagnostic.messageText),
  };
}

function serializeDiagnostics(diagnostics) {
  return diagnostics
    .map(serializeDiagnostic)
    .sort((a, b) =>
      [
        (a.file ?? "").localeCompare(b.file ?? ""),
        a.start - b.start,
        a.end - b.end,
        a.code - b.code,
      ].find((value) => value !== 0) ?? 0,
    );
}

function parseOptions(rawOptions) {
  const defaults = { noEmit: true, skipLibCheck: true, pretty: false };
  const merged = { ...defaults, ...(rawOptions ?? {}) };
  const converted = ts.convertCompilerOptionsFromJson(merged, VIRTUAL_ROOT);
  return {
    options: converted.options ?? {},
    errors: converted.errors ?? [],
  };
}

function createInMemoryHost(files, options) {
  const defaultHost = ts.createCompilerHost(options, true);
  const normalizedFiles = new Map();
  for (const [rawName, text] of Object.entries(files || {})) {
    normalizedFiles.set(toAbsolute(rawName), text);
  }
  const virtualDirectories = collectVirtualDirectories(normalizedFiles.keys());

  return {
    ...defaultHost,
    getCurrentDirectory: () => VIRTUAL_ROOT,
    getCanonicalFileName: (fileName) => normalizePath(fileName),
    fileExists: (fileName) => {
      const absolute = toAbsolute(fileName);
      return (
        normalizedFiles.has(absolute) ||
        defaultHost.fileExists(absolute)
      );
    },
    readFile: (fileName) => {
      const absolute = toAbsolute(fileName);
      return (
        normalizedFiles.get(absolute) ??
        defaultHost.readFile(absolute)
      );
    },
    directoryExists: (dirName) => {
      const absolute = toAbsolute(dirName);
      return (
        virtualDirectories.has(absolute) ||
        (defaultHost.directoryExists?.(absolute) ?? false)
      );
    },
    getDirectories: (dirName) => {
      const absolute = toAbsolute(dirName);
      const fromDefault = defaultHost.getDirectories?.(absolute) ?? [];
      const virtual = listVirtualSubdirectories(
        absolute,
        virtualDirectories,
      );
      return Array.from(new Set([...fromDefault, ...virtual]));
    },
    getSourceFile: (
      fileName,
      languageVersion,
      onError,
      shouldCreateNewSourceFile,
    ) => {
      const normalized = toAbsolute(fileName);
      const text = normalizedFiles.get(normalized);
      if (text !== undefined) {
        const scriptKind = ts.getScriptKindFromFileName(normalized);
        const target =
          languageVersion ?? options.target ?? ts.ScriptTarget.Latest;
        return ts.createSourceFile(
          normalized,
          text,
          target,
          true,
          scriptKind,
        );
      }
      return defaultHost.getSourceFile(
        normalized,
        languageVersion,
        onError,
        shouldCreateNewSourceFile,
      );
    },
    writeFile: () => {},
  };
}

function runRequest(request) {
  const { options, errors: optionErrors } = parseOptions(request.options);
  const rootNames = (request.rootNames ?? []).map(toAbsolute);
  const host = createInMemoryHost(request.files ?? {}, options);
  const program = ts.createProgram({ rootNames, options, host });
  const diagnostics = [
    ...optionErrors,
    ...ts.getPreEmitDiagnostics(program),
  ];
  const diagnosticsOnly =
    request.diagnosticsOnly === true || request.diagnostics_only === true;

  let typeFacts = null;
  if (!diagnosticsOnly) {
    const providedMarkers =
      (request.type_queries && request.type_queries.length
        ? request.type_queries
        : request.typeQueries && request.typeQueries.length
          ? request.typeQueries
          : null) ?? null;
    const markers =
      providedMarkers && providedMarkers.length
        ? providedMarkers
        : collectTypeQueries(request.files);
    const checker = program.getTypeChecker();
    typeFacts = collectTypeFacts(program, checker, markers, request.files ?? {});
  }

  const response = {
    schemaVersion: SCHEMA_VERSION,
    metadata: {
      typescriptVersion: ts.version,
      options,
    },
    diagnostics: serializeDiagnostics(diagnostics),
  };
  if (typeFacts) {
    response.type_facts = typeFacts;
  }
  return response;
}

function respond(payload) {
  process.stdout.write(`${JSON.stringify(payload)}\n`);
}

function main() {
  const rl = readline.createInterface({
    input: process.stdin,
    crlfDelay: Infinity,
  });

  rl.on("line", (line) => {
    if (!line.trim()) {
      return;
    }

    let request;
    try {
      request = JSON.parse(line);
    } catch (err) {
      respond({
        diagnostics: [],
        crash: { message: `invalid JSON input: ${err?.message ?? String(err)}` },
      });
      return;
    }

    try {
      const result = runRequest(request);
      respond(result);
    } catch (err) {
      respond({
        diagnostics: [],
        crash: {
          message: err?.message ?? String(err),
          stack: err?.stack,
        },
      });
    }
  });

  rl.on("close", () => process.exit(0));
}

main();
