#!/usr/bin/env node
// Minimal NDJSON TypeScript runner for the Rust harness.
const path = require("path");
const readline = require("readline");
const ts = require("typescript");

const VIRTUAL_ROOT = "/";
const SCHEMA_VERSION = 1;

function normalizePath(fileName) {
  return path.posix.normalize(fileName.replace(/\\/g, "/"));
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

function serializeDiagnostic(diagnostic) {
  const start = diagnostic.start ?? 0;
  const end = (diagnostic.start ?? 0) + (diagnostic.length ?? 0);
  const fileName = diagnostic.file ? toAbsolute(diagnostic.file.fileName) : null;
  const relative = fileName ? path.posix.relative(VIRTUAL_ROOT, fileName) : null;

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
  return {
    schemaVersion: SCHEMA_VERSION,
    metadata: {
      typescriptVersion: ts.version,
      options,
    },
    diagnostics: serializeDiagnostics(diagnostics),
  };
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
