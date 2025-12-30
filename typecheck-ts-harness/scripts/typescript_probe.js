#!/usr/bin/env node
const { loadTypeScript } = require("./typescript_loader");

try {
  const ts = loadTypeScript();
  process.stdout.write(`${ts.version}\n`);
} catch (err) {
  process.stderr.write(`${err?.message ?? String(err)}\n`);
  process.exitCode = 1;
}

