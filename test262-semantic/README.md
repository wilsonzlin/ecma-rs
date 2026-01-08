# test262 semantic harness

This directory hosts the semantic (runtime) test runner for
[`tc39/test262`](https://github.com/tc39/test262).

## Corpus setup

The full `test262` corpus is large, so it is kept as an **optional submodule** at
`test262-semantic/data`.

Fetch it with:

```bash
git -C engines/ecma-rs submodule update --init --recursive test262-semantic/data
```

When running inside the `ecma-rs` repo directly, the equivalent command is:

```bash
git submodule update --init --recursive test262-semantic/data
```

The runner should default `--test262-dir` to `test262-semantic/data` so running
from the repo root requires no extra flags.

