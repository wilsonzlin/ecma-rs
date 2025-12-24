## parse-js

`parse-js` provides the parser that powers the rest of this workspace. The TypeScript conformance harness depends on the official TypeScript repository as a git submodule.

To run the conformance suite locally you must first initialize the submodule:

```bash
git submodule update --init --recursive --depth=1 parse-js/tests/TypeScript
```

If the `tests/TypeScript` directory is missing or empty, the conformance runner will exit with a helpful error explaining how to populate it.
