# Parser syntax gap tracker

Updated 2025-02-24 (post import.meta/private index signature/destructuring fixes).

Current parser gaps observed when running the conformance runner without filtering out expected-error tests:

- **Import meta misuse** — 3 virtual files (`importMeta.ts` invalid `import.metal`/`import.import`, and `importMetaPropertyInvalidInCall.ts`) intentionally exercise illegal `import.*` accesses. The parser now accepts `import.meta` expressions/assignments; remaining failures are expected diagnostics.
- **Arbitrary module namespace identifiers without `as`** — 5 virtual files in `arbitraryModuleNamespaceIdentifiers_syntax.ts` that omit `as` or misuse `type` still report syntax errors, matching the negative tests.
- **Dynamic import grammar errors** — 4 virtual files covering spreads, missing arguments, or type arguments in `import(...)` remain failures by design.

No additional unsupported valid syntactic constructs are known after fixing `import.meta` expression statements, export assignments without semicolons, index-signature-like members in object/class bodies, qualified `this` in type references, and destructuring parameters in type signatures. If the harness filters out the above negative cases, the filtered subsets for `importMeta`, `exportAsNamespace`, `accessor`, `privateIndexer2`, `privateInstanceMemberAccessibility`, `destructuringParameterDeclaration1ES6`, and `importCallExpression` are clean.
