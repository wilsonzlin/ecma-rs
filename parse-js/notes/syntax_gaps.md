# Parser syntax gap tracker

Updated 2025-02-24 (post import.meta/private index signature/destructuring fixes).

Current parser gaps observed when running the conformance runner without filtering out expected-error tests:

- **Import meta misuse** — 3 virtual files (`importMeta.ts` invalid `import.metal`/`import.import`, and `importMetaPropertyInvalidInCall.ts`) intentionally exercise illegal `import.*` accesses. The parser now accepts `import.meta` expressions/assignments; remaining failures are expected diagnostics.
- **Arbitrary module namespace identifiers negative syntax** — 12 virtual files in `arbitraryModuleNamespaceIdentifiers_syntax.ts` intentionally exercise invalid forms (e.g. missing `as`, string-literal local import bindings, and local exports with string-literal exportables). These remain expected syntax errors.
- **Dynamic import grammar errors** — 4 virtual files covering spreads, missing arguments, or type arguments in `import(...)` remain failures by design.

No additional unsupported valid syntactic constructs are known after fixing `import.meta` expression statements, export assignments without semicolons, index-signature-like members in object/class bodies, qualified `this` in type references, and destructuring parameters in type signatures. If the harness filters out the above negative cases, the filtered subsets for `importMeta`, `exportAsNamespace`, `accessor`, `privateIndexer2`, `privateInstanceMemberAccessibility`, `destructuringParameterDeclaration1ES6`, and `importCallExpression` are clean.
