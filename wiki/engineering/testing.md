# Testing infrastructure

The verification estate: what oracles exist, what each harness does, and how to run
them. Philosophy: expected values come from authoritative sources — the TypeScript
compiler, ECMA-262/test262, property invariants — never from what our code currently
returns ([how-to-work § testing policy](../meta/how-to-work.md#testing-policy)).
(Absorbed from `typecheck-ts-harness/README.md`, `test262/README.md`,
`test262-semantic/README.md`, `conformance-harness/README.md`, `megatest/README.md`,
`bench/typecheck-ts/README.md`, 2026-07.)

## The oracle map

| Layer | Oracle | Harness |
| --- | --- | --- |
| Parser | TS corpus `.errors.txt` baselines; test262-parser pass/fail/early | `parse-js` conformance runner; `test262` crate |
| Checker | live `tsc` (pinned 5.9.3) diagnostics + type facts; stored JSON baselines | `typecheck-ts-harness` (`conformance`, `difftsc`, `verify-snapshots`, `triage`) |
| Types core | property invariants (terminate, no panic, idempotent canon) | `fuzz/type_graph`, unit tests |
| Optimizer | deterministic goldens; (future) semantic equivalence via VM | unit tests, megatest corpus |
| VM | test262 proper | `test262-semantic` |
| Everything | determinism (thread-count invariance, sorted outputs) | `typecheck-ts` 1-vs-N rayon snapshot; ordering tests; emit megatest fixpoint ([determinism](../architecture/determinism.md#determinism-as-a-test-target)) |

## Shared harness mechanics (`conformance-harness`)

VM-agnostic utilities reused by runners (no parse-js/VM deps): **expectation
manifests** (TOML/JSON; statuses `pass|skip|xfail|flaky`; matcher precedence exact
`id` > `glob` > `regex`), **deterministic sharding** (`Shard` + `apply_shard`),
**cooperative timeouts** (`TimeoutManager`/`TimeoutGuard` over any cancellation token;
`Arc<AtomicBool>` out of the box), **JSON report helpers** (`ReportRef` with
runner-owned `schema_version`; pretty, stably-ordered output; `FailOn` policy).
Report determinism rules: sort results by id before serializing; `BTreeMap` for any
serialized maps.

**Convergence status (2026-07-24):** **done** for manifest + shard mechanics.
`typecheck-ts-harness` depends on `conformance-harness` and re-exports
`FailOn`/`Shard`/`ShardStrategy`; its `Expectations` type is a thin
`HarnessError`-mapping wrapper over the shared parser. Hash sharding (stable
FNV-1a) lives in `conformance-harness`. Remaining local: conformance/difftsc
report shapes and Node/`tsc` process timeouts (not the cooperative
`TimeoutManager` used by test262 runners).

**Expectation semantics** (shared across runners): `xfail`/`flaky` entries are
*expected to mismatch*; if one passes it reports **XPASS** — treated as failure under
`--fail-on new|all` so stale manifest entries can't linger. `--fail-on` levels:
`new` (default — only uncovered mismatches fail), `all`, `none` (report-only runs).

## TypeScript conformance + difftsc (`typecheck-ts-harness`)

Prereqs: the TS submodule (`parse-js/tests/TypeScript`) for upstream suites; Node +
pinned `typescript` (`cd typecheck-ts-harness && npm ci`;
`node scripts/typescript_probe.js` to verify; `TYPECHECK_TS_HARNESS_TYPESCRIPT_DIR`
overrides the install; `--node` overrides the binary). All fixtures are strict UTF-8
(discovery fails fast otherwise). The Node side is `scripts/tsc_runner.js` — an
NDJSON, in-memory TypeScript runner using `ts.getPreEmitDiagnostics` with `noEmit` +
`skipLibCheck`.

### `conformance` — Rust checker vs upstream suite

```bash
cargo run -p typecheck-ts-harness --release -- conformance \
  --filter "*/es2020/**" --shard 3/16 --shard-strategy hash \
  --timeout-secs 20 --manifest typecheck-ts-harness/fixtures/conformance_manifest.toml \
  --fail-on new --json > report.json
```

Semantics worth knowing: filters are globs or regexes over the path under the root;
`--shard-strategy hash` keeps shard contents stable as upstream adds/removes tests
(use in CI); `--extensions` uses longest-suffix-wins (`d.ts` must be listed separately
from `ts`); per-test timeouts cancel *only* the offending case — Rust side via
`Program::cancel()`, live-tsc side by killing the Node runner process, with no
thread-per-test (inline on rayon workers + bounded deadline threads); `--jobs` caps
parallelism; `--compare auto|tsc|snapshot|none` picks the oracle (auto prefers live
tsc, falls back to snapshots); `--update-snapshots` regenerates
`baselines/<suite>/<id>.json`; `--span-tolerance <bytes>` absorbs small span drift;
`--trace` emits JSONL to stderr keeping stdout parseable; `--profile` forwards to the
checker. Unlike the parser's runner, **multi-file `@filename:` tests are handled**
(`multifile.rs`). A tiny committed corpus lives at `fixtures/conformance-mini`
(suitable for CI without submodules). Missing suite ⇒ fail-fast with setup hint
(`--allow-empty` to opt out).

### `verify-snapshots` — baseline integrity

Checks stored snapshots against the *current* pinned tsc (snapshot-vs-tsc, not
Rust-vs-tsc): exits non-zero on missing snapshots, drift, crashes, or timeouts. Run it
when bumping the TypeScript pin.

### `difftsc` — differential testing

Two modes: baseline stability (tsc vs stored JSON) and true differential (tsc vs Rust
via `--compare-rust`; `--use-baselines` substitutes stored JSON for live tsc — **no
Node needed**, which is what CI-without-Node and `README` quickstart use).
Baselines: `baselines/<suite>/<test>.json` carrying `schemaVersion`, tsc
version/options metadata, diagnostics, and optional **type facts** —
`type_facts.exports` (rendered types of exported value symbols) and
`type_facts.markers` (`^?` markers per the TypeScript baseline convention: a marker on
its own comment line queries the preceding line, otherwise its own line at the marker
column). `--update-baselines` honors `--filter`/`--shard` for parallel regeneration.
Fixture naming: single-file tests are `<name>.ts`, multi-file tests are directories;
names must be unique per suite (baseline filenames derive from them). Adding a test =
drop fixture, regenerate baselines, commit both.

CI live-smoke (nightly): tiny `fixtures/difftsc` suite against installed
`typescript@5.9.3`, `RAYON_NUM_THREADS=2`, single shared tsc runner, JSON artifact.

**Cornerstone litmus ladder** (theory checklist): unit fixtures under
`typecheck-ts/tests/litmus/cornerstone_*` plus difftsc suite
`fixtures/cornerstones/` (tsc baselines in `baselines/cornerstones/`). Coverage
(2026-07-25): all six green vs tsc — const/`satisfies` (TS2322 on property key),
excess props (TS2353 on key), CFA narrowing, distributive conditionals, `keyof`/
mapped, overload selection (TS2769 on arg span) — see
[compiler-theory § cornerstones](../theory/compiler-theory.md#the-typescript-cornerstones).

### `triage` — report summarization

Consumes a `--json` report; emits deterministic summaries: mismatch outcomes
(`extra|missing|span|code`, crashes, timeouts), dominant codes, dominant path
prefixes, uncovered regressions, and *suggested manifest entries* for high-volume
known gaps. `--baseline previous.json` diffs runs (regressions/fixes); `--input -`
reads stdin; human summary on stderr, `--json` machine report on stdout.

Caveat on `top_codes`/`top_prefixes` set-difference math: when comparing report
codes by hand, remember the Rust engine tags upstream-mirrored codes as `TS####`
strings while the tsc engine records bare integers (`2454`). Normalize (strip the
`TS` prefix on the Rust side) before diffing, or every diagnostic looks like a
simultaneous "extra + missing". `TC####`/`PS####`/`ICE####` codes have no tsc
equivalent by design.

## Upstream conformance baseline (shards vs live tsc)

Snapshotted 2026-07-23 against pinned `typescript@5.9.3` (shard strategy `hash`,
per-case timeout 12–20s, `--compare tsc --fail-on none`). Reports live under
`reports/conformance-upstream-shard<N>of64-baseline.json` (and `-after.json` for
the post-fix rerun of the same shards). **Widened 2026-07-25** to the full
hash matrix **0–63/64** (`-after.json` for every shard).

### Current floor (2026-07-25): shards 0–63/64

| Shard (of 64) | Cases | Match | Notes |
| --- | --- | --- | --- |
| 0 | 105 | 41 (39.0%) | after refreshed 2026-07-25 (XPASS hygiene) |
| 1 | 97 | 36 (37.1%) | after refreshed 2026-07-25 (XPASS hygiene) |
| 2 | 99 | 38 (38.4%) | re-included after budget/cancel work; gaps manifested 2026-07-25 |
| 3 | 98 | 36 (36.7%) | after refreshed 2026-07-25 (XPASS hygiene) |
| 4 | 101 | 42 (41.6%) | after refreshed 2026-07-25 (XPASS hygiene) |
| 5 | 78 | 27 (34.6%) | manifest ratchet green (`--fail-on new`) |
| 6 | 103 | 37 (35.9%) | prior `rust_ice` fixed 2026-07-24 late |
| 7 | 95 | 32 (33.7%) | prior `rust_ice` fixed 2026-07-24 late |
| 8 | 98 | 37 (37.8%) | after refreshed 2026-07-25 (XPASS hygiene) |
| 9 | 93 | 28 (30.1%) | prior `rust_ice` fixed 2026-07-24 late |
| 10 | 109 | 40 (36.7%) | after refreshed 2026-07-25 (XPASS hygiene) |
| 11 | 97 | 40 (41.2%) | |
| 12 | 75 | 29 (38.7%) | manifested 2026-07-24 late |
| 13 | 90 | 31 (34.4%) | manifested 2026-07-24 late |
| 14 | 96 | 25 (26.0%) | manifested 2026-07-24 late |
| 15 | 87 | 30 (34.5%) | manifested 2026-07-24 late |
| 16 | 80 | 27 (33.8%) | manifested 2026-07-24 late |
| 17 | 92 | 34 (37.0%) | manifested 2026-07-24 late |
| 18 | 76 | 23 (30.3%) | manifested 2026-07-24 late |
| 19 | 90 | 31 (34.4%) | manifested 2026-07-24 late |
| 20 | 103 | 46 (44.7%) | manifested 2026-07-25 |
| 21 | 91 | 36 (39.6%) | manifested 2026-07-25; +1 `tsc_crashed` xfail |
| 22 | 106 | 41 (38.7%) | manifested 2026-07-25 |
| 23 | 105 | 35 (33.3%) | manifested 2026-07-25 |
| 24 | 90 | 33 (36.7%) | manifested 2026-07-25 |
| 25 | 84 | 37 (44.0%) | manifested 2026-07-25 |
| 26 | 90 | 24 (26.7%) | manifested 2026-07-25 |
| 27 | 75 | 22 (29.3%) | manifested 2026-07-25 |
| 28 | 97 | 33 (34.0%) | manifested 2026-07-25 |
| 29 | 106 | 39 (36.8%) | manifested 2026-07-25; +1 timeout |
| 30 | 92 | 35 (38.0%) | manifested 2026-07-25; +1 timeout |
| 31 | 86 | 35 (40.7%) | manifested 2026-07-25 |
| 32 | 101 | 29 (28.7%) | manifested 2026-07-25 |
| 33 | 96 | 33 (34.4%) | manifested 2026-07-25; +1 timeout |
| 34 | 78 | 27 (34.6%) | manifested 2026-07-25 |
| 35 | 78 | 26 (33.3%) | manifested 2026-07-25 |
| 36 | 89 | 28 (31.5%) | manifested 2026-07-25 |
| 37 | 83 | 25 (30.1%) | manifested 2026-07-25 |
| 38 | 85 | 24 (28.2%) | manifested 2026-07-25 |
| 39 | 82 | 29 (35.4%) | manifested 2026-07-25 |
| 40 | 89 | 29 (32.6%) | manifested 2026-07-25; +1 timeout |
| 41 | 96 | 39 (40.6%) | manifested 2026-07-25 |
| 42 | 103 | 37 (35.9%) | manifested 2026-07-25 |
| 43 | 87 | 25 (28.7%) | manifested 2026-07-25 |
| 44 | 76 | 31 (40.8%) | manifested 2026-07-25 |
| 45 | 91 | 32 (35.2%) | manifested 2026-07-25 |
| 46 | 103 | 39 (37.9%) | manifested 2026-07-25 |
| 47 | 84 | 31 (36.9%) | manifested 2026-07-25 |
| 48 | 95 | 32 (33.7%) | manifested 2026-07-25; +1 `tsc_crashed` |
| 49 | 87 | 29 (33.3%) | manifested 2026-07-25 |
| 50 | 95 | 34 (35.8%) | manifested 2026-07-25; +2 timeout |
| 51 | 88 | 32 (36.4%) | manifested 2026-07-25 |
| 52 | 84 | 39 (46.4%) | manifested 2026-07-25 |
| 53 | 112 | 28 (25.0%) | manifested 2026-07-25 |
| 54 | 95 | 32 (33.7%) | manifested 2026-07-25 |
| 55 | 104 | 38 (36.5%) | manifested 2026-07-25 |
| 56 | 78 | 26 (33.3%) | manifested 2026-07-25; completes /64 |
| 57 | 110 | 30 (27.3%) | manifested 2026-07-25; completes /64 |
| 58 | 98 | 23 (23.5%) | manifested 2026-07-25; completes /64 |
| 59 | 96 | 40 (41.7%) | manifested 2026-07-25; completes /64 |
| 60 | 96 | 30 (31.2%) | manifested 2026-07-25; completes /64 |
| 61 | 85 | 26 (30.6%) | manifested 2026-07-25; completes /64 |
| 62 | 82 | 21 (25.6%) | manifested 2026-07-25; completes /64 |
| 63 | 88 | 25 (28.4%) | manifested 2026-07-25; completes /64 |
| **aggregate (0–63)** | **5898** | **2049 (34.74%)** | |

Former stack-overflow aborts (process death; cooperative timeout could not
recover) were bisected to unguarded recursion in
`lookup_interned_property_type` when `expand_ref` returned an in-progress `Ref`.
**Fixed 2026-07-24 late** (cycle/`seen` guard + no-progress stop). Cases that
used to abort:

- shard 6: `classes/members/privateNames/privateNamesInGenericClasses.ts`
- shard 7: `interfaces/declarationMerging/mergedInterfacesWithInheritedPrivates.ts`
- shard 9: `interfaces/declarationMerging/mergedInterfacesWithInheritedPrivates2.ts`

Manifest (`typecheck-ts-harness/fixtures/conformance_manifest.toml`) ratchets
shards **0–63** (mismatches `xfail`; ICE `skip`s removed; shard 2 gaps + XPASS
hygiene applied 2026-07-25; shards 48–51 +238 `xfail`; shards 52–55 +258
`xfail`; shards 56–63 +512 `xfail`). Nightly `ts-conformance-ratchet` matrix is
`0..63` of 64 (full /64 matrix).

### Historical 4-shard sample (2026-07-23; shards 0/1/3/4)

| Shard (of 64) | Cases | Match (before) | Match (after) |
| --- | --- | --- | --- |
| 0 | 105 | 36 (34.3%) | 39 (37.1%) |
| 1 | 97 | 26 (26.8%) | 32 (33.0%) |
| 3 | 98 | 33 (33.7%) | 33 (33.7%) |
| 4 | 101 | 38 (37.6%) | 38 (37.6%) |
| **aggregate (0,1,3,4)** | **401** | **133 (33.2%)** | **142 (35.4%)** |

The two fixes below moved that aggregate **+9 matches (33.2% → 35.4%) with zero
regressions** (verified by a per-case before/after diff): `nullishCoalescingOperator6`
flipped `rust_extra → match` (parameter-default fix), and 8 jsdoc/salsa cases
flipped `rust_missing → match` once the allowJs baseline became honest.

Shard 2/64 was briefly **excluded** for a pathology that drove multi-GB RSS;
budgets/`TC4000` landed and it was **re-included 2026-07-24** (see
`reports/shard2-pathology-handoff.md`).

Dominant mismatch drivers in the before-baseline (data-driven, not guessed):
- `rust_missing` **TS6504** (30/401) was a *harness-fidelity artifact*, not a
  checker gap: the harness dropped `@allowJs`/`@checkJs`, so tsc refused to check
  `.js` fixtures and emitted "did you mean to enable allowJs" instead of the
  fixtures' real errors. Fixed in `directives.rs` (now forwarded to tsc); those
  cases now surface genuine checkJs/JSDoc gaps. Since then, `@type` / `@param` /
  `@returns` / `@typedef` / `@template` (+ `@property` shapes), Closure
  `new:` / `@constructor`, nested `@param opts.x` sugar (+ TS8032), class
  `@template` construct call-site instantiation, and unmatched root `@param`
  (TS8024) landed under checkJs (XPASS `paramTagNestedWithoutTopLevelObject*`,
  `jsdocTemplateClass`, `jsdocParamTagTypeLiteral`,
  `checkJsdocParamOnVariableDeclaredFunctionExpression`); residual gaps are
  deeper `@template` (typedef/variance/defaults/`@constructor`), TS8024 mixed
  with other codes, and richer CJS typedef graphs (see
  [typecheck-ts](../crates/typecheck-ts.md)).
- `rust_extra` **TC3000** (implicit-any false positives): parameters with a
  default-value initializer were flagged as implicitly `any`. Fixed (see
  [typecheck-ts](../crates/typecheck-ts.md#known-issues-and-directions)).
- `rust_extra` **TC0005** (unknown-identifier false positives): dominated by
  CommonJS globals (`require`/`module`/`exports`) in `.js`/JSDoc fixtures and
  `globalThis`; plus genuinely-declared names the checker fails to resolve.
- `PS0002`/`PS0013` (parser) `rust_extra` and several `rust_missing` cases trace
  into `parse-js` (error recovery) — out of scope for the checker program.

### Ratchet commands (upstream suite)

Capture / refresh a shard baseline (report-only, never fails):

```bash
cargo run -p typecheck-ts-harness --release -- conformance \
  --shard 3/64 --shard-strategy hash --timeout-secs 12 \
  --compare tsc --fail-on none --jobs 2 --json \
  > reports/conformance-upstream-shard3of64-baseline.json
```

Aggregate/triage a captured report (dominant outcomes, codes, prefixes, and
suggested manifest entries):

```bash
cargo run -p typecheck-ts-harness --release -- triage \
  --input reports/conformance-upstream-shard3of64-baseline.json --json --top 20
```

Run a shard **against the committed expectations manifest** so known gaps are
green and only *new* regressions fail (this is the CI-shaped invocation):

```bash
cargo run -p typecheck-ts-harness --release -- conformance \
  --shard 3/64 --shard-strategy hash --timeout-secs 12 --compare tsc \
  --manifest typecheck-ts-harness/fixtures/conformance_manifest.toml \
  --fail-on new
```

The manifest (`typecheck-ts-harness/fixtures/conformance_manifest.toml`) lists the
captured known-gap cases as `xfail`; when a gap is fixed the run reports **XPASS**
(a failure under `--fail-on new`), forcing the stale entry to be pruned. Regenerate
it from triage suggestions after broadening the captured shards.

### Guard invariants (rerun after every landing)

```bash
# difftsc curated suite (Node-free): must stay 56/56
cargo run -p typecheck-ts-harness --release -- difftsc \
  --suite typecheck-ts-harness/fixtures/difftsc --compare-rust --use-baselines

# conformance-mini (needs Node): 5 match + 1 expected mismatch, green under fail-on new
cargo run -p typecheck-ts-harness --release -- conformance \
  --root typecheck-ts-harness/fixtures/conformance-mini \
  --manifest typecheck-ts-harness/fixtures/conformance-mini/manifest.toml \
  --compare tsc --fail-on new --timeout-secs 20
```

## test262 parser harness (`test262`)

Drives `tc39/test262-parser-tests` (submodule `test262/data`) against `parse-js`:
`pass/`, `pass-explicit/` must parse; `fail/` must not; `early/` must trigger early
errors. Module-vs-script inferred from `.module.` in filenames. Deterministic JSON
report (schema v2: summary, ordered per-test results, diagnostic code + byte span per
failure); only unexpected mismatches print to stderr. The shipped manifest
(`test262/manifest.toml`) carries precise per-cluster xfails — template/string
literal pass-corpus gaps, early-error clusters each annotated with its ECMA-262
section and owning layer (parser vs binder), and a small fail-corpus set
(including RegExp `u`-flag grammar) — with unexpected mismatches at 0. Prune
entries as the clusters close.

```bash
cargo run -p test262 --release -- --data-dir test262/data \
  --manifest test262/manifest.toml --report-path reports/test262-parser.json --fail-on new
```

## test262-semantic runner (`test262-semantic`)

Language-semantics runner over curated subsets of full test262 (submodule
`test262-semantic/data`; also runnable from the FastRender embedding via
`engines/ecma-rs` paths). Default executor is `vm-js`-backed; `--features
stub_executor` swaps in an always-pass executor for wiring/CI experiments. Mechanics:
deterministic discovery/sharding; suites as TOML/JSON id/include/exclude selections
(built-in `suites/smoke.toml`; unknown explicit ids error); expectation manifests
(shared format); per-test timeouts; versioned JSON reports (`--json`,
`--report-path`). Spec fidelity in the harness itself: test IDs are forward-slash
paths under `test/`; script tests expand to `non_strict` + `strict` variants unless
`onlyStrict`/`noStrict`; `module` flag runs as a single module case; harness modes
`--harness test262` (implicit `assert.js`+`sta.js` then `includes`), `includes`, or
`none` (early bring-up); strict variants keep `'use strict';` *ahead of* prepended
harness code so the directive prologue survives.

## Megatest stress programs

`megatest/*.js` — self-contained programs stress-testing parsing, compilation, static
analysis, type analysis, optimization opportunities, execution correctness, and
runtime performance (vdom, reactive pipeline, task scheduler, arena GC, scientific
computing, stream processing, static analysis, business logic, deliberately-weird
code, optimizable patterns). Use them as cross-cutting corpora: emit round-trips,
optimizer equivalence (once VM-executable), checker stress.

**Emit fixpoint guard** (as of 2026-07-24): `cargo test -p emit-js --test megatest_fixpoint`
asserts parse→emit→parse→emit text identity (AST always; HIR where supported). Skip
tables and reasons live in the test + [emit-js](../crates/emit-js.md#verification).

**1-vs-N checker determinism** (as of 2026-07-24):

```bash
cargo test -p typecheck-ts --test determinism \
  check_outputs_identical_under_1_vs_n_rayon_threads
```

Installs dedicated 1- and 4-thread rayon pools and diffs full program snapshots
(diagnostics, exports, `TypeId`s, body side tables). Both guards have named steps in
`.github/workflows/ci.yaml` (also covered by `cargo test --workspace`).

## Fuzzing

`fuzz/` (excluded from the workspace; `cargo-fuzz`): target `type_graph` feeds
arbitrary bytes → JSON → possibly-cyclic `TypeKind` graphs → intern → evaluate/relate
with limits. **Invariant: terminate, never panic.** The workspace config sets
`RUSTC_BOOTSTRAP=1` so the pinned stable toolchain suffices
(`cargo fuzz run type_graph`). Crate-level `fuzzing`-feature entrypoints exist in
`parse-js`→`hir-js` (`fuzz_lower`), `semantic-js` (`fuzz.rs`), `minify-js`
(`fuzz_minify_pipeline`), `typecheck-ts` (`fuzz.rs`) — wire more targets as passes are
added ([roadmap](../status/roadmap.md#3-correctness-program)).

## Benchmarks

- **`bench/typecheck-ts`** (`cargo bench -p typecheck-ts-bench`): deterministic
  fixtures for parse/lower micro-benches, pipeline (parse+lower+bind), end-to-end
  typechecking with stage timings and relation-cache stats, `type_of_def` export
  surfaces, cold-vs-warm `check_body`, relation micro-benches with hit rates, and
  allocation counters (`body_alloc`, `check_body_alloc`; versioned JSON schema with
  name-sorted results). The **incremental scenario** (`incremental/full` vs
  `incremental/edit` — live `Program` + `set_file_text` on a body-only edit in
  `project_text.ts`, scored by `body_check_count`) is the regression guard for
  invalidation quality. JSON mode: `TYPECHECK_TS_BENCH_JSON=1` (stdout
  reserved for JSON); scale runtime with `TYPECHECK_TS_BENCH_ITERS_SCALE`; fixture
  filter `TYPECHECK_TS_BENCH_ALLOC_FIXTURES`; skip alloc benches with
  `TYPECHECK_TS_BENCH_ALLOC_SKIP=1`. Nightly CI uploads the three JSON artifacts.
- **`bench/minify-js`**: the esbuild-comparative corpus behind the README charts
  (diagnostic prefix `MINIFY####`); `bench/run`/`build`/`graph` orchestrate.
- **`parse-js/benches/baseline_performance.rs`**: criterion parser baseline.

## Unit/integration suites

`cargo test --workspace` covers crate unit tests plus `typecheck-ts`'s 129 integration
files (narrowing, generics, classes, modules, decl merging, db memoization,
cancellation, litmus dirs …).

**Feature-gated tests and cargo feature unification (lesson, 2026-07-23)**:
`cargo test -p <crate>` builds with *default features*, so `#[cfg(feature = …)]`
tests silently don't compile — but a combined/workspace invocation unifies features
across the dependency graph (e.g. `parse-js-cli` enables `parse-js/serde`) and
suddenly compiles them. Several stale serde-gated parse-js snapshot tests escaped
five workers' green `-p parse-js` runs exactly this way and only surfaced in a
multi-crate run. Rule: when you touch a crate, verify it with `--all-features` too
(or at least the features its workspace dependents enable).

**parse-js data-driven fixture modes**: fixtures under `parse-js/src/parse/tests/`
parse as TS *modules* by default; fixtures named `*.script.*` parse as sloppy
*scripts* (contextual keywords `await`/`let`/`yield` as identifiers). One parse
context cannot serve both — a spec-correct parser treats `await` as an operator in
module code and an identifier in sloppy scripts — so the mode is filename-inferred,
mirroring the test262 runner's `.module.` convention. The
[NameInterner deadlock](../architecture/determinism.md#case-study-the-nameinterner-deadlock)
is fixed (2026-07-23); keep `RAYON_NUM_THREADS=1` as a diagnostic knob when hunting
schedule bugs, and rely on the 1-vs-N snapshot test above as the standing guard.
