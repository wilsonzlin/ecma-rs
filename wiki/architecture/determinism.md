# Determinism doctrine

Determinism — same inputs, same outputs, bit-for-bit, regardless of thread scheduling
or insertion order — is this workspace's signature constraint
([vision bet #1](../vision.md#the-hypotheses-falsifiable-bets)). This page owns the
mechanisms, the rules, and the one hard-won concurrency case study.

## Why determinism is load-bearing

- **Caching**: content-addressed outputs can be reused across runs, machines, and CI
  shards without trust issues.
- **Parallelism**: if outputs are order-independent, thread count is a pure performance
  knob — results never need "blessing" per configuration.
- **Differential testing**: diffing against `tsc` or against yesterday's run only works
  if our own noise floor is zero.
- **Debuggability**: any failure reproduces exactly; there are no heisenbugs from map
  iteration order by construction.

## Mechanisms by layer

Every layer has its own determinism device; they compose:

- **`hir-js`** — `DefId`/`BodyId` are FNV-1a hashes of `DefPath`/`BodyPath` (module,
  parent, kind, name, disambiguator), truncated to 32 bits with **deterministic
  salt-on-collision**: descriptors are sorted before allocation, so collision handling
  itself is order-stable. The per-file 32-bit ID is packed with the owning `FileId` in
  the upper 32 bits, making cross-file collisions impossible
  (`hir-js/src/ids.rs`). Names are content-addressed too (`NameInterner`).
- **`semantic-js`** — JS-mode `ScopeId`/`SymbolId`/`NameId` are stable hashes of file
  id, scope ancestry, declaration kind, and spans; scope symbol tables are
  `BTreeMap<NameId, SymbolId>`; TS-mode export/global maps are `BTreeMap`; declaration
  lists sort by deterministic `order` fields. Caveat recorded in its README: stability
  is relative to caller-controlled inputs (file ids, spans, resolver answers).
- **`types-ts-interned`** — 128-bit **domain-separated fingerprints** (two seeded
  ahash-64 passes, domains like `TYPE_DOMAIN`/`SHAPE_DOMAIN`/`NAME_DOMAIN`) identify
  interned values, so `TypeId` allocation is independent of insertion order
  (`types-ts-interned/src/store.rs`). Composite types are canonicalized before
  interning (flatten, sort by `type_cmp`, dedup) so `A | B` and `B | A` intern to the
  same ID.
- **`diagnostics`** — canonical sort orders (`diagnostic_cmp`, `label_cmp`) applied at
  every public boundary; reports and JSON outputs sort by test id / name.
- **Checker parallelism** — parallel body checking must reduce with fixed, associative
  merges (sorted `BodyId` order), never first-come accumulation.

## Collision semantics (the fine print)

Truncated hashes can collide, so every interner has a salt-rehash fallback. The
subtlety, documented in `types-ts-interned/src/lib.rs`: salt fallback is deterministic
for a *fixed insertion sequence*, but it does **not** define an order-independent
assignment under collisions — the first value inserted keeps the lowest-salt ID,
because already-returned IDs must never change. With 128-bit fingerprints, collisions
are astronomically unlikely; consumers that need strict schedule-independence even
under collisions enable the `strict-determinism` feature, which panics on collision
instead of salting (surfacing the event rather than silently becoming
insertion-order-dependent). `hir-js` sidesteps the issue by sorting descriptors before
allocating — its collision handling is deterministic because its insertion sequence is.

Rule of thumb when adding an interner: content-address with a wide fingerprint;
domain-separate the hash; make the insertion sequence deterministic *or* treat
collision as an error.

## The determinism rules

1. Public maps are ordered (`BTreeMap`/sorted `Vec`); `HashMap` is allowed only for
   internal caches whose iteration order never reaches an output.
2. No output-visible ID may come from a shared counter/atomic incremented under
   parallelism. Content-address it or allocate it in a deterministic serial phase.
3. Sort at the boundary: diagnostics, exports, report entries, JSON keys.
4. Parallel reductions must be associative with a fixed combination order.
5. `RAYON_NUM_THREADS=1` and `=N` must produce byte-identical outputs; treat any
   difference as a correctness bug. (This doubles as the diagnostic knob when hunting
   concurrency bugs — see the case study.)

## Lock discipline

The workspace goal is *lock-minimal*, not lock-free-at-any-cost: immutable `Arc`
snapshots for anything published, sharded caches (`DashMap`, seeded shards) for
concurrent memoization, and `RwLock` only around genuinely small, hot, append-mostly
state (e.g. interner tables). The rules that keep `RwLock` safe:

1. **Never hold a guard across a call that can re-enter the same lock.** parking_lot's
   fair `RwLock` blocks a *re-entrant read* whenever a writer is queued between the two
   read acquisitions: reader waits on writer, writer waits on the reader's outstanding
   guard — deadlock with no cycle visible in the code, only in the schedule.
2. Copy out or snapshot, then compute: take the guard, extract the small fact (a name,
   an ID), drop the guard, recurse.
3. If re-entrant reads are structurally unavoidable, `read_recursive()` exists — but
   treat it as a marked exception with a comment, because it forfeits writer fairness.
4. Recursion + locks is the red-flag combination; any recursive algorithm that touches
   a locked structure needs its lock behavior stated in a comment.

### Case study: the NameInterner deadlock

Found 2026-07-23 by attaching GDB to a hung `typecheck-ts` test (`debug_narrowing`, 66
threads futex-parked, ~7s CPU over 20 minutes). Two stacks told the story:

- Thread A (writer): `FlowBodyChecker::eval_expr_inner` →
  `TypeStore::intern_name` → `names.write()` — parked in `wait_for_readers`.
- Thread B (reader): `TypeLowerer::lower_type_expr` → `TypeStore::union` →
  `sort_and_dedup` → `type_cmp` → `names.read()` — parked *behind the queued writer*.

Root cause in `types-ts-interned/src/store.rs`: `compare_props` takes
`self.names.read()` to compare property keys, then — **while still holding the
guard** — recurses into `type_cmp` on the property types; if the nested comparison
reaches a `StringLiteral` case it calls `self.names.read()` again on the same lock.
Under a serial run or a quiet pool the nested read succeeds (shared locks stack); the
moment another thread's `intern_name` write request lands between the two reads,
parking_lot's fairness turns the nested read into a deadlock. Verified: the identical
test passes in ~8s with `RAYON_NUM_THREADS=1`.

Fix directions (roadmap "restore green"): drop the guard before recursing in
`compare_props` (copy the key comparison out), or key-compare via interned IDs without
holding the name table, or — least preferred — `read_recursive`. The durable lesson is
rule 1 above; the bug survived a well-tested codebase because single-threaded tests
cannot see it and the parallel window is timing-dependent.

### Resolution (2026-07-23)

Fixed by dropping the `names` read guard before the recursive `type_cmp` in
`compare_props` (scoped key-order computation). Other `names` sites in `store.rs`
were audited: `intern_shape` already scoped its sort; leaf sites (`name`,
`compare_prop_keys`, `StringLiteral` in `type_cmp`) do not recurse while holding the
guard. Prefer guard-dropping over `read_recursive`. Stress regression:
`types-ts-interned/tests/lock_stress.rs` (multi-thread intern + union/object
canonicalization under a wall-clock deadline).

Meta-lesson for verification: this was caught by *running the suite on a loaded
machine* and then *observing the process* (ps/wchan/GDB) instead of re-reading code.
Concurrency claims need runtime evidence; see
[how-to-work § Instrumentation](../meta/how-to-work.md#instrumentation).

## Determinism as a test target

What exists:

- Deterministic-ordering unit tests in `diagnostics` and `semantic-js`; snapshot/JSON
  outputs designed order-stable; benches emitting sorted results.
- **`typecheck-ts/tests/determinism.rs`** — schedule-independence over a multi-file
  fixture (root-order + parallel `check_body`), plus an explicit **1-vs-N rayon
  pool** guard (`check_outputs_identical_under_1_vs_n_rayon_threads`): fresh
  `Program`s snapshotted under dedicated 1-thread and 4-thread pools must agree on
  diagnostics, exports, `TypeId`s, and body side tables. Named CI step in
  `.github/workflows/ci.yaml`.
- **`emit-js/tests/megatest_fixpoint.rs`** — parse→emit→parse→emit **text fixpoint**
  over `megatest/*.js` (AST minified + canonical; HIR where emit is supported).
  Intentional non-participants are skip-listed with reasons (see
  [emit-js](../crates/emit-js.md#verification)).

Still wanted (roadmap): broaden the 1-vs-N snapshot to a larger corpus / harness
JSON byte-diff; (long-term) seed under `strict-determinism` in CI to keep the
collision story honest.
