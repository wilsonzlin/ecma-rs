# Shard 2 pathology fix handoff (2026-07-23)

## Case

- **Upstream:** `parser/ecmascript5/parserRealSource12.ts` (shard 2/64, hash strategy)
- **Shape:** large AST-walker source (~108 `childrenWalkers[…] = …` assigns, many
  walker functions) with a missing `typescript.ts` reference → unresolved names
- **Minimized:** `typecheck-ts/tests/engine_budget.rs` (`pathological_source`)

## Root mechanism

Not a single infinite relate loop. Hot stack was:

`TypeEvaluator::evaluate_object` → nested signature/`Ref` expansion →
`TypeStore::intern_shape` / `intersection` / (formerly structural)
`sort_and_dedup` via `type_cmp`, allocating into a **shared** `TypeStore`.

Per-`RelateCtx` / per-`evaluate()` step budgets reset often enough that work
stayed under `step_limit` while RSS grew across many bodies. Cancellation was
not observed inside relate/eval hot paths (`DEFAULT_STEP_LIMIT` was
`usize::MAX`).

## Three-layer fix

### a) Cancellation in hot loops (`types-ts-interned` + wire-up)

- `RelateHooks::should_stop: Option<&AtomicBool>` — on stop: conservative
  success, latch `budget_exceeded`, never panic in the pure crate
- `TypeEvaluator::with_should_stop` — same contract
- `normalize_type` shares remaining relation step budget with nested evaluators
- `typecheck-ts` sets `should_stop` from the salsa cancel token at body-check /
  flow / merging relate construction sites
- Flow CFA worklist + per-`eval_expr` observe cancel → `FatalError::Cancelled`

### b) Finite default budgets

| Knob | Default | Notes |
| --- | --- | --- |
| `RelationLimits::DEFAULT_STEP_LIMIT` | **50_000** | was `usize::MAX` (off) |
| `EvaluatorLimits::DEFAULT_STEP_LIMIT` | **50_000** | aligned with relation |
| `InstantiationLimits::DEFAULT_MAX_STEPS` | **50_000** | depth 128 |
| Checker `DEFAULT_EXPR_STEP_LIMIT` | 100_000 | per body |
| Flow `DEFAULT_FLOW_STEP_LIMIT` | 25_000 | worklist + expr visits |
| Per-body `DEFAULT_MAX_TYPE_GROWTH` | **5_000** | shared `TypeStore` growth |
| `MAX_COMPOSITE_MEMBERS` | 4_096 | union → unknown / ∩ → never |

Exceeding budgets in the checker → `TC4000` (`ENGINE_BUDGET_EXCEEDED`).
Cancel → `CANCEL0001`.

Calibration: shards **0/1/3/4** match-counts **unchanged** vs
`reports/conformance-upstream-shard{N}of64-after.json`; difftsc **56/56**;
conformance-mini **5 match + 1 expected**.

### c) Pathology-specific guards

- `sort_and_dedup` sorts by content-addressed `TypeId` (not structural `type_cmp`)
- Empty / type-param-only subst: do not deep-walk nested **object property**
  graphs in `evaluate_object` (still reduce call/construct signatures +
  `Callable`/`Ref` props) — stops `evaluate_ref(Promise<T>)`-style re-entry
- Identity short-circuit when `!type_needs_evaluation` under empty subst
  (`TypeParam` alone is not “needs eval”)
- Do not cache evaluator results after `budget_exceeded`

## Shard 2 after fix

- Command: `conformance --shard 2/64 --shard-strategy hash --timeout-secs 20 --compare none`
- **~22s wall**, peak RSS **~516 MB**, **0 timeouts**, 99 cases completed
- Report: `reports/shard2-after-budget-fix.json`

## Tests

- `typecheck-ts/tests/engine_budget.rs` — minimized + real case terminate; cancel → `CANCEL0001`
- `types-ts-interned/tests/relate.rs` — step limit + `should_stop`
