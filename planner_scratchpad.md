# Planner scratchpad (conditional types / normalization)

This file is checked into the repository so future planning doesn't trip over
already-completed work. (Agent-local `scratchpad.md` files are ignored by git in
this swarm environment.)

## Current state

- Conditional evaluation uses structural assignability safely via `RelateCtx` in
  `RelationMode::SKIP_NORMALIZE`.
- Normalization uses `TypeEvaluator` caches (`EvaluatorCaches`) and can delegate
  conditional assignability via `TypeEvaluator::with_conditional_assignability`
  (defaulting to a `RelateCtx`).

## Open tasks

- (none)

## Completed

- [x] Task 40 — `RelationMode::SKIP_NORMALIZE`
- [x] Task 45 — Evaluator conditional-assignability integration
- [x] Task 49 — Options consistency invariant
- [x] Task 55 — Indeterminate conditional deferral
- [x] Task 64 — `any`/`never` conditional special cases
- [x] Task 71 — Distributive `extends` per-member evaluation
- [x] Task 79 — Scope-aware free type param detection
- [x] Task 85 — Structural conditional tests
