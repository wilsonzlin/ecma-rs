# vm-js (+ runtime-js, webidl, webidl-vm-js)

The ECMAScript virtual machine stack — the foundation for browser-grade JS execution,
built to be embedded (notably by **FastRender**, which vendors this repo as
`engines/ecma-rs`). Spec-shaped first, fast later
([vision bet #5](../vision.md#the-hypotheses-falsifiable-bets)); theory background:
[compiler-theory § VM](../theory/compiler-theory.md#7-the-vm-spec-shaped-semantics-precise-gc).

**Status note (2026-07-23)**: `vm-js` lib + integration tests are **fully green**
(including the previously failing `new.target`-in-arrow cases). The interpreter core
has the full numeric/bitwise/relational operator surface (incl. **BigInt bitwise/shift**
`& | ^ << >>`), **optional-chain short-circuit propagation** (§13.3.9), **primitive
autoboxing** (`GetV` on primitive bases, §7.3.2/§13.3.3), **retained function ASTs** (no
call-time re-parse), and a growing built-in global surface (`Math`, `parseInt`/
`parseFloat`/`isFinite`, `Number` statics, `Object` introspection) — see
[test262 status](#test262-status) and [Execution engine](#execution-engine). Expect
API drift at the edges while host/promise refactors settle.

## Heap and GC

Non-moving mark/sweep with precise rooting (`heap.rs`, `handle.rs`):

- **Handles** (`GcObject`, `GcString`, `GcSymbol`) are `{index, generation}` pairs:
  slots are index-addressed (stable across `Vec` growth), generations increment on
  slot free, so stale handles are *detectable* — public APIs validate and return
  `VmError::InvalidHandle` rather than UB. During GC, a stale handle in a root set is
  a bug (`debug_assert!` + ignore).
- **A handle is not a root.** The GC traces only **stack roots** (RAII `Scope` +
  `push_root`; dropping the scope pops its roots) and **persistent roots**
  (`Heap::add_root`/`remove_root`, for embedder globals like intrinsics or `Window`).
  Storing a `GcObject` in Rust-side structures does not keep it alive — deliberately,
  because that is what makes weak caches expressible (`WeakGcObject::upgrade`).
- `HeapLimits` (size/GC-threshold) bound the heap; any allocation may trigger
  collection, hence the rooting rules below.
- **Throw→catch rooting (2026-07-23)**: `Completion::Throw(Thrown { value, … })`
  carries a bare `Value` (plus stack frames), not a GC root. `eval_catch` /
  `enter_catch_env_pub` must `push_root(thrown)` *before* `env_create` — creating
  the catch environment can allocate and collect the exception object, which
  previously surfaced as `InvalidHandle` / a debug assert under tight
  `HeapLimits` (repro: `exec_stmt::thrown_object_survives_gc_during_catch_env_creation`).
  The `finally` path already rooted pending completion values; catch now matches.

## Execution engine

- **Spec-shaped interpreter**: `exec.rs` (completion records — `Completion::Normal/
  Throw(Thrown)/…`), `spec_ops.rs`/`ops.rs`/`object_ops.rs` (abstract operations),
  `env.rs` (environment records — explicitly *not* JS objects, per spec),
  `execution_context.rs`, `realm.rs` + `intrinsics.rs` (realms, well-known
  intrinsics), `function.rs`/`function_properties.rs` (ECMAScript + native + bound
  functions), `destructure.rs`, `iterator.rs`, `string.rs`/`symbol.rs`/`value.rs`/
  `property.rs` (values, property keys, descriptors), `error_object.rs` (JS error
  construction; VM errors that correspond to JS semantics must become *catchable*
  JS exceptions — a repeated theme in recent fixes).
- **Jobs and promises**: `job_queue.rs`, `jobs.rs`, `microtasks.rs`, `promise*.rs`
  (abstract ops, reaction jobs, unhandled-rejection tracking) — the spec's job model,
  needed for module evaluation and host integration.
- **Modules**: `module_record.rs`, `module_request.rs`, `module_graph.rs`,
  `module_loading.rs` (+ deprecated `module_graph_loader.rs` shim —
  [graveyard](../graveyard.md#module_graph_loader-shim-vm-js)); import attributes are
  parsed/validated per the latest commit.
- **Binding**: the `test262-semantic` executor runs `semantic-js`'s
  `bind_js_for_runtime` (TDZ diagnostics suppressed; TDZ is enforced at runtime)
  with `TopLevelMode::Script` **before** `exec_script_source`, so parse-phase
  early errors (`$DONOTEVALUATE` negatives) surface as `SyntaxError`. The VM
  itself still does its own lightweight instantiation-time checks; wiring bind
  into `JsRuntime` directly remains a follow-up.
- **Retained function ASTs (no call-time re-parse)**: at closure creation,
  `register_ecma_function` captures an `Arc<ParsedProgram>` (the script/`eval` tree)
  plus a `NonNull<Node<Func>>` into that tree. Call/construct push that program onto
  a VM program stack and execute the retained node directly. This preserves
  function-code context that a top-level snippet re-parse cannot (`new.target` /
  `super` legality, strictness, `ParenthesizedExpr` markers) and removes per-call
  parse work. `Loc` values stay absolute in the original `SourceText`
  (`base_offset`/`prefix_len` are 0 for retained bodies). The VM does not currently
  attach per-program binder state to these nodes, so sharing the original tree across
  calls is safe; if binder attachments become program-local later, re-bind at
  registration (still once) rather than resurrecting call-time re-parse.
- **Cooperative scheduling** (`vm.rs`, `interrupt.rs`): `VmOptions.interrupt_flag`
  (shared `AtomicBool`), per-task `Budget { fuel, deadline, check_time_every }` via
  `set_budget`/`push_budget` (RAII) — enforced only where evaluators call
  `Vm::tick()`; the provided `JsRuntime` ticks per statement and per loop iteration,
  and custom evaluators must match that or budgets silently don't apply.
  Termination surfaces as `VmError::Termination(TerminationReason::OutOfFuel/…)`.

### Resumable bodies: generators and async functions (architecture decision)

**Chosen model (2026-07-23): dual-path step-interpreter for suspendable bodies only**
(`resumable.rs` + `generator.rs`). Normal functions keep the fast recursive
`Evaluator` path unchanged. Generator/async bodies execute on an explicit heap state
machine: a `ResumableBody` holding a `Vec<Frame>` of suspended activation records
(one `Frame` variant per statement/expression form that can enclose a suspension),
plus the captured environments (`lexical_env`/`var_env`), `this`, the realm's global,
and the retained-AST `Arc` that keeps `NodeRef`/`ListRef` pointers alive.

- **Hybrid delegation is the key economy**: a frame is pushed only for subtrees that
  *contain* a `yield`/`await` (decided by `expr_contains_suspend`/`stmt_contains_suspend`,
  which treat nested function bodies as boundaries and `for await` as an intrinsic
  suspend point). Yield-free subtrees evaluate via the existing recursive evaluator
  (`Action::EvalExpr`/`EvalStmt`), so the frame machine only models the suspension
  *spine*, not the whole language.
- **Drive loop shape**: `resumable::drive` repeatedly calls `step()` under a short
  `RefCell` borrow; `step` either mutates frame state (`Continue`), pushes a child
  frame (`Push`), or requests an effect (`Do(Action)`) that `perform()` executes
  *outside* the borrow (all allocation/GC/user-code re-entry happens there). JS
  throws from actions become `Completion::Throw` feedback that unwinds frames,
  running `finally` blocks and closing iterators; host errors (OOM/budget) propagate
  as `Err` and **poison** the generator (state := completed, body dropped).
- **Spec anchors**: `[[GeneratorState]]` (suspendedStart/suspendedYield/executing/
  completed) lives on the `HeapObject::Generator` variant; `Generator.prototype.
  next/return/throw` implement GeneratorResume/GeneratorResumeAbrupt (§27.5.3) by
  injecting `Feedback::Value` / `Completion::Return` / `Completion::Throw` at the
  suspension point (the popped `Yield` frame's parent receives it, so injected
  completions route through enclosing `try/finally` exactly like the spec's abrupt
  resumption). Async functions are the same machinery driven internally
  (AsyncFunctionStart §27.7.5.1): `await` suspends with `SuspendKind::Await`; the
  driver resolves the operand via `PromiseResolve` and attaches
  `FunctionData::AwaitContinuation` natives through `PerformPromiseThen`
  (await-as-yield-to-microtask, §6.2.4/§27.7.5.3), settling the result promise on
  completion.
- **Rooting/tracing contract**: the suspended state is heap-reachable — `JsGenerator`
  traces its `ResumableBody` (all frame-held `Value`s, `IteratorRecord`s,
  `OwnedReference`s, saved environments, `this`, global). The body updates its
  `lexical_env` snapshot at every suspension so the resume reconstructs the exact
  scope chain. During the creation window (before the generator object exists) the
  captured envs are rooted by the still-active `RuntimeEnv` and `this`/callee by
  explicit scope roots. The `Rc<RefCell<…>>` indirection means GC tracing (which runs
  inside allocations, always outside `step`'s borrow) can read the body without
  aliasing the driver's mutation — a borrow conflict would panic loudly rather than
  corrupt.
- **Async generators + `for await` (2026-07-24)**: `FunctionFlavor::AsyncGenerator`
  shares the same frame machine. `%AsyncIteratorPrototype%` /
  `%AsyncGeneratorPrototype%` provide promise-returning `next`/`return`/`throw`;
  `await` keeps state `Executing` (single outstanding request; concurrent enqueue
  is a residual). `yield` uses AsyncGeneratorYield (await the yielded value, then
  settle the pending promise). `for await` extends the resumable `ForOf` frame:
  `GetAsyncIterator` (`@@asyncIterator`) → `next()` → `Suspend(Await)` →
  `IterResultParts`, with per-iteration `let`/`const` envs. Sync-iterable
  for-await uses `CreateAsyncFromSyncIterator` (wrap sync `IteratorRecord` in an
  `%AsyncFromSyncIteratorPrototype%` whose `next` returns
  `PromiseResolve({value,done})`). Concurrent async-generator request queues
  remain `Unimplemented`.
- **Boundary (explicit, visible)**: `yield`/`await` in remaining exotic positions
  (template literals, `new` args, call/new argument spread, destructuring
  targets, `switch`/`for-in` bodies) is `Unimplemented` rather than silently
  mis-evaluated. Array-literal `...` spread, object-literal members/spread, and
  computed / optional `?.[…]` members are supported on the resumable path. `with`
  is supported (Object Environment + `@@unscopables`) on both the recursive and
  resumable paths.

**Rejected alternatives**:
- *(b) AST→state-machine lowering at registration* (CPS-style splitting at suspension
  points): strictly more up-front complexity — every enclosing construct must be
  compiled into resumable blocks (the same coverage matrix as the frame machine)
  *plus* a new lowered IR + its GC story, while losing the recursive evaluator's
  battle-tested semantics for the yield-free 95%. Steady-state perf would be better,
  but generators are not the hot path in this VM's workloads.
- *(c) External coroutine crate* (corosensei-style stack switching): cleanest
  conceptually (suspend = stack switch, zero frame modeling), but it is a
  load-bearing dependency decision (unsafe stack juggling, platform support, and the
  GC would have to scan *foreign stacks* for roots — a fundamental conflict with the
  explicit-rooting Scope model). Per dependency doctrine this was not adoptable
  unilaterally; the analysis also concludes it is the wrong trade for a spec-shaped
  interpreter where suspended state must be precisely traceable.

### Reference model: primitive bases, no wrapper allocation on gets

Property access is evaluated through a spec-shaped `GetV` (`exec.rs::get_v`, ECMA-262
§7.3.2) whose **base may be a primitive `Value`, not just a `GcObject`**. This is a
permanent architectural decision, not a status detail:

- A member/computed access on a primitive (`"abc".length`, `(5).toFixed(2)`,
  `true.toString()`) does **not** allocate a wrapper object. `GetV` resolves the
  property against the matching well-known prototype (`String.prototype`,
  `Number.prototype`, …) with the primitive itself as the receiver. String `length`
  and canonical integer indices are handled as the String exotic own-properties
  (§10.4.3 / §22.1.3.1) *before* the prototype lookup.
- `null`/`undefined` bases throw a **catchable** `TypeError` ("Cannot read properties
  of …"), matching `ToObject` failing in §7.3.2 step 1 (previously a non-catchable
  `VmError::Unimplemented`).
- Method calls derive `this` from the base value, so `this` inside a called prototype
  method **is the primitive** — which is exactly how the native intrinsics read it
  (`this_number_value`/`this_string_units`/…). No boxing on the hot path.
- **Optional chains** (`?.`) are evaluated as a whole `OptionalExpression`
  (`exec.rs::eval_chain`) so a nullish `?.` short-circuit propagates through the
  remaining non-optional links (`a?.b.c` → `undefined`, not a throw). Parenthesization
  is a chain boundary: an inner short-circuit becomes a plain `undefined` value and
  does not propagate out (`(a?.b).c` throws), while the `this` binding from the inner
  reference is preserved (`(a.b)?.()` binds `this` to `a`). The `ParenthesizedExpr`
  assoc marker from `parse-js` is what distinguishes the two.

### Intrinsic namespace objects and BigInt representation

- **Namespace objects** (`Math`, `JSON`) are ordinary objects (proto = `%Object.prototype%`)
  built in `intrinsics.rs::Intrinsics::init`, rooted for the realm, exposed via an
  `Intrinsics` getter, and installed on the global object in `realm.rs`. Their methods
  are registered exactly like static constructor methods (`install_object_static_method`
  works on any target object, not just constructors), so `Math` is populated by looping a
  `(name, length, NativeCall)` table. `Math[@@toStringTag]`/`Math` constants are plain
  data properties. **Pattern to reuse for future namespaces** (`Reflect`, `Atomics`): add
  a field + getter to `Intrinsics`, build it in `init`, install it in `realm.rs`.
- **`JsBigInt` is a hybrid** (`value.rs`): **inline** sign + `u128` magnitude for the
  common path (keeps `Value: Copy`), and a **wide** path holding `NonNull<num_bigint::BigInt>`
  via `Box::leak` (immortal; GC-tracked BigInt is a later refinement). Decimal literals,
  arithmetic, and bitwise ops promote to the wide path on overflow; the inline path still
  uses the **exact 128-bit two's-complement window** (`twos_complement` /
  `from_twos_complement`) for `& | ^ << >>`. `>>>` remains `TypeError` (BigInts are not
  fixed-width). Exact BigInt↔Number equality/relational compare uses mathematical value
  (not `f64` round-trip) so `Number.MAX_VALUE` extremes work.

`runtime-js` is a deliberately small interpreter wrapper ("execute the curated
test262-semantic suite; grow into a full runtime") — the spec-shaped scaffolding that
`test262-semantic`'s default executor drives.

## WebIDL layer

`webidl` is runtime-agnostic scaffolding for WebIDL conversions and overload
resolution: IDL types (`DomString`/`ByteString`/`UsvString`, records, sequences,
unions, `FrozenArray`), conversion + `to_js` helpers, `WebIdlError`/`WebIdlLimit`, and
an abstract `JsRuntime` trait plus `InterfaceId` so binding generators can do fast
platform-object interface checks. It deliberately does not depend on `vm-js` —
embedders (FastRender) implement the hooks. `webidl-vm-js` is that adapter for
`vm-js`: `VmJsWebIdlCx` conservatively roots values it produces/consumes for the
conversion context's lifetime (WebIDL conversion code holds handles across
allocations, so it must root — see rules below).

## WebIDL host objects: rooting rules and wrapper caches

(Absorbed from `vm-js/docs/webidl_host_objects.md`, 2026-07 — the embedder contract
for exposing interfaces like `Window`/`Document`/`Node` and DOM wrapper objects.)

**Rooting rules (non-negotiable)**:

- Use a `Scope` + `push_root` whenever you allocate multiple objects and need earlier
  allocations alive across later ones (any allocation may GC), or while holding
  `Value`s in temporary Rust structures.
- Use persistent roots for objects that outlive a stack scope (intrinsics, `Window`,
  prototypes); keep the `RootId` and `remove_root` on teardown.
- **Wrapper identity caches must store weak handles.** A `NodeId → wrapper` cache
  holding roots leaks every wrapper forever; store `WeakGcObject` and
  `upgrade(&heap)` on lookup — collected wrappers reallocate fresh.
- **Host data must trace its JS edges.** Wrapper host payloads (event listener
  callbacks, `MutationObserver` callbacks, retained promise resolvers) are outgoing GC
  edges: host data lives on the heap as part of the allocation, and marking asks it to
  trace its handles. A missed trace = invalid-handle failures later (use-after-free
  shaped).

**Interface initialization pattern** (per interface): allocate
`Interface.prototype` (proto → parent interface's prototype or `Object.prototype`);
allocate the constructor (native, often construct-throws for non-constructible
interfaces like `Window`); wire `constructor.prototype` (non-writable data descriptor)
and `prototype.constructor` back-reference; set constructor's `[[Prototype]]` to
`Function.prototype`; define methods/attributes via `PropertyDescriptor` on the
prototype; install on the global per `[Exposed]`. Native functions receive
`(vm, scope, host: &mut dyn VmHost, hooks, callee, this, args)` — embedder state is
reached by downcasting `host`, never via globals. The full worked pseudo-code
(`Window` + `alert` + weak `NodeId` wrapper cache) lives in the source doc, which
remains the deep-dive reference.

## Verification

`test262-semantic` drives curated slices of the full test262 corpus against the VM
(harness modes, strict/non-strict variant expansion, expectation manifests — details
in [testing](../engineering/testing.md#test262-semantic-runner-test262-semantic)).
The recent commit log is a case study in oracle-driven development: each fix
corresponds to a spec-observable behavior (catchability of engine errors, top-level
`this` semantics, `Function.prototype.bind` for ECMAScript functions, GC rooting of
op inputs).

## test262 status

First measured pass-rate baseline for the `vm-js` stack (2026-07-23), established with
the `test262-semantic` runner (`--harness test262`, 5s per-test timeout, strict +
non-strict variant expansion). Counts are **case-level** (each test expands to two
variants). The `smoke` suite is 174/174 both before and after.

Seven curated language-core suites live in `test262-semantic/suites/` (`operators`,
`equality-relational`, `statements-control`, `types-coercion`, `asi`,
`builtins-basics`, and `generators-async`). Per-suite passed / unexpected-mismatch
(`--fail-on none`):

Passed counts, showing the autoboxing baseline → the current value after the
**built-ins program** (missing globals + BigInt bitwise/shift + wrapper receiver
coercion):

| Suite | Total | Passed → | Passed (built-ins) |
| --- | --- | --- | --- |
| operators | 1094 | 1011 | **1063** |
| equality-relational | 992 | 775 | **781** |
| statements-control | 1410 | 619 | **621** |
| types-coercion | 303 | 198 | **207** |
| asi | 204 | 134 | **134** |
| builtins-basics | 771 | 336 | **454** |

Net this program: **+187 passing cases** (builtins-basics +118, operators +52,
types-coercion +9, equality-relational +6, statements-control +2). `builtins-basics`
moves the most because `Math`, the `Number` statics, `parseInt`/`parseFloat`,
`Object.prototype.hasOwnProperty`, and `Object.getOwnPropertyDescriptor`/
`getOwnPropertyNames` (the last two unblock `propertyHelper.js`'s `verifyProperty`
across the whole corpus). `operators` rises entirely from **BigInt bitwise/shift**
(`& | ^ << >>`). `asi` is flat (its residual failures are parser early-errors, out of
vm-js scope). All six suites exit 0 under `--fail-on new`; the manifest trimmed
714 → **620** ids (94 now-passing entries removed, every one verified to pass both
strict and non-strict variants).

**Fixes (spec-shaped, cited at each `exec.rs`/`value.rs` site):**

- Bitwise `& | ^`, shifts `<< >> >>>`, and unary `~` — ECMA-262 §13.12 / §13.9 /
  §13.5.6 over `ToInt32`/`ToUint32` (§7.1.6/§7.1.7). Previously all fell through to
  `Unimplemented("binary operator")` (the single largest failure bucket).
- Exponentiation `**` — ECMA-262 §13.6 / `Number::exponentiate` (§6.1.6.1.3),
  including the `NaN`/`(±1) ** ±Infinity` edges IEEE-754 `pow` gets wrong.
- Abstract Relational Comparison `< > <= >=` — ECMA-262 §7.2.15 / §13.10: string
  operands now compare by UTF-16 code units (they were being coerced to Number, so
  `"a" < "b"` was wrong); NaN → `false`; BigInt and mixed BigInt/Number handled.
- Sequence (comma) operator — ECMA-262 §13.16.
- BigInt arithmetic `- / % **` and `~` — ECMA-262 §6.1.6.2, with `RangeError` on
  divide-by-zero / negative exponent and `TypeError` on `>>>` (BigInts are not
  fixed-width). Wide magnitudes use the hybrid `JsBigInt` path (see design note).
- **Optional-chain short-circuit propagation** — ECMA-262 §13.3.9 (ChainEvaluation).
  Previously the nullish check applied only at the immediate `?.` link, so `a?.b.c`
  with nullish `a` threw "member access on non-object". Now a `?.` short-circuit
  propagates through the whole `OptionalExpression` (`exec.rs::eval_chain`), with
  parenthesization resetting the boundary (`(a?.b).c` throws; `(a.b)?.()` preserves
  `this`), and `delete a?.b` short-circuits to `true` (§13.5.1.2). Cited at the fix
  sites in `exec.rs`.
- **Primitive autoboxing / `GetV`** — ECMA-262 §7.3.2 + §13.3.3. Member access and
  method calls on string/number/boolean/symbol/bigint primitives now resolve against
  the matching wrapper prototype with the primitive as receiver — **no wrapper object
  is allocated** (see the Reference-model design note above). Added the high-value
  `String.prototype` methods (`valueOf`, `charAt`, `charCodeAt`, `indexOf`, `includes`,
  `slice`, `substring`, `concat`, `toUpperCase`, `toLowerCase`), `Number.prototype`
  (`toString` incl. radix, `toFixed`), and `Boolean.prototype.toString`
  (`builtins.rs`, installed in `intrinsics.rs`).

**Built-ins program (2026-07-23, this program):**

- **Missing globals** — `Math` (§21.3: the elementary functions + `pow`/`atan2`/
  `hypot`/`min`/`max`/`random`/`sign`/`round`/`fround`/`clz32` and the `E`/`PI`/… value
  constants, with `Math[@@toStringTag] = "Math"`); global `parseInt`/`parseFloat`
  (§19.2.5/.4) and `isFinite` (§19.2.2); `Number` statics `isNaN`/`isFinite`/`isInteger`/
  `isSafeInteger` (§21.1.2, **no coercion** — distinct objects from the coercing global
  `isNaN`/`isFinite`), `parseInt`/`parseFloat` (§21.1.2.12/.13, the **same** function
  objects as the globals), and `MAX_SAFE_INTEGER`/`MIN_SAFE_INTEGER`/`EPSILON`;
  `String.fromCharCode` (§22.1.2.1, `ToUint16` per unit).
- **Object introspection** — `Object.prototype.hasOwnProperty` (§20.1.3.2, incl. String
  primitive `length`/index own-props), `Object.getOwnPropertyDescriptor` (§20.1.2.8, via
  `FromPropertyDescriptor` §6.2.6.4), and `Object.getOwnPropertyNames` (§20.1.2.10).
  These unblock test262's `propertyHelper.js` (`verifyProperty`) corpus-wide.
- **BigInt bitwise/shift** — `& | ^ << >>` (§6.1.6.2.18–.22); inline path uses the
  128-bit two's-complement window, wide path uses `num_bigint`. `>>>` still throws
  `TypeError` (BigInts are not fixed-width).
- **Wrapper receiver coercion** — `Number.prototype.valueOf`/`Boolean.prototype.valueOf`
  now route through `thisNumberValue`/`thisBooleanValue` and throw a **catchable**
  `TypeError` on an incompatible receiver (§21.1.3.7/§20.3.3.3), instead of a
  non-catchable `VmError::Unimplemented`.

Regression coverage: `vm-js/tests/numeric_binary_operators.rs` (operators, spec-derived),
`vm-js/tests/optional_chaining_and_autoboxing.rs` (optional-chain short-circuit,
parenthesized boundaries, `delete a?.b`, primitive length/index/method access, `this`
binding), and `vm-js/tests/builtins_globals_and_bigint_bitwise.rs` (BigInt bitwise/shift
incl. two's-complement negatives, `Math`, `parseInt`/`parseFloat`/`isFinite`, `Number`
statics, `String.fromCharCode`, `Object.prototype.hasOwnProperty`,
`Object.getOwnPropertyDescriptor`/`getOwnPropertyNames`, wrapper `valueOf` receiver
coercion — all spec-derived).

**Generators + async functions program (2026-07-23, this program):**

Sync generators and async functions are implemented on the resumable-body
architecture (see the design note under *Execution engine*). Suite deltas
(passed cases, built-ins baseline → after this program):

| Suite | Passed → | Passed (generators/async) |
| --- | --- | --- |
| operators | 1063 | **1063** |
| equality-relational | 781 | **783** |
| statements-control | 621 | **643** |
| types-coercion | 207 | **207** |
| asi | 134 | **134** |
| builtins-basics | 454 | **454** |

Net +24 passing cases — modest by design: the six language-core suites contain few
generator-focused tests (the dedicated `built-ins/GeneratorFunction`/`async-function`
test262 directories are not yet in any curated suite; adding a generators suite is
the natural next measurement). The real coverage evidence is unit-level:
`vm-js/tests/generators.rs` (39 tests: yield both directions, first-next argument
ignored, yield in binary/call/array/conditional/loop positions, `return()`/`throw()`
at suspendedStart vs suspendedYield, yield-in-finally deferring return completion,
catch across suspension, for-of integration incl. break→IteratorClose→finally,
spread, `yield*` delegation over generators and arrays incl. next-argument and throw
forwarding, prototype wiring (`Object.getPrototypeOf(g()) === g.prototype`, shared
`%GeneratorPrototype%`, non-constructor TypeError), closures/`this`, reentrant-next
TypeError, and suspended-state-survives-GC with forced collections) and
`vm-js/tests/async_functions.rs` (17 tests: result-promise identity/state,
synchronous-until-first-await, await of plain values / resolved + rejected promises /
thenables, rejection→catch, finally-across-await, microtask sequencing, await in
loops, async arrows incl. lexical `this` and expression bodies, non-constructor,
suspended-state-survives-GC).

Also fixed here: `get_iterator` now uses the realm's **well-known `@@iterator`
symbol** (it previously looked up a `Symbol.for`-registry symbol that could never
match `Symbol.iterator`-keyed methods — invisible until now because arrays
short-circuit through the fast path).

**Follow-ups (2026-07-23, post generators/async program):**

1. **`eval_catch` GC rooting** — thrown values are rooted across catch-env creation
   (see [Heap and GC](#heap-and-gc)); regression in `exec_stmt`.
2. **Switch CaseBlock scoping** — GeneratorDeclaration / AsyncFunctionDeclaration in
   `switch` case clauses are lexically scoped to the CaseBlock (§14.12 / §14.2.3);
   Annex B.3.2 var-hoisting applies only to *ordinary* `function` declarations.
   `scope-lex-generator` / `scope-lex-async-function` / `scope-lex-async-generator`
   share a residual negative-type classification gap (error `name` not seen by the
   harness); flavor boundary for async generators is cleared.
3. **`flags: [async]` host wiring** — `assemble_source` prepends `doneprintHandle.js`
   when `flags` contains `async`; `VmJsExecutor` installs `print`, runs
   `perform_microtask_checkpoint` after the script (no-op when the queue is empty),
   and treats `Test262:AsyncTestComplete` / `Test262:AsyncTestFailure:` per
   test262 INTERPRETING.md. Optional-chaining async + for-await ids now pass;
   residue is exotic await positions (precise reasons).
4. **`generators-async` measurement suite** — new curated suite
   `test262-semantic/suites/generators-async.toml` (statements/expressions
   `generators` + `async-function` + `await`; excludes `_FIXTURE`/modules). Baseline
   (`--fail-on none`): **1394** cases, **732** passed, **442** expected mismatches
   after manifesting 240 new ids under grouped reasons (destructuring/iterator ~116,
   ToString-on-objects ~34, parser early-errors ~21, resumable-frame boundaries
   spread/exotic-yield ~12, statement/expression gaps ~20, …). Exits 0 under
   `--fail-on new`. Report: `reports/generators-async-baseline.json`.
5. **`let`-newline ASI (parse-js)** — the 8 manifested `PS0018` ids now pass after the
   concurrent parse-js fix and were removed from the manifest.

Suite floors after these follow-ups (passed cases; historical snapshot — current
floors are under the wrapper-method cluster note below):

| Suite | Passed (floor) |
| --- | --- |
| operators | **1063** |
| equality-relational | **783** |
| statements-control | **647** |
| types-coercion | **213** |
| asi | **134** |
| builtins-basics | **454** |
| generators-async | **732** (new) |

Manifest size: **773** ids (546 after the generators/async program, −2 switch
scope-lex, −3 async-flag now-passing, −8 let-newline, +240 generators-async baseline).

**`Function` constructor program (2026-07-24):**

Implements `CreateDynamicFunction` (§20.2.1.1.1) for `%Function%` (`Function(…)` /
`new Function(…)`): `ToString` of parameter/body args, parse as a parenthesized
`FunctionExpression`, register a retained `ParsedProgram` + `EcmaFunctionId`,
`SetFunctionName("anonymous")`, `MakeConstructor`, and `[[Prototype]]` via
`GetPrototypeFromConstructor`. GeneratorFunction / AsyncFunction kinds share the
same helper path (not yet wired as globals). Unit coverage:
`vm-js/tests/function_constructor.rs` (11 tests).

| Suite | Passed → | Passed (`Function` ctor) |
| --- | --- | --- |
| operators | 1063 | **1065** (+2) |
| equality-relational | 783 | **811** (+28) |
| builtins-basics | 454 | **456** (+2) |
| statements-control | 647 | **647** |
| types-coercion | 213 | **213** |
| asi | 134 | **134** |
| generators-async | 732 | **732** |

Net **+32** passing cases; **16/17** manifested `Function constructor not
implemented` ids unblocked. Residual: `language/expressions/typeof/native-call.js`
(`missing global: RegExp` — Function/`Date` typeof checks now pass). Manifest
773 → **757**.

**Async generators + `for await` program (2026-07-24):**

Extends the dual-path resumable architecture with `FunctionFlavor::AsyncGenerator`
(§27.6) and resumable `for await` over `@@asyncIterator` iterables. Also lands
minimal `Array.prototype.push` (unblocks await-interleave tests that log via
`actual.push`). Unit coverage: `vm-js/tests/async_generators.rs` (10 tests).

| Suite | Passed (`Function` ctor) → | Passed (async gen / for-await) |
| --- | --- | --- |
| operators | 1065 | **1069** (+4) |
| equality-relational | 811 | **811** |
| builtins-basics | 456 | **456** |
| statements-control | 647 | **647** |
| types-coercion | 213 | **217** (+4) |
| asi | 134 | **134** |
| generators-async | 732 | **744** (+12) |

Net **+20** passing cases. Unblocked ids include
`async-generator-interleaved`, `for-await-of-interleaved`,
`iteration-statement-for-await-of`, plus latent await-interleave xpasses via
`Array.prototype.push`. Residual boundary: concurrent async-generator
next/return/throw while executing; exotic yield/await positions;
`scope-lex-async-generator` still xfail (negative ReferenceError
type-classification gap shared with `scope-lex-generator`). Manifest 757 →
**749**.

**`RegExp` global + `CreateAsyncFromSyncIterator` (2026-07-24):**

Two small residuals from the Function-ctor / async-gen ladder:

1. **Minimal `%RegExp%`** — callable/constructable stub (`source`/`flags`/
   `lastIndex`, `@@toStringTag`); no regex engine. Unblocks
   `language/expressions/typeof/native-call.js`.
2. **`CreateAsyncFromSyncIterator`** — `GetIterator` (async hint) falls back to
   sync `GetIterator` + wrap; `%AsyncFromSyncIteratorPrototype%.next` steps the
   sync record (array fast-path or protocol) and returns
   `PromiseResolve(iterResult)`. Full `AsyncFromSyncIteratorContinuation`
   thenable-unwrap of `value`, plus `return`/`throw`, remain residuals.

Unit coverage: `vm-js/tests/regexp_builtin.rs` (3), `async_generators.rs` (+2
sync for-await cases; 12 total).

| Suite | Passed (async gen) → | Passed (RegExp / AFSI) |
| --- | --- | --- |
| operators | 1069 | **1069** |
| equality-relational | 811 | **815** (+4) |
| builtins-basics | 456 | **456** |
| statements-control | 647 | **647** |
| types-coercion | 217 | **217** |
| asi | 134 | **134** |
| generators-async | 744 | **744** |

Net **+4** passing cases (typeof/`RegExp` surface in equality-relational;
`for-await-of` sync cases are not yet in a curated suite — covered by unit
tests). Manifest 749 → **748**.

**Wrapper-method cluster (2026-07-24):**

Highest-leverage residue from the GetV/autoboxing program — methods and
receiver slots that unblock harness helpers and large `Number.prototype`
buckets:

- `Number.prototype` / `Boolean.prototype` carry `[[NumberData]]=+0` /
  `[[BooleanData]]=false` (unblocks `Number.prototype.toString()` /
  `Boolean.prototype.toString()` and the radix `A2_T*` matrix).
- `Object.prototype.toString` tags Number/Boolean/String wrappers + arrays
  (and honors `@@toStringTag` when present).
- `Array.isArray` + array-rest `ArrayCreate` in destructuring (was allocating
  a plain object — `assert(Array.isArray(x))` failed corpus-wide).
- `Number.prototype.toExponential` / `toPrecision` (ryu digit rounding;
  non-finite early-return before range checks), `toFixed`/`toString` radix
  `RangeError`, `String.prototype.split` (string separator).

| Suite | Passed (RegExp/AFSI) → | Passed (wrapper cluster) |
| --- | --- | --- |
| builtins-basics | 456 | **616** (+160) |
| statements-control | 647 | **693** (+46) |
| generators-async | 744 | **800** (+56) |
| operators | 1069 | **1069** |
| equality-relational | 815 | **815** |
| types-coercion | 217 | **217** |
| asi | 134 | **134** |

Net **+262** passing cases. Manifest 748 → **614**. Wrapper-related residual
ids ≈ **37** (was ~127 / roadmap ~64): precision digit-string edges,
`toString` radix `a-z` (blocked on `for (let)` re-init), wrapper-object
identity, and misc `length`/`name`/`prop-desc` surface.

**>128-bit BigInt program (2026-07-24):**

Hybrid `JsBigInt` (inline `u128` + immortal `num_bigint` wide path; see design
note). Unblocks large decimal literals, `**` / `<<` / `>>` beyond 128 bits, and
exact BigInt↔Number extremes (`Number.MAX_VALUE`). Also closed a latent Annex B
bug: nested `function*` / `async function` in `switch` no longer receive a
var binding (CaseBlock lexical only) — fixes `scope-lex-generator` /
`scope-lex-async-function` / `scope-lex-async-generator`.

| Suite | Passed (wrapper) → | Passed (wide BigInt) |
| --- | --- | --- |
| operators | 1069 | **1077** (+8) |
| equality-relational | 815 | **839** (+24) |
| generators-async | 800 | **804** (+4) |
| statements-control | 693 | **693** |
| builtins-basics | 616 | **616** |
| types-coercion | 217 | **217** |
| asi | 134 | **134** |
| smoke | 174 | **174** |

Net **+36** passing cases. Manifest 614 → **601** (12 BigInt width/extremes ids
+ `scope-lex-async-generator`). All seven suites + smoke exit 0 under
`--fail-on new`.

**Destructuring / iterator-protocol program (2026-07-24):**

Burned down the largest semantic residual buckets in `language-core.toml`
(~88 generator/async param + ~36 `for`/`let`/`const`/`var` binding-pattern ids,
plus adjacent un-triaged fn-name / iter-close / Array.prototype[@@iterator]
override cases that shared the same root cause):

- `GetIterator` always uses the iterator protocol (no Array exotic fast-path bypass).
- `%Array.prototype%.values` / `%Array.prototype%[@@iterator]` +
  `%ArrayIteratorPrototype%.next` (`CreateArrayIterator`).
- Array BindingInitialization = GetIterator → IteratorBindingInitialization
  (elision steps, rest `ArrayCreate`, nested patterns) →
  `IteratorClose` when not exhausted (completion-aware).
- SingleNameBinding defaults: `IsAnonymousFunctionDefinition` + `SetFunctionName`
  (arrow / `function` / `function*` / cover parentheses; class deferred).

| Suite | Passed (wide BigInt) → | Passed (dstr/iterator) |
| --- | --- | --- |
| statements-control | 693 | **837** (+144) |
| generators-async | 804 | **980** (+176) |
| operators | 1077 | **1077** |
| equality-relational | 839 | **839** |
| builtins-basics | 616 | **616** |
| types-coercion | 217 | **217** |
| asi | 134 | **134** |
| smoke | 174 | **174** |

Net **+320** passing cases (160 unique ids × strict/non-strict variants).
Manifest 601 → **437** (−160). Iterator-protocol dstr buckets **cleared**.

**Proxy / PutValue + ToPrimitive / propertyHelper program (2026-07-24):**

Finished the mid-flight Proxy install and burned the largest vm-js-owned
residual clusters in the same suite window (property-desc surface, ToString
on objects, wrapper `==` / `Number(wrapper)`):

- **`%Proxy%` on the global** — `ProxyCreate` (`[[ProxyTarget]]` /
  `[[ProxyHandler]]`), callable proxies keep `typeof "function"` after revoke,
  `Proxy.revocable`, Proxy `[[Set]]` (`set` trap).
- **OrdinarySet parent.`[[Set]]`** — own-property check then
  `parent.[[Set]](P,V,Receiver)` so a Proxy on the prototype chain receives
  `[[Set]]` (PutValue-through-spy).
- **PutValue on primitive bases** — Set starts at the matching intrinsic
  prototype with the primitive as receiver (§6.2.5.5).
- **Vm-aware `ToPrimitive` / `ToString` / `ToNumber` / `ToPropertyKey`**
  (`spec_ops`, §7.1.1 / §7.1.17 / §7.1.4 / §7.1.19) — `@@toPrimitive` then
  OrdinaryToPrimitive; wired into `String()`, `Array.prototype.join`,
  `Number()` / `new Number`, `CreateDynamicFunction`, `Error.prototype.toString`,
  `parseInt`/`parseFloat`, and computed property keys.
- **Abstract equality `ToPrimitive`** — evaluator prepares Object vs
  String/Number/BigInt/Symbol/Boolean operands via real `valueOf`/`toString`
  (heap stub cannot invoke methods); Object↔Object stays reference equality;
  Null/Undefined do not trigger conversion.
- **`Object.prototype.propertyIsEnumerable`** (§20.1.3.5) — unblocks
  test262 `propertyHelper.js` / `verifyProperty` across Number/Boolean
  `length`/`name`/`prop-desc` / `EPSILON` / statics.
- **`Number.prototype.toLocaleString`** — locale-independent fallback (= `toString`).
- **`Object.prototype.valueOf`** — `ToObject(this)` (§20.1.3.7); unblocks
  `'valueOf' in {}` and Number/Boolean wrapper coercion edges.
- **`Reflect.construct`** / **`RegExp.prototype.exec`** stub (prior mid-flight).

| Suite | Passed (dstr/iterator) → | Passed (Proxy/ToPrimitive + follow-ups) |
| --- | --- | --- |
| builtins-basics | 616 | **731** (+115) |
| equality-relational | 839 | **897** (+58) |
| generators-async | 980 | **1044** (+64) |
| statements-control | 837 | **865** (+28) |
| types-coercion | 217 | **229** (+12) |
| operators | 1077 | **1077** |
| asi | 134 | **134** |
| smoke | 174 | **174** |

Net **+275** vs dstr/iterator floor. Manifest 437 → **173**.
Follow-ups: parameter-expression body env (`let arguments`); `eval` parse →
throwable `SyntaxError`; for-header function ASI; spaced optional call; named
FunctionExpression immutable name binding (sloppy no-op / strict TypeError).
`missing global object/constructor` (prop-desc/length/name surface) and
`wrapper-object (new Boolean/new Number)` buckets are **cleared**. All eight
suites exit 0 under `--fail-on new`.

**Mapped arguments + global `eval`/`BigInt` (2026-07-24 late++):**

- **CreateMappedArgumentsObject** for non-strict functions with a simple
  parameter list — integer indices get `MakeArgGetter`/`MakeArgSetter` native
  accessors over the parameter Environment Record (test262
  `evaluation-mapped-arguments.js`; defaults/rest/destructuring stay unmapped).
- **Global `%eval%`** — installed on the realm global; identifier `eval(...)`
  remains direct `PerformEval`; `eval?.(...)` / other value-calls intercept as
  **indirect** eval (global lexical + `VarEnv::GlobalObject`).
- **Global `%BigInt%`** — `BigInt(value)` (not constructable) + existing
  `Object(bigint)` boxing; clears `typeof/bigint.js`.
- **Async FDI abrupt → promise reject** — parameter TDZ/abrupt during
  `instantiate_function` rejects the preallocated result promise (EvaluateAsyncFunctionBody).

| Suite | Passed (Proxy/ToPrimitive) → | Passed (mapped args / eval / BigInt) |
| --- | --- | --- |
| generators-async | 1044 | **1068** |
| equality-relational | 897 | **899** |
| types-coercion | 229 | **231** |
| builtins-basics | 731 | **759** (`isPrototypeOf` + `toExponential`/`toPrecision`/`Array.toString`) |
| others | (unchanged) | smoke **174**, statements **865**, operators **1077**, asi **134** |

### 2026-07-24 late+++ — `for (let)` per-iteration + toString radix

| Suite | Prior → | Passed |
| --- | --- | --- |
| builtins-basics | 759 | **765** (`toString/a-z` + poisoned radix + `toPrecision/exponential`) |
| statements-control | 865 | **881** (nested for-let continue + scope-head/body lex + head-let-destructuring) |

Manifest **146 → 135**. Implemented ECMA-262 `for (let/const)` **loopEnv** +
`CreatePerIterationEnvironment` in both the recursive evaluator and the resumable
driver (closures in init vs body/test/incr capture correctly; nested `for (let)` no
longer hits "binding already initialized"). `Number.prototype.toString(radix)` now
uses full `spec_ops::to_number` so poisoned `valueOf` throws `Test262Error`.
`toPrecision` uses exact `floor(log10)` + IEEE significand digits (clears
`toPrecision/exponential.js`).

Also landed in the same wave: full compound + logical assignment operators in the
recursive evaluator; BigInt↔String/`toString` object path via `StringToBigInt`
(empty/`0x`/`0b`/`0o`). Floors: equality **907**, statements **889**, operators
**1079**, builtins **765**; manifest **126**.

### 2026-07-25 — ClassDeclaration / ClassExpression (base)

Minimal class evaluation in `exec.rs` (ECMA-262 ClassDefinitionEvaluation, base
classes only):

- **ClassDeclaration** — immutable lexical binding (TDZ until evaluation), including
  CaseBlock / block scope (`switch`/`{}`).
- **ClassExpression** — anonymous + named; named expressions bind the name in a
  fresh class environment (immutable).
- **Constructor** — explicit `constructor` method, or default native
  `constructor() {}` (`MakeClassConstructor`: `[[Call]]` throws TypeError).
- **Methods / getters / setters** — instance + `static`, non-enumerable; class
  bodies are strict.
- **NamedEvaluation** for anonymous classes in SingleNameBinding defaults (name
  applied *before* static elements so `static name()` can overwrite). Follow-up
  (2026-07-30): `eval_named_initializer` no longer re-applies the inferred name
  *after* class evaluation — `SetFunctionName` only fires when the function has
  no real name yet (anonymous default `""` still takes it), so a static
  `name()` method survives (`var xCls2 = class { static name() {} }` →
  `typeof xCls2.name === "function"`, matching V8).

Deferred at the time: `extends` / `super` (landed below), private elements /
`#x in`, fields (static blocks landed in the follow-up below).

| Suite | Prior → | Passed |
| --- | --- | --- |
| statements-control | 889 | **901** (+12; for/`dstr` fn-name-class ×6 ids) |
| generators-async | 1068 | **1084** (+16; generator `dstr` fn-name-class ×8 ids) |
| others | (unchanged) | operators **1079**, equality **907**, types **231**, asi **134**, builtins **765**, smoke **174** |

Manifest **126 → 111** (−15). Cleared: 6 `for/dstr/*fn-name-class*`, 8
generator `dstr/*fn-name-class*`, `switch/scope-lex-class`. Residuals retagged:
private-in (11), `class extends` / `super` (2 optional-chaining ids; cleared below).

### 2026-07-25 — `class … extends` + `super()` / `super.prop`

Minimal derived-class support on top of base ClassDefinitionEvaluation:

- **Heritage** — evaluate `extends` in the class env; wire
  `ctor.[[Prototype]]` / `proto.[[Prototype]]`; `[[ConstructorKind]]=derived`.
- **Default derived ctor** — native `constructor(...args){ super(...args); }`.
- **`[[HomeObject]]`** — `MakeMethod` on constructors + methods/getters/setters.
- **`super()`** — `Construct(GetSuperConstructor(), args, newTarget)` + BindThisValue
  (derived ctors start with uninitialized `this`).
- **`super.prop` / `super[k]`** — Get from GetSuperBase with receiver = this;
  optional-chain call sites (`super.method?.()`, `super()?.a`) covered.

| Suite | Prior → | Passed |
| --- | --- | --- |
| types-coercion | 235 | **239** (+4; optional-chaining `call-expression` + `super-property-optional-call` ×2 variants) |
| others | (unchanged) | statements **919**, generators-async **1119**, operators **1079**, equality **907**, asi **134**, builtins **765**, smoke **174** |

Manifest **76 → 74** (−2). Cleared: the two `unimplemented class extends / super`
optional-chaining ids. Residuals: private class elements (cleared in the
private-in note below).

### 2026-07-25 — non-writable globals / `instanceof` @@hasInstance / MakeConstructor proto

Cleared three residual clusters (**+22** cases; manifest **74 → 61**):

- **`var` assign to non-writable globals** — `Infinity`/`NaN`/`undefined` SetMutableBinding
  is a sloppy no-op (strict TypeError); cleared `S8.5_A10_T2` / `S8.5_A4_T2` / `S8.1_A3_T2`.
- **`InstanceofOperator`** — `GetMethod(@@hasInstance)` before IsCallable (plain objects
  with `Symbol.hasInstance` work); also cleared adjacent instanceof residuals
  (`S11.8.6_A6_T4`, primitive/getter prototype, `symbol-hasinstance-get-err`).
- **MakeConstructor + `Object.preventExtensions`** — `F.prototype` is
  `OrdinaryObjectCreate(%Object.prototype%)`; `preventExtensions`/`isExtensible` installed.
  Cleared `S8.6.2_A1` / `S8.6.2_A8` / `8.7.2-5-s`. Side fix: CreateImmutableBinding `S`
  flag (`const`/class strict vs named-fn-expr non-strict).

| Suite | Prior → | Passed |
| --- | --- | --- |
| types-coercion | 239 | **247** (+8) |
| equality-relational | 907 | **921** (+14) |
| others | (unchanged) | operators **1079**, statements **919**, generators-async **1119**, asi **134**, builtins **765**, smoke **174** |

### 2026-07-25 — `Object.defineProperties` + latent XPASS sweep

- **`Object.defineProperties`** — `ObjectDefineProperties` (enumerable own keys →
  `ToPropertyDescriptor` → `DefinePropertyOrThrow`); shared helper with
  `Object.defineProperty`. Tiny related gap: `Object.create(O, Properties)` now
  calls the same path when `Properties` is present.
- Cleared residual `typeof/get-value.js` (old “missing prototype method” tag).
- Latent XPASS hygiene (already green from prior FDI / eval / param-body work):
  async-function `*eval-var-scope-syntax-err*`, generator
  `scope-paramsbody-var-open` (expr + stmt).

| Suite | Prior → | Passed |
| --- | --- | --- |
| equality-relational | 921 | **923** (+2) |
| others | (unchanged) | operators **1079**, statements **919**, generators-async **1119**, types **247**, asi **134**, builtins **765**, smoke **174** |

Manifest **61 → 55**. Cleared ids: `typeof/get-value.js`, 3 async
`*eval-var-scope-syntax-err*`, 2 `scope-paramsbody-var-open`. Residuals in the
former “missing prototype method” tag: **none**.

### 2026-07-25 — private class elements / `#x in`

Minimal private-element support for `#PrivateIdentifier in` presence checks:

- **Private names** — unique symbols bound in the class env (PrivateEnvironment
  stand-in); methods resolve `#name` via the lexical outer chain.
- **`[[PrivateElements]]`** — presence keys on instances; installed via
  `InitializeInstanceElements` (base ctor / default ctor / after `super()`).
- **`#x in obj`** — recursive + resumable paths; TypeError on non-object RHS.
  Fields / methods / accessors / nested-class shadowing covered. Private method
  *invocation* and public field init remain deferred.

| Suite | Prior → | Passed |
| --- | --- | --- |
| equality-relational | 923 | **945** (+22; 11 ids × strict/non-strict) |
| others | (unchanged) | operators **1079**, statements **919**, generators-async **1119**, types **247**, asi **134**, builtins **765**, smoke **174** |

Manifest **55 → 44** (−11). Cleared: all
`unimplemented private class elements / private-in` ids. Residuals in that tag:
**none**. Remaining private-element gaps (get/set, `this.#x`, static private) are
outside this cluster.

### 2026-07-25 — BigInt↔String `IsLessThan` via `StringToBigInt`

Relational BigInt↔String now matches ECMA-262 §7.2.15 (same primitive path as
abstract equality): `StringToBigInt` before `ToNumeric`. Incomparable strings
(`"0."`, `"1e0"`, …) yield `undefined` → all four operators false; integers past
`2^53` stay exact (no f64 round-trip).

| Suite | Prior → | Passed |
| --- | --- | --- |
| equality-relational | 945 | **957** (+12; 6 ids × strict/non-strict) |

Manifest **44 → 38** (−6). Cleared:
`greater-than/bigint-and-string`, `less-than-or-equal/bigint-and-string`, and the
four `*/bigint-and-incomparable-string` ids. Residuals in that tag: **none**.

### 2026-07-25 — `with` / ObjectEnv + class static blocks

Cleared the residual cluster tagged
`unimplemented: statement type in generator/async body` (12 ids / **+14** cases):

- **`with` statement** — NewObjectEnvironment(`withEnvironment=true`);
  Object Environment Record `HasBinding`/`Get`/`Set` honor `@@unscopables`.
  Resumable `Frame::With` covers yield/await on the object expr or in the body
  (suspend-free `with` still delegates to the recursive evaluator).
- **Class static blocks** — evaluate the block statement list in a fresh
  declarative env with `this` = constructor (enough for `await`-as-identifier
  early-error tests inside nested generators).

| Suite | Prior → | Passed |
| --- | --- | --- |
| generators-async | 1084 | **1098** (+14) |
| others | (unchanged) | operators **1079**, equality **907**, statements **901**, types **231**, asi **134**, builtins **765**, smoke **174** |

Manifest **111 → 99**. Cleared: 10 `*unscopables-with*` (async/generator), 2
`static-init-await-*`. Residuals in that former tag: **none**.

### 2026-07-25 — resumable array-literal spread (IteratorSpread)

Cleared the residual cluster tagged
`unimplemented: spread in suspendable array literal (resumable-frame boundary)`
(6 ids / **+12** cases):

- **`Frame::ArrayLit` Rest elements** — evaluate the spread source (suspend-capable),
  `GetIterator`, then `IteratorStepValue` + `ArrayDefine` in a loop, matching the
  recursive evaluator's IteratorSpread path (`eval_lit_arr`).

| Suite | Prior → | Passed |
| --- | --- | --- |
| generators-async | 1098 | **1110** (+12) |
| others | (unchanged) | operators **1079**, equality **907**, statements **901**, types **231**, asi **134**, builtins **765**, smoke **174** |

Manifest **90 → 84** (−6). Cleared: 4 expression + 2 statement `*yield-spread-arr-*`.
Residuals in that former tag: **none**.

### 2026-07-25 — resumable object-literal + computed/optional member

Cleared residual clusters tagged
`unimplemented: yield/await in exotic expression position (resumable-frame boundary)`
(6 ids / **+9** generators-async cases) and
`unimplemented: yield/await in optional-chain / computed-member expression position`
(2 ids / **+4** types-coercion cases):

- **`Frame::ObjectLit`** — member walk with suspend-capable Prop values / object
  spread (`CopyDataProperties`), matching `eval_lit_obj`.
- **`Frame::ComputedMember`** — object then key, with `?.` nullish short-circuit
  before key eval; suspend-free optional-chain bases use `EvalChain` so
  `a?.b[await…]` propagates short-circuit (does not evaluate the key).

| Suite | Prior → | Passed |
| --- | --- | --- |
| generators-async | 1110 | **1119** (+9) |
| types-coercion | 231 | **235** (+4) |
| others | (unchanged) | operators **1079**, equality **907**, statements **919**, asi **134**, builtins **765**, smoke **174** |

Manifest **84 → 76** (−8). Cleared: `*yield-spread-obj*`, `*yield-identifier-spread-non-strict*`,
`optional-chain-async-*-square-brackets`. Residuals in those tags: **none**.

### 2026-07-25 — non-TCO language-core residual burn-down

Cleared **12** non-TCO `xfail` ids (manifest **38 → 26**; **21** honest TCO remain,
**5** realm/`$262` residuals). TCO xfails untouched.

| Fix | Cleared ids |
| --- | --- |
| `GetMethod` nullish → TypeError (`ToObject`) | `optional-chaining/iteration-statement-for-of-type-error` |
| `LitRegex` + `RegExp.prototype.test` (Rust `regex`) | `optional-chaining/member-expression` (was mis-tagged short-circuit) |
| parse-js IdentifierName unicode decode (`\u` / `\u{…}`) | `optional-chaining/optional-chain-prod-identifiername` |
| FDI: non-strict body lex≠var; param-expr lex≠var + EvalDeclarationInstantiation conflict walk | `*generators/scope-body-lex-distinct*`, `*generators/eval-var-scope-syntax-err*` |
| Resume pushes `ParsedProgram` for nested function registration | `*async-function/try-reject-finally-reject*` |
| NamedEvaluation on `var`/`let`/`const`/`=` | `expressions/generators/implicit-name` |
| `%Function.prototype%` `caller`/`arguments` → `%ThrowTypeError%` | `statements/generators/restricted-properties` (mis-tagged dstr) |
| `Number(bigint)` via ToNumeric + ℝ→Number | `built-ins/Number/bigint-conversion` |

| Suite | Prior → | Passed |
| --- | --- | --- |
| generators-async | 1119 | **1131** (+12) |
| types-coercion | 235 | **253** (+18; includes adjacent optional-chain XPASSes from LitRegex/unicode) |
| builtins-basics | 765 | **767** (+2) |
| others | (unchanged) | operators **1079**, equality **957**, statements **919**, asi **134**, smoke **174** |

Manifest **76 → 26** (−12 non-TCO; floor recount after prior trims). Remaining non-TCO:
realm/`$262` only. All primary suites + smoke exit 0 under `--fail-on new`.

### 2026-07-25 — `$262.createRealm` host + foreign-eval restore

Cleared the last **5** non-TCO language-core xfails (manifest **26 → 21**; TCO-only).

| Fix | Cleared ids |
| --- | --- |
| Harness `$262` (`createRealm` + `global`) on primary + secondary realms | `Boolean`/`Number` `proto-from-ctor-realm`, `generators/eval-body-proto-realm`, get/put `*-prop-base-primitive-realm` |
| `eval_perform_eval_string` restores caller globals/intrinsics/`this` after foreign-realm indirect eval | (required for multi-eval cross-realm scripts) |

| Suite | Prior → | Passed |
| --- | --- | --- |
| builtins-basics | 767 | **771** (+4) |
| generators-async | 1131 | **1133** (+2) |
| types-coercion | 253 | **257** (+4) |
| others | (unchanged) | operators **1079**, equality **957**, statements **919**, asi **134**, smoke **174** |

Manifest **26 → 21** (honest TCO only). All primary suites + smoke exit 0 under `--fail-on new`.

Residual: TCO (`features:[tail-call-optimization]`, honestly reason-tagged) — **do not fake green**.
Private-in presence checks are cleared (see note above).

### 2026-07-25 — Map / Set collections program

New curated suite `builtins-collections` (`built-ins/Map/**`, `built-ins/Set/**`,
excluding deferred `groupBy` / `getOrInsert*`; Set composition later unlocked).

- **`%Map%` / `%Set%`** — constructor (+ iterable via `AddEntriesFromIterable`),
  `get`/`set`/`add`/`has`/`delete`/`clear`/`size`, SameValueZero (+0/−0/NaN),
  iteration (`keys`/`values`/`entries`/`forEach`/`@@iterator`), `@@toStringTag`,
  `@@species` getter. `[[MapData]]`/`[[SetData]]` as GC-traced entry arrays.
- **WeakMap / WeakSet constructor stubs** — enough for Map/Set methods to throw
  TypeError (not ReferenceError) on weak receivers.
- **`Array.prototype.pop` / `shift`** — unblock forEach/insertion-order helpers.
- **`String(symbol)`** → `SymbolDescriptiveString` (ECMA-262 §22.1.1.1 special
  case; distinct from throwing `ToString` on Symbol) — unblocks
  `propertyHelper.js` on `@@iterator` / `@@toStringTag` / `@@species`.

| Suite | Prior → | Passed |
| --- | --- | --- |
| builtins-collections | *(new)* | **696** / 704 (4 ids ×2 variants xfail) |
| builtins-basics | 771 | **771** (no regression) |
| equality-relational | 957 | **957** (no regression) |
| language-core | TCO plateau | **21** TCO xfails unchanged |

Manifest: `test262-semantic/manifests/builtins-collections.toml` (**4** ids).
Suite + smoke + builtins-basics + equality-relational exit 0 under `--fail-on new`.

### 2026-07-25 — WeakMap/WeakSet + Map/Set proto-from-ctor realm

| Fix | Cleared / unlocked |
| --- | --- |
| `GetPrototypeFromConstructor` default proto from `GetFunctionRealm(newTarget)` for Map/Set/WeakMap/WeakSet | `Map`/`Set` `proto-from-ctor-realm` **XPASS** (manifest **4 → 2**) |
| **`%WeakMap%` / `%WeakSet%`** get/set/has/delete (+ iterable ctor), `CanBeHeldWeakly` (Objects + unregistered Symbols); entries stored strongly for now | suite includes `built-ins/WeakMap/**` + `WeakSet/**` (exclude `getOrInsert*`); **204** + **170** all pass |
| `Symbol.for` / `Symbol.keyFor` | required by WeakMap/WeakSet CanBeHeldWeakly tests |

| Suite | Prior → | Passed |
| --- | --- | --- |
| builtins-collections | 696 / 704 | **1074** / 1078 (2 ids ×2 variants xfail) |
| builtins-basics | 771 | **771** (no regression) |
| smoke | 174 | **174** (no regression) |

Manifest: `test262-semantic/manifests/builtins-collections.toml` (**2** ids —
TypedArray/`WeakRef` only: `Map/valid-keys`, `Set/valid-values`). Residue: true
weak GC edges, `getOrInsert*`, TypedArray/WeakRef globals.

### 2026-07-25 — Minimal TypedArray + WeakRef (collections XPASS)

Cleared the last **2** builtins-collections xfails (`Map/valid-keys`,
`Set/valid-values`) with honest minimal globals (not stubs that lie about
identity):

- **`Int32Array` / `Uint32Array` / `BigInt64Array` / `BigUint64Array`** —
  construct-only surface: `new TA(arrayLike)` sets `length`, copies converted
  indexed elements, `BYTES_PER_ELEMENT`, `@@toStringTag`. No ArrayBuffer /
  DataView / detach / exotic `[[Get]]` yet.
- **`WeakRef`** — `new WeakRef(target)` + `deref()`; `[[WeakRefTarget]]` stored
  strongly for now (true weak GC deferred).

| Suite | Prior → | Passed |
| --- | --- | --- |
| builtins-collections | 1074 / 1078 | **1078** / 1078 (manifest empty) |
| builtins-basics | 771 | **771** (no regression) |
| smoke | 174 | **174** (no regression) |

Manifest: `test262-semantic/manifests/builtins-collections.toml` (`expectations = []`).
Residue outside this suite: full TypedArray/ArrayBuffer/DataView, true weak GC,
`getOrInsert*`, Set composition methods.

### 2026-07-25 — Set composition methods (XPASS cluster)

Unlocked Set `union` / `intersection` / `difference` / `symmetricDifference` /
`isSubsetOf` / `isSupersetOf` / `isDisjointFrom` (ECMA-262 `GetSetRecord` +
size-aware `has` vs `keys` paths; results via `OrdinaryObjectCreate(%Set.prototype%)`,
no `@@species` / no `add`). Supporting: minimal `Array.prototype.indexOf` /
`includes` (set-like order/mutation helpers). Suite excludes for composition
dirs removed; manifest stays empty.

| Suite | Prior → | Passed |
| --- | --- | --- |
| builtins-collections | 1078 / 1078 | **1450** / 1450 (manifest empty, unexpected 0) |
| builtins-basics | 771 | **771** (no regression) |
| smoke | 174 | **174** (no regression) |

### 2026-07-25 — Map.groupBy + getOrInsert* (XPASS cluster)

Unlocked `Map.groupBy` (`GroupBy` + `~collection~` key coercion),
`Map`/`WeakMap` `getOrInsert` / `getOrInsertComputed` (upsert; callback may
mutate, then overwrite). Supporting: minimal `Array.from` (iterable path),
`String.prototype[@@iterator]` (code-point), for-of `let`/`const` per-iteration
envs. Suite excludes for `groupBy` / `getOrInsert*` removed; manifest stays empty.

| Suite | Prior → | Passed |
| --- | --- | --- |
| builtins-collections | 1450 / 1450 | **1620** / 1620 (manifest empty, unexpected 0) |
| builtins-basics | 771 | **771** (no regression) |
| smoke | 174 | **174** (no regression) |

Residue outside this suite: full TypedArray/ArrayBuffer/DataView, true weak GC.

**Manifest + rerun.** Residual failures are recorded as `xfail` (visible, not
weakened) in `test262-semantic/manifests/language-core.toml` (TCO).
`builtins-collections.toml` is empty (suite green). Rerun any suite
green-with-known-gaps:

```bash
cargo run -p test262-semantic --release -- \
  --suite-path test262-semantic/suites/operators.toml \
  --harness test262 --timeout-secs 5 \
  --manifest test262-semantic/manifests/language-core.toml --fail-on new
```

Swap the `--suite-path` for the other suite files (including `generators-async.toml`).

**Known-gap inventory** (dominant `xfail` categories; fixing the operation makes the
entry obsolete and the test starts passing):

- **async/generator functions — core implemented** (sync generators + async
  functions + async generators + `for await` over async *and* sync iterables via
  CreateAsyncFromSyncIterator; see the resumable-bodies design note). Array
  destructuring iterator-protocol (IteratorClose / elision / rest / fn-name) is
  **cleared**. Array-literal `...` spread and object-literal / computed-member
  yield/await positions are **cleared**. Remaining generator/async-adjacent gaps:
  early-SyntaxError / redeclaration (parser-binder), concurrent async-generator
  request queue, AFSI continuation thenable-unwrap / `return`/`throw`, exotic
  yield/await (template / call-arg spread / `switch`/`for-in`), ToString-on-objects.
  `with` + `@@unscopables` and class static blocks are **cleared**. Class
  NamedEvaluation in binding defaults is **cleared** for base classes;
  minimal `extends` + `super()` / `super.prop` is **cleared**; `#x in` private
  presence is **cleared** (get/set / `this.#x` still deferred).
- **wrapper-prototype method surface**. GetV/autoboxing + prototype `[[*Data]]`
  slots + `toExponential`/`toPrecision`/`split`/`Array.isArray`/`Array.toString` +
  `Object.prototype.valueOf` / `propertyIsEnumerable` / `isPrototypeOf` are in;
  residue:
  - `toPrecision/exponential.js` — **cleared** (exact `floor(log10)` + significand digits).
  - `Number.prototype.toString` radix `a-z` + poisoned-radix — **cleared**
    (`for (let)` per-iteration + radix via full `ToNumber`).
  - `wrapper-object (new Boolean/new Number)` — **cleared**.
  - `toExponential` suite — **cleared** (full `ToNumber` for fractionDigits +
    IEEE significand→decimal via `num-bigint`).
- **parser/binder early-error detection** (~43 ids: escaped `await`/`yield`
  IdentifierNames, optional-chain template-tail early-errors, duplicate
  `default`, etc.) — **out of the vm-js scope** (`parse-js`/`semantic-js`).
- **missing globals** — `Math` / `parseInt`/`parseFloat`/`isFinite` / `Number`
  statics / minimal `RegExp` (+`exec` stub) / **`Proxy`** (+`revocable`, `[[Set]]`)
  / **`Reflect.construct`** / harness `$262.createRealm` / **`Map`/`Set`** (core)
  / **`WeakMap`/`WeakSet`** (get/set/has/delete + iterable; strong entry storage)
  / `Symbol.for`/`keyFor` / minimal **TypedArray** (Int32/Uint32/BigInt64/BigUint64)
  / minimal **WeakRef** (`deref`; strong target) / **Set composition**
  (`union`/`intersection`/`difference`/`symmetricDifference`/
  `isSubsetOf`/`isSupersetOf`/`isDisjointFrom`) / **Map.groupBy** /
  **Map/WeakMap getOrInsert*** / minimal `Array.from` /
  `String.prototype[@@iterator]` / minimal
  `Array.prototype.indexOf`/`includes` are **implemented**. Residue: full
  RegExp engine, true weak GC edges,
  ArrayBuffer/DataView/full TypedArray exotic surface, rest of `Reflect.*`.
  `builtins-collections` is **green** (1620/1620).
- **`ToString` on objects** (13 ids) — residual generator/async named-binding /
  name-inference edges; core OrdinaryToPrimitive + `String()`/`join` path is in.
- **`IsConstructor` / constructor-ness of built-ins** — small residue.
- **`Function` constructor** — *core implemented*. Residue: separate
  FormalParameters/FunctionBody parse validation, `%GeneratorFunction%` /
  `%AsyncFunction%` as globals.
- **BigInt beyond 128 bits** — *resolved*.
- **Optional-chain short-circuit** — *resolved* (§13.3.9).
- **Un-triaged residual mismatches** (~58 ids) — kept `xfail` with assertion
  snippets; candidates for future triage.

## Known issues and directions

- **Lib compile break (2026-07-23) — resolved**: HEAD had five errors — three duplicate
  `Realm::id` methods (kept the documented `self.id` getter; removed a redundant clone
  and a mistaken `RealmId::from_raw(global_object.id())` variant) and three
  `exec.rs` sites still constructing `Completion::Throw(err: Value)` after the
  migration to `Throw(Thrown)`. Those now use the same `thrown_at_stmt(err)` stack
  capture as neighboring `VmError`→throw arms. Lib + integration tests are green.
- **`promise_capability_ops` NativeCall/checkpoint migration (2026-07-23) — resolved**:
  updated `then_handler` to the host+hooks `NativeCall` arity and stopped using `?` on
  `MicrotaskQueue::perform_microtask_checkpoint` (`Vec<VmError>`).
- **`webidl-vm-js` `Vm::call` host plumbing (2026-07-23) — resolved**: iterator call sites
  now use `call_without_host` (conversion context has `WebIdlHooks`, not `VmHost`).
- **`test262-semantic` `HarnessMode::Inline` (2026-07-23) — resolved**: smoke test mapped
  to `HarnessMode::None` (no external harness files prepended).
- **test262 baseline established (2026-07-23)** — see [test262 status](#test262-status)
  for per-suite numbers, the operator/relational fixes, and the manifest-tracked gaps.
  Ratcheting continues via `--fail-on new` against
  `test262-semantic/manifests/language-core.toml`.
- **Optional chaining + primitive autoboxing landed (2026-07-23)** — optional-chain
  short-circuit (§13.3.9) and `GetV` on primitive bases (§7.3.2/§13.3.3, no wrapper
  allocation) are implemented; see [test262 status](#test262-status). Net +122 passing
  cases; manifest trimmed 775 → 714. The next highest-value target is finishing the
  wrapper-prototype method surface + receiver coercion (bounded now that the mechanism
  exists) ([roadmap phase 5](../status/roadmap.md#5-product-programs)).
- **Call-time function re-parse eliminated (2026-07-23)** — previously
  `ecma_function_ast` re-parsed source snippets as top-level `(snippet)` under Ecma,
  which correctly rejected `new.target` in arrows that had been legal in their
  original enclosing function. Functions now retain the parsed `Node<Func>` from the
  originating program AST (see [Execution engine](#execution-engine)); the two
  `arrow_functions` `new.target` integration tests pass and `cargo test -p vm-js` is
  fully green. test262 suite floors unchanged (no manifest ids flipped).
- **Built-ins program landed (2026-07-23)** — missing globals (`Math`, `parseInt`/
  `parseFloat`/`isFinite`, `Number` statics), `Object.prototype.hasOwnProperty` +
  `Object.getOwnPropertyDescriptor`/`getOwnPropertyNames`, `String.fromCharCode`, BigInt
  bitwise/shift (`& | ^ << >>`), and catchable wrapper-`valueOf` receiver coercion. Net
  **+187 passing cases**; manifest trimmed 714 → 620. See
  [test262 status](#test262-status). Language-core “missing built-in prototype method”
  residuals are cleared (`Object.defineProperties` landed 2026-07-25). Broader built-ins
  surface (`length`/`name`/`prop-desc`, `@@toStringTag`) remains for the full built-ins
  corpus; `Function` constructor is landed (see program note).
- **Throw→catch GC window closed (2026-07-23)** — see [Heap and GC](#heap-and-gc);
  `eval_catch` roots the thrown value before `env_create`.
- **Switch generator/async CaseBlock scoping (2026-07-23, hardened 2026-07-24)** —
  Annex B.3.2 var-hoisting applies only to *ordinary* nested `function`
  declarations; generator / async / async-generator decls stay CaseBlock/
  block-lexical (`collect_annex_b_*` / `instantiate_annex_b_*` in `exec.rs`).
- **test262 async-flag executor wiring (2026-07-23)** — `doneprintHandle.js` +
  `print` + microtask checkpoint; see [test262 status](#test262-status).
- **`generators-async` suite baselined (2026-07-23)** — 732/1394 passed; 240 xfails
  manifested; see [test262 status](#test262-status).
- **`Function` constructor landed (2026-07-24)** — `CreateDynamicFunction` for
  `%Function%`; net +32 passing cases; 16/17 ladder ids unblocked; see
  [test262 status](#test262-status).
- Performance tiers (bytecode, ICs) are explicitly *later* — do not let them leak into
  the spec-shaped core prematurely.
