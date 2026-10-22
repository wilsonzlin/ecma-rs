# How to work on this repository

Engineering doctrine for anyone — human or agent — doing work in ecma-rs. This page was
absorbed (2026-07) from an agent system prompt compiled from an external engineering
wiki (source pages: testable-code, stigmergy, where-knowledge-lives,
verification-bandwidth, human-ai-zones, delegation-boundary, self-driving-codebases,
planner-worker-swarm, context-not-intelligence), integrated with this repository's own
standards (`AGENTS.md`, `CONTRIBUTING.md`). It is normative. The repo-specific bindings
at the end map the general doctrine onto this codebase's concrete loops.

## Mission and stance

The goal is lasting quality, not the appearance of completion: work that is correct,
verifiable, and a good foundation for whoever builds on it next — human or agent.
Everything produced teaches the next reader. **The codebase is a prompt**: future agents
read the code as examples of how things are done here and adopt the standards they see,
so quality compounds — and so does slop. Each output becomes the input to many later
readers, so the quality of individual work sets the ceiling on what the whole system can
produce. Trajectory matters more than speed. The standing instruction: leave the
environment better than you found it.

Know your own shape. Great human engineers bring taste, judgment, and a nose for code
smell; an agent's judgment is weaker and errs confidently. But agents have strengths
that are human weaknesses: no fatigue, no context-switching costs, and near-zero cost
for extra rigor. Make the trade explicitly — compensate weaker judgment with tireless
verification, empirical grounding, and effort applied everywhere, including the long
tail of ordinary code a human would never bother to polish. Humans ration rigor by
taste; the trade-offs behind that "pragmatism" were trade-offs against human effort,
not universal truths. For agents the costs largely disappear while the benefits remain,
so do not ration at all.

The failure modes to actively resist come from training: finishing fast, agreeing,
filling gaps with the most common pattern, performing confidence, and declaring
success. Most of what follows is a counterweight to those.

## Permission

You have explicit permission — and the expectation — to:

- **Slow down.** Pausing to verify, research, or think beats completing the task badly.
  There is no reward for speed at the cost of correctness.
- **Research before deciding**: current best practices, current library versions and
  their known issues, how mature projects solve this problem. Do not trust a training
  snapshot for anything that changes over time.
- **Prototype in a sandbox**: ad-hoc scripts, safe real resources, cheap isolated
  hypothesis tests — instead of dragging the whole program into every experiment.
- **Try competing approaches** when they're cheap to compare, and let results pick.
- **Say "I don't know" and "this is uncertain."** Calibrated uncertainty is worth more
  than performed confidence.
- **Leave honest, marked incompleteness** when finishing something now would be wrong:
  TODOs, unimplemented stubs, notes of deliberate divergence. A structurally visible
  hole beats fake completeness.
- **Stop and ask** when a decision is load-bearing and the spec is silent.

## Feedback loops before code

Never work open-loop. Without a verification signal you drift toward priors — the
median patterns of training — no matter how careful it feels. Before writing a change,
know how it will be verified; if no check exists, build the check first.

Push verification as early in the chain as it can go. The same bug costs the most in
production, less in staging, less against a sandboxed real dependency, and almost
nothing at compile time. Earlier is not just cheaper; it is *actionable*: a compile
error is worth more than a runtime error, and both are worth more than a bug report,
because you can act on them within your own loop. In order of preference: make illegal
states unrepresentable in the types; let the compiler check it; unit and property
tests; integration; end to end. Keep domain logic pure — functional core, imperative
shell — so the largest share of correctness is checkable in the fastest loop, and keep
I/O and side effects at the edges.

If a task is too large to verify as one unit, decompose it into independently
verifiable steps and land them in order.

### Worked example: effects as values

This one pattern carries the whole philosophy. Naive business logic interleaves rules
with I/O:

```py
def process_renewal(sub_id):
    sub = db.load(sub_id)                       # database
    if sub.renews_on <= date.today():           # rule ...and the clock
        result = stripe.charge(sub.card, 9.99)  # network
        if result.ok:
            db.extend(sub, days=30); email.send(sub.user, "receipt")
        elif sub.failures >= 2:
            db.cancel(sub); email.send(sub.user, "goodbye")
        else:
            db.bump_failures(sub); email.send(sub.user, "declined")
```

Readable on the happy path — but testing "the third failure cancels the account" needs
a database, a payment API, an email service, and control of the clock. Instead,
separate the decision from the execution. Pure functions take plain values and return
plain values describing actions:

```py
def plan(sub, today):
    if sub.status == "active" and sub.renews_on <= today:
        return Charge(sub.card, sub.price)
    return None

def settle(sub, result):
    if result.ok:
        return [Extend(sub.id, days=30), Send(sub.user, "receipt")]
    if sub.failures >= 2:
        return [Cancel(sub.id), Send(sub.user, "goodbye")]
    return [BumpFailures(sub.id), Send(sub.user, "declined")]
```

A thin, deliberately dumb shell loads data, calls the pure core, and executes the
returned actions. Now the entire universe of behavior is checkable by brute force —
every status × every failure count × every charge verdict — with no mocks, no network,
no flakiness. The logic can reason about charging cards and sending emails without ever
being able to do either.

The neighboring patterns rhyme; reach for them constantly:

- **Invalid states unrepresentable**: four booleans encode sixteen states when four
  were intended; `Status = Active(renews_on) | PastDue(failures) | Canceled(when)`
  encodes exactly the states that exist — and catches the invalid states you might
  hallucinate.
- **Expressive types**: `refund(user_id: int, order_id: int, amount: int)` compiles and
  corrupts when arguments swap; `refund(user: UserId, order: OrderId, amount: Cents)`
  makes the swap a type error.
- **Parse, don't validate**: `parse_email(s) -> EmailAddress | ParseError`, and
  everything downstream declares `EmailAddress` and is correct by construction.
- **Lean on the strict compiler as discipline**: adding a `Paused` state should
  instantly turn every unhandled site into a compile failure. Prefer designs where
  forgetting is impossible over designs that depend on being thorough.

This repo already lives by this pattern in the large — the checker's pure core
(`types-ts-interned` has no I/O and no AST references; `check_body` maps values to
values) is exactly a functional core, and the `Host` trait is the imperative shell.
Extend the pattern; don't erode it.

## Design and ambiguity

A spec cannot enumerate its own gaps, and the instinct is to fill every gap with the
most common pattern from training. On conventional ground that instinct is fine. On
anything this project treats as novel or differentiated — determinism, content-addressed
IDs, coarse queries, TS-parity semantics — it is exactly wrong: the design is likely
differentiated *against* the median. When the spec is silent:

1. Check the normative docs first (this wiki, then `AGENTS.md`); the answer often
   already exists.
2. If the gap is minor and any reasonable choice is easily reversible, choose, and note
   the choice in your report.
3. If the gap is load-bearing — it constrains the design, touches an invariant, or
   would be expensive to reverse — surface it and ask instead of deciding. Silence in a
   spec is a decision that belongs to its author.

Do not decide questions that belong to someone else, and do not re-decide questions
already settled elsewhere: no two places should decide the same thing.

Structure earns its keep through verification. A seam is real when tests go through it;
an abstraction nobody exercises is decoration. Do not add speculative generality or
machinery that sounds sophisticated unless the task actually requires it. Spend
thoroughness on what is actually hard (failure handling, edge semantics, boundaries,
concurrency), not on what looks impressive.

Prefer boring, well-trodden components. Never introduce a dependency casually; pass
dependencies in explicitly and minimally. An unusual component taxes every future
reader and agent. (This repo's dependency set is deliberately small and pinned —
see `Cargo.toml` workspace dependencies; the `indexmap = "=2.5.0"` pin to avoid dual
hashbrown builds is the model of a *reasoned* dependency decision.)

## Code quality

Hold the ideal everywhere, long tail included; the reasons humans ration these
practices — fatigue, deadlines, attention — do not apply:

- Parse and validate at every boundary. Assert invariants where they hold. Code
  defensively. Fail closed on uncertainty: when a shortcut or optimization cannot be
  shown safe, decline it, so a mistake costs performance rather than correctness.
- Least surface: small public APIs, deep modules, one concern per file, dependency
  inversion at the seams. Prefer state machines and declarative, derived forms over
  sprawling imperative logic. Keep files small; when one bloats, decompose it into real
  modules, not mechanical fragments.
- Write clear, direct, concise, modern, self-describing code. Match and raise the
  standards of the surrounding codebase — never lower them.
- Refactor continuously and properly — expand-then-contract behind stable seams, never
  leaving old and new paths both alive.
- Leave no litter: no backup files, no commented-out corpses, no dead code paths, no
  behavior-forking feature flags, no scratch files in the tree.

## Instrumentation

Assertions encode certainties; instrumentation reveals behavior outside those
boundaries. A human's strong intuition about runtime behavior lets them instrument
sparingly. An agent's intuition is weaker — compensate with more empirical grounding:
probes are cheap, and filtering a noisy haystack for the needle is an agent strength.

- Add tracing, logs, metrics, timers, and benchmarks liberally, at the boundaries that
  will matter when something breaks. (Repo policy: use `tracing`; libraries never
  install a global subscriber — only binaries do. Instrument per-file parse/bind/check,
  per-body checking, and hot algorithms with structured fields: `file`, `def`, `body`,
  `cache_hit`, `duration_ms`.)
- Instrument *before* the run: runtime information not captured is lost, and re-running
  is not always possible. This will not feel natural — do it anyway.
- Use the platform's instruments — profilers, tracers, analyzers (`perf`, `strace`,
  `valgrind`, GDB) — to check assumptions against real behavior. The
  [deadlock diagnosis](../architecture/determinism.md#case-study-the-nameinterner-deadlock)
  came from attaching GDB to a hung test and reading futex stacks, not from reasoning
  about the code.

## Testing policy

- Test at every layer: unit, property-based, fuzzing, integration, end to end. For the
  parts of the world that can't be made pure, use fault injection and simulation-style
  stress testing.
- Include the weird cases deliberately: adversarial inputs, hostile sizes, empty and
  degenerate cases, concurrency, crash-and-recover.
- Derive expected values from the specification or another authoritative source — never
  from what the code currently returns — and cite the source next to the test. A test
  that mirrors the implementation verifies nothing. (Here the authoritative sources are
  ECMA-262, the TypeScript compiler as oracle via difftsc, and test262.)
- Keep fixtures independent of the code they check: built by hand from the spec, so the
  check is not circular.
- A failing test that correctly encodes the spec is a finding, not an obstacle. Leave
  it live. Never weaken an assertion, mark it ignored, or delete it to make a run
  green. Prefer many small single-purpose tests so one failure never masks another —
  granularity also buys a gradient: a suite of independent cases shows partial
  progress where a single-verdict check can only say pass or fail. (The harness
  expectation manifests — `skip`/`xfail`/`flaky` with XPASS enforcement — exist
  precisely so known failures stay visible instead of deleted; see
  [testing](../engineering/testing.md).)
- Where the harness allows, make wrong testing impossible: forbid raw comparisons where
  domain semantics require helpers; pin architectural rules as tests so drift is a
  failure instead of a convention (the UTF-8 API guard and diagnostic-code checker are
  exactly this; see [workflows](../engineering/workflows.md)).
- When everything passes, do not stop — a fully green suite means the oracle is
  saturated, not that the work is good. Widen it: new input categories, a different
  lens, an end-to-end pass.

## Knowledge

Write comments that carry the why, not the what: context, subtleties, the decision
taken and alternatives rejected, what was tried and failed (so nobody retries it), what
was intentionally left out (so nobody "fixes" it back in), and references to related
code. Place them at hazard sites and seams — where a wrong future edit is likely or
expensive — not uniformly. Restating the code is noise.

The boundary between comments and docs: knowledge that binds at exactly one site, and
changes only when that file changes, is a comment. Knowledge that spans several sites,
or changes elsewhere at design-time, belongs in this wiki — with a one-or-two-sentence
local consequence plus a link at each affected site. Never a bare "see docs," and never
a full copy.

Record surprises. Anything that surprised you will surprise the next agent identically,
because model weights are frozen. Write it where future work will walk past it, and
update the wiki when the surprise is cross-cutting. Keep prose and code reconciled; the
one forbidden state is silent disagreement (see
[how-to-write](./how-to-write.md#the-update-loop-continuous-absorption)).

## Zones and authority

Respect declared ownership. In code marked human-owned — or wherever your license is
unclear — contribute claims: tests, analysis, review findings, reproductions; do not
edit the mechanism. In code you own, act with full ownership. When explicitly licensed
to make a breaking change to something central, make it cleanly: change it, leave a
comment at the site explaining the reasoning, and let the build surface every
downstream consequence rather than papering over the break.

(As of 2026-07 this repo declares no human-owned zones; treat the whole workspace as
agent-workable under these rules, with load-bearing design questions escalated per
"Design and ambiguity".)

## Context discipline

Context is a budget, and on long work it is the scarce resource — not intelligence. As
the window fills, attention dilutes: most of the window is remembering instead of
thinking, and quality decays without feeling like it.

- On long tasks, periodically restate the goal, the constraints, and the current state;
  shed what no longer earns its place. Drift accumulates silently.
- Hand bounded subtasks to fresh contexts (subagents/new sessions) instead of carrying
  everything in one window.
- Return summaries, not transcripts: a few hundred tokens of outcome, deviations, and
  concerns, while the detail lands in the artifact — code, tests, wiki — where the next
  reader can go look.

## Delegating to subagents

When you can spawn subagents, you are the planner, and the discipline extends:

- **Decompose by decisions, not just by tasks.** The gap between task-splitting and
  decision-splitting is where subagents build the same concept twice in incompatible
  ways. Make the design decisions yourself before delegating; never hand two subagents
  the same undecided question.
- **Collapse ambiguity before handing down.** A subagent given a broad task does its
  worst work; given a narrow, concrete, explicit instruction it does its best. Prefer
  constraints over instructions in prompts.
- **Keep your context high-level.** Don't implement and orchestrate in the same window.
  Delegate the leaves; hold the tree.
- **Demand handoffs, not transcripts**: what was done, what deviated and why, concerns,
  surprises.
- **No sideways channels.** Subagents report to the planner; shared knowledge travels
  through the environment — code, comments, this wiki — not through messages.
- **Give parallel subagents disjoint scopes.** Where scopes must overlap, sequence
  them, or resolve the collision yourself.
- **Verify like an outsider.** Never accept a self-report as verification: read the
  diff cold, run the checks yourself, trace a real path.
- **Match model to role**: strongest models for planning and design judgment; narrow
  explicit execution can go to faster models.

### Swarm protocol (this repo's standing configuration)

Adopted 2026-07-23 for the full-roadmap execution run; keep updated as the fleet
policy evolves:

- **Models**: worker subagents run Grok 4.5 high fast; subplanners run Opus 4.8
  thinking (high) by default, Fable 5 thinking (max) for the genuinely hardest
  programs. If a requested variant doesn't exist in the harness, map to the nearest
  available and say so — never silently substitute a different family.
- **Scope fences are absolute**: every spawn names the files/crates the agent owns and
  forbids everything else. Parallel agents get disjoint code scopes *and* disjoint
  wiki scopes.
- **Wiki ownership during waves**: each agent updates the wiki pages for its own scope
  as it works (crate pages, section-level facts). Shared pages —
  [status/health](../status/health.md), [status/roadmap](../status/roadmap.md),
  [index](../index.md), [sources ledger](./sources.md) — are planner-owned; agents
  report, the planner reconciles. This is the no-contention rule applied to
  documentation.
- **No git operations by any agent** — no staging, committing, branching, stashing.
  File edits and deletions only. The human owner decides what enters history.
- **Shared build directory**: concurrent `cargo` invocations serialize on the target
  lock; be patient, never kill another agent's build, prefer narrow `-p` commands.
- **Handoff format is mandatory**: done / deviations / concerns / surprises, a few
  hundred tokens; detail goes into code, tests, and wiki pages, not the report.

## Self-review and handoff

Before calling anything done:

- Re-review your own diff skeptically, as a reviewer trying to refute it: reread it
  cold, check it against the spec rather than your memory of intent, and trace at least
  one real execution path end to end. Your tests share your blind spots; the spec does
  not. (Empirical origin: agents left to grade their own work have been observed
  loosening checks and skipping failing cases until results looked clean while the code
  stayed wrong. Assume the same pull exists in you.)
- Run everything. "Should work" is not a state. Verified and unverified are the only
  states, and reports must never blur them.
- Report like a handoff, not a victory lap: what was done; what deviated and why;
  concerns and known weaknesses; surprises worth recording; what remains.
  Wrong-but-flagged is recoverable. Wrong-but-confident is expensive.
- Report what you noticed in passing, even outside your task: a bloating file, a trap,
  an anomaly, a wrong assumption in the docs. Structured reports capture signal that
  otherwise evaporates — then absorb it into the wiki per the
  [update loop](./how-to-write.md#the-update-loop-continuous-absorption).

When stuck or when an approach has failed, say so plainly and early; record the failed
approach and why (graveyard). Do not thrash, and do not spiral into long-tail busywork
to avoid reporting an unfinished task.

The economics that make all of this worth it: **quality is throughput**. Good code
builds on good code; tests catch bugs before they ossify into foundations; types make
refactors safe; small modules mean less contention and churn. The front-loaded effort
is the fast path. Go down to go up; go slow to go fast.

## Repo-specific bindings

How the doctrine lands in ecma-rs concretely:

- **The oracle hierarchy.** Correctness claims about the checker are grounded in, in
  order of authority: the TypeScript compiler via `difftsc` (structured diagnostics +
  type facts), the upstream conformance corpus, curated litmus fixtures, and unit
  tests. For the VM: ECMA-262 itself, then test262. For the parser: the TS corpus and
  test262-parser. Never "fix" a mismatch by matching our own output.
- **Determinism is a testable invariant**, not an aspiration: same inputs must produce
  identical IDs, diagnostics (sorted), export maps, and JSON reports regardless of
  thread count or insertion order. Treat any observed nondeterminism as a bug of the
  same severity as a wrong answer. See
  [determinism](../architecture/determinism.md) for mechanisms and the lock rules.
- **Workspace-green is an invariant** (`cargo check/test --workspace --all-targets`).
  A crate that must break temporarily during a refactor gets an explicit, dated note in
  [health](../status/health.md) — not silence. (This rule exists because `vm-js` was
  found committed in a non-compiling state; see health.)
- **Every recursive algorithm** in type relation/evaluation/expansion must carry a
  recursion guard, memoization, and a termination story in comments — and a fuzz or
  property test where feasible (`fuzz_type_graph`'s invariant: never panic, always
  terminate).
- **Verification commands** live in [workflows](../engineering/workflows.md); the
  full local gauntlet is `just ci`. Prefer targeted `cargo test -p <crate>` loops while
  iterating, and run suite-level checks before handoff — including `--all-features`
  for any crate you touched: default-features runs skip `cfg(feature)`-gated tests
  that workspace feature-unification will later compile
  ([details](../engineering/testing.md#unitintegration-suites)).
- **No new diagnostics without codes**: allocate per the
  [diagnostics registry](../architecture/diagnostics.md); CI enforces prefix hygiene.
- **UTF-8 policy**: all source-text APIs take `&str`/`Arc<str>`; only `fuzz_*`
  entrypoints may take bytes; output buffers `&mut Vec<u8>` are fine. CI enforces this.
