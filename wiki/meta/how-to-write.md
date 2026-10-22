# How to write this wiki

This page is the constitution for `wiki/**/*.md`. It governs how knowledge enters the
wiki, how pages are shaped, and how the wiki stays true as the code moves. Update this
page whenever the way we work on the wiki changes — it is itself subject to its own rules.

## What the wiki is

The wiki is the repository's **single knowledge base**: architecture, design rationale,
theory, workflows, status, and history in one coherent whole. Scattered docs (crate
READMEs, `docs/`, `notes/`, `AGENTS.md`) are being absorbed into it; the absorption
ledger in [sources.md](./sources.md) tracks what has been absorbed and what remains.

Two audiences, one text: humans catching up, and agents whose sessions start from zero.
For agents especially, an unwritten lesson is relearned by every future session; a
written one is inherited by all of them. When in doubt, write it down — here.

## Absorption discipline

When new knowledge arrives (a source doc, a finding, a decision, a postmortem), it is
**absorbed**, never grafted:

- **Do not graft.** Never tack new content onto a page as an appendix, a "misc" section,
  or a second page that overlaps an existing one. Find where the knowledge belongs in
  the existing structure and weave it in. If the structure has no right place, change
  the structure — deliberately, updating the index and cross-links.
- **Do not bulldoze.** Never replace existing content wholesale because new content
  covers the same ground. Merge them: keep every detail from both sides unless one is
  **directly superior** (more precise, more current, verified where the other was
  assumed). When you drop something, it either moves to the [graveyard](../graveyard.md)
  (if it has historical value) or is noted in the ledger (if it was simply wrong).
- **Preserve maximal detail.** Exact commands, flag semantics, schema fields, code
  citations, edge-case notes, and numbers survive absorption. Summarizing is allowed
  only on top of preserved detail, not instead of it.
- **One home per fact.** Every fact has exactly one owning page; other pages link to it
  with a one-or-two-sentence local consequence. Never a bare "see X", and never a full
  copy. If two pages both want to own a fact, that is a structure bug — fix the
  structure.

## Evergreen style

Write pages to stay true:

- Prefer statements about **invariants and design** ("IDs are content-addressed so
  insertion order cannot leak into outputs") over statements about the moment ("we
  currently have 129 test files").
- Volatile facts are quarantined in `status/` pages, which are **dated snapshots** and
  exempt from the evergreen rule. Everything under `status/` carries an "as of" date and
  is expected to be re-verified, not trusted.
- When an evergreen page must mention a volatile fact, date it inline ("as of 2026-07,
  …") and link to the status page that owns it.
- Never write "recently", "new", "now supports" without a date — those phrases rot
  silently.

## Rationale, background, and the graveyard

The wiki keeps **why** and **why not**, not only **what**:

- Every design page carries its rationale: the constraints that forced the design, the
  alternatives considered, and why they lost. A design without its why gets "fixed"
  back into a rejected alternative by someone who couldn't know better.
- Failed approaches, retired components, and completed one-off plans go to the
  [graveyard](../graveyard.md) with enough context that nobody retries them ignorantly —
  and enough honesty that someone *can* retry them if the constraints have changed.
- Record surprises where future work will walk past them: an API behaving unexpectedly,
  a discovered constraint, a diagnosed bug. The deadlock case study in
  [determinism](../architecture/determinism.md) is the model: symptom, stacks, root
  cause, fix directions, and the general rule it teaches.

## Page anatomy

Not a rigid template, but pages should generally answer, in order:

1. **What and why** — the component/topic's purpose and the bet it serves (link to
   [vision](../vision.md) when relevant).
2. **Design** — how it works, with real type/function/file names and code citations.
3. **Rationale** — why this way; alternatives rejected and why; links to graveyard.
4. **Operations** — how to run/use/test it (commands preserved exactly).
5. **Known issues and directions** — honest, linked to [status/health](../status/health.md)
   and [status/roadmap](../status/roadmap.md).

Style:

- Prose-first, complete sentences. Tables only for short enumerable facts (registries,
  flag lists). Fragments and arrow-chains don't survive contact with a reader who
  wasn't there.
- Cite code as `path/to/file.rs` (with line numbers only when durable — prefer symbol
  names, which survive edits better).
- Use fenced code blocks for commands and code; keep commands copy-pasteable.
- Headings are navigation, not decoration; if a section is one sentence, inline it.
- Relative links between wiki pages; check them when moving pages.

## The update loop (continuous absorption)

The wiki is maintained **as part of every work session**, not as a separate chore.
After any meaningful unit of work on the repo:

1. **Status**: update [health](../status/health.md) if build/test reality changed;
   update [roadmap](../status/roadmap.md) if an item completed, changed shape, or was
   discovered.
2. **Owning pages**: update the crate/architecture page whose subject changed. New
   invariants, new flags, changed semantics — same commit as the change ideally.
3. **Surprises**: record anything that surprised you at the page a future reader will
   consult before hitting the same surprise.
4. **Graveyard**: if an approach was abandoned or superseded, bury it properly.
5. **Ledger**: if you absorbed or invalidated an external source, update
   [sources.md](./sources.md).
6. **Meta**: if the *way* of working changed, update this page or
   [how-to-work.md](./how-to-work.md).

The forbidden state is **silent disagreement** between wiki and code. If code violates a
normative wiki page, the code is wrong — fix it or flag it. If implementation reveals
the wiki is wrong or incomplete, do not silently diverge — fix the page in the same
session.

## Relationship to in-repo docs during migration

Until migration completes (tracked in [roadmap](../status/roadmap.md)):

- `AGENTS.md` remains the harness-wired agent rules file and is externally load-bearing;
  its architectural content is absorbed here, and the two must not contradict. As of
  2026-07-24 it carries a Living docs table pointing at this wiki and conservatively
  defers ops/status/crate-depth duplication here — further slimming still needs owner
  sign-off ([roadmap](../status/roadmap.md#decisions-needing-an-owner)).
- `wiki/architecture/deps.md` is a **generated artifact** (by
  `scripts/gen_deps_graph.sh`, drift-checked by CI): never edit it by hand; regenerate.
  (The generator was repointed from `docs/deps.md` into the wiki on 2026-07-23;
  `docs/deps.md` is now a stub.)
- Crate READMEs are the public face on crates.io for publishable crates (`minify-js`,
  `parse-js`); they stay, but the wiki owns the deep content and READMEs should shrink
  toward summaries plus pointers.
- Everything else (`docs/*.md`, `notes/*.md`, `planner_scratchpad.md`) is absorbed and
  should eventually be reduced to a pointer or deleted; the ledger tracks each file's
  disposition. Do not update an absorbed source in place — update the wiki and, if the
  source still exists, keep it consistent or reduce it to a pointer.

## Provenance

When a page absorbs an external or pre-existing text, note it briefly at the point of
absorption ("absorbed from `notes/Parentheses.md`, 2026-07") or in the ledger. This is
cheap insurance: it lets a future maintainer trace a claim to its origin when it stops
matching reality.
