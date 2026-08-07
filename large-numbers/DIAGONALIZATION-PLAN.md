# Scoping the diagonalization construction: staged plan

Follow-up to `RAYO-EXPLAINER.md`'s "does the growth rate speed up
eventually?" section. That section identified the real Rayo(n)-maximizing
strategy as a Berry-paradox-style self-reference construction over a
Tarskian satisfaction predicate, categorically different from the
enumerate-predecessors strategy `rayo-lean/` already mechanized for k=0-6.
This plan scopes whether and how to attempt formalizing *that* construction.

**Honest framing up front, unlike the last two runs:** k=0-6 carried low
risk — I was confident something would land even before running it, only
uncertain how far. This does not have that property. The hardest stage
(Stage 2) is genuinely uncertain to close in any bounded budget, even for
domain experts without a clear existing playbook. This plan is staged with
real go/no-go gates specifically so that uncertainty gets discovered cheaply,
early, rather than paid for at the end of an expensive run.

## Stage 0 — Audit prior art (parallel, cheap, do first)

Three independent questions, genuinely parallelizable since none depends on
the others' answers:

1. **What does Lean's Mathlib `Mathlib.ModelTheory` namespace already
   provide?** Specifically: a `Realize`/satisfaction relation for arbitrary
   first-order languages; anything toward Gödel-coding formulas as terms;
   anything toward definability or diagonal/fixed-point lemmas. If
   substantial machinery already exists, Stage 1-2's effort drops a lot —
   this is the single highest-leverage question to answer first.
2. **Has anyone published a Lean (or Coq/Isabelle, for porting-feasibility)
   formalization of Gödel's diagonal lemma / fixed-point theorem, or of
   Gödel's first incompleteness theorem?** If so: what approach did they
   take, how long did it take, and is any of it structurally reusable for a
   set-theoretic (not just arithmetic) satisfaction predicate?
3. **Has anyone attempted to formalize or rigorously verify Rayo's function's
   own construction, Berry's paradox resolutions, or a comparable
   self-referential large-number construction, in any proof assistant?**
   Direct prior art for the actual target, as opposed to the general
   diagonal-lemma machinery in (2).

Recorded as findings (sourced, with an explicit "searched, found nothing
citable" where that's the honest answer — same discipline as
`rayo-notes/literature-notes.md`). No code written at this stage.

**Go/no-go gate.** Proceed to Stage 1 regardless of what Stage 0 finds — a
negative result (nothing reusable exists) is itself useful and doesn't
block attempting it from scratch. What Stage 0's answer changes is *how*
Stage 1-2 are scoped: reusing existing Mathlib machinery where it exists,
building from scratch where it doesn't, and calibrating Stage 2's resource
caps against how long comparable prior efforts (incompleteness
formalizations) are known to have taken.

## Stage 1 — Encode formulas as sets (build, bounded, low risk)

Extend `rayo-lean/Rayo/Syntax.lean` and `Satisfaction.lean` so a `Formula`
can be represented *as a hereditarily-finite-set object* (a genuine Gödel
coding into the same HF universe the k=0-6 proofs already use), with a
proven-correct encode/decode correspondence. This is the same kind of task
as K0-K6 — well-defined, mechanically checkable, sized appropriately for a
normal bounded plimsoll run (toolchain already exists, so no ~40-minute
bootstrap cost this time).

**Go/no-go gate.** This stage should close. If it doesn't within a
generous but real cap (to be set when scoping the actual run), that is
itself informative — it would mean even the "easy" prerequisite is harder
than expected, and Stage 2 should not be attempted yet.

## Stage 2 — An internally-expressible satisfaction predicate (the hard part)

Build a predicate `Sat` that is *itself expressible as a formula in the
object language*, not merely a Lean meta-level function — i.e., formalize
enough of Tarski's semantic theory of truth, for formulas up to a bounded
complexity, to support the diagonal step in Stage 3. This is the step
Tarski's undefinability theorem restricts in general; the escape route (each
formula's truth is fixed by ordinary set-theoretic recursion on its own
structure, not by one uniform predicate ranging over unboundedly complex
formulas) has to be gotten right formally, not just gestured at.

**Explicit resource cap, matching the discipline from the last run's hard-
bounds section:** a stated wall-clock and attempt-count cap, agreed before
the run starts. If it doesn't close within the cap: stop, record exactly
what was tried and where it got stuck, as a finding — not a failure to
hide, and not something to push through by relaxing the cap mid-run.

**Go/no-go gate.** Stage 3 does not run without a working Stage 2 artifact.

## Stage 3 — The diagonal lemma, applied to one concrete tiny target

Only attempted if Stage 2 succeeds. Formalize that the self-referential
construction is well-founded (not an actual instance of the Berry paradox),
then apply it to name one small, concrete target as a proof of concept —
not an attempt to reach any particular impressive number, just to show the
mechanism works end to end.

## Where parallelism actually fits

Stage 0 is the only stage that's naturally parallel across independent
sub-questions — three unrelated research questions, no shared state, ideal
for concurrent agents (including cloud-isolated ones) right now. Stages 1-3
are inherently sequential (each gates the next) and are better suited to a
single disciplined plimsoll run with its own receipt/verify loop, the same
model as `rayo-lean/`'s K0-K6 work, rather than fanning out further agents
against shared, half-finished formalization state.
