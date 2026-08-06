Goal (frozen): for R = first-order set theory over the single relation
symbol `in` (the Rayo's-function family, `BN-function.md` Section 7's last
row, `KAPPA-TABLE.md`'s Rayo row currently marked infeasible-to-pin-exactly),
answer three linked questions with actual mechanically-verified numbers
rather than estimates:

  (1) how many symbols does kappa(R) cost — a concrete number for "the
      rules" (the FOL grammar plus the satisfaction/evaluation machinery),
      refining or confirming KAPPA-TABLE.md's existing lower bound;
  (2) for the smallest naturals k = 0, 1, 2, ... in order, how many symbols
      does the cheapest known formula phi_k(x) that uniquely names k cost,
      under one fixed, explicitly stated counting convention;
  (3) what is the largest such k actually reached, and what is its formula.

(1) and (2) are then to be aggregated into one combined-cost table: for each
k reached, total cost = kappa(R) + (symbols to name k). This is the same
kappa(R)-plus-n framing `BN-function.md` already uses everywhere else; this
run's job is to make it concrete for the one row Phase 2 could not pin down.

Mode: open. Whether this reaches k=0, k=3, or k=15 is not knowable in
advance — report the true stopping point honestly, per the bounds below,
rather than treating a stall as a problem to hide.

Background already committed in this directory: `BN-function.md` (BN(R,n),
kappa(R) concept, admissibility A1-A5), `METHODOLOGY.md` Section 2.5 and C4
(the existing Rayo counting convention: FOL-over-`in` parser + Tarskian
satisfaction clauses + unique-denotation readout counts toward kappa; axiom
schemas count as finite templates), `KAPPA-TABLE.md`'s Rayo row (current
verdict: infeasible to pin exactly, lower-bounded by "at least several
hundred BLC bits"), and `PRIOR-FINDINGS.md` (a copy of the prior run's
FINDINGS.md, renamed on purpose: this run's own FINDINGS.md is a fresh,
harness-owned document for *this* run's findings only — it does not carry
the prior run's content over, so `PRIOR-FINDINGS.md` is where that context
lives). Read all of these before doing anything else; do not re-derive what
they already establish. This run extends that Rayo row — it does not redo
Phases 0-4 of `PLIMSOLL-PROMPT.md`.

`FINDINGS.md` is rendered by the harness from recorded findings; no item may
write it, assemble it, or declare it in `scope`/`assembles`. Every "record
as a finding" instruction below means: use the harness's own finding
mechanism for that item, not a hand-written edit to that file.

## Hard bounds — read this before writing any item that searches or proves

Every item below that involves a proof search or a toolchain install carries
an explicit resource cap. These are not suggestions: an item that would
exceed its cap must stop, record what it tried and why it stopped as a
finding (ruled-out-for-now, not failed), and the run must not silently
retry past the cap or invent a workaround that spends more budget than the
cap allows.

- **Toolchain setup, one attempt, ~40 minutes wall-clock total.** Try the
  lighter option first: a small, self-contained Lean 4 formalization (no
  external library) of first-order formula syntax over `{in, =, not, and,
  exists, forall}` plus a satisfaction relation over a Lean-native model of
  hereditarily finite sets built for this purpose. This requires its own
  flagged methodological choice (recorded as a finding, in the same spirit
  as `METHODOLOGY.md`'s C1-C7): satisfaction over this hereditarily-finite
  model must be argued to coincide with satisfaction over the true universe
  V for the specific bounded/absolute formulas this run constructs, and that
  argument must be stated, not assumed. If that route stalls, fall back to
  Lean 4 + Mathlib's `ZFSet` (`Mathlib.SetTheory.ZFC.Basic`), which gives
  real ZFC semantics at the cost of a heavier install (`elan`, then `lake
  exe cache get` rather than a from-scratch build, to avoid compiling
  Mathlib). If neither produces a working `lean`/`lake` environment that can
  typecheck a trivial test proof within the 40-minute budget, stop here.
  Record which route was tried, how far it got, and why it stopped, as a
  finding. This is a legitimate, reportable outcome — "mechanized
  verification was not tractable in this sandbox in this budget" answers
  the question it was asked, it does not fail to answer it.

- **Per-k proof-search budget, ~25 minutes wall-clock or ~15 distinct
  tactic-strategy attempts, whichever binds first.** For each candidate
  formula phi_k(x), that is the total budget for proving "phi_k has exactly
  one solution and it is k" in Lean. Track both the elapsed time and the
  count of genuinely distinct strategies tried (not re-running the same
  tactic block with cosmetic changes) and stop at whichever limit is hit
  first.

- **On any single k hitting its budget: stop extending the table
  immediately.** Do not attempt k+1 "in case it is easier" — record k as
  blocked with the formula attempted and what the proof search tried, and
  the table's final answer is the largest k *before* the one that stalled.
  A gap-filled or reordered table would misrepresent what was actually
  established.

- **Whole-run hard stop: 3 hours of wall-clock from the first item.** This
  is a hard instruction to the agent, not merely the `--ceiling-unit hours`
  flag passed at the CLI (that flag only alerts at multiples, per SPEC.md
  §5 — it does not stop the run by itself). If 3 hours elapse with items
  still in progress, stop wherever the table currently stands and record
  that as the reason for stopping, distinct from a per-k proof failure.

## Phase A (inquiry + build): fix the convention, confirm feasibility

(a) Fix the symbol-counting convention for formulas naming a natural via
    first-order set theory: the alphabet (recommend the minimal primitive
    set `{in, =, not, and, exists, forall, (, )}` plus variables, with `or`,
    `implies`, `iff`, `unique-exists` all counted as their expansions rather
    than as free primitives — state whether this recommendation is adopted
    or a different convention is, and why), the natural-number encoding
    (von Neumann: 0 = empty set, k+1 = k union {k}), and whether each
    variable occurrence counts as one symbol regardless of which variable
    (the usual convention, since variables are freely renameable). Record
    as a finding. This is a genuinely arbitrary choice, like `METHODOLOGY.md`
    C1/C3 — flag it as such rather than presenting it as forced.

(b) Before assuming Lean-mechanized verification is the right approach at
    all here, spend up to 20 minutes of the toolchain budget searching for
    prior published work on minimal-formula-length results for small
    naturals in first-order set theory (the 2013 "Big Number Duel," Rayo
    vs. Adam Elga, MIT, and any retrospective analysis of it, is the most
    likely lead — search for it specifically). If real sourced numbers
    already exist, record them as a finding with citation and treat them as
    a cross-check target for Phase C rather than reinventing the search from
    nothing. If nothing solid turns up, record that as a finding too — an
    honest "searched, found nothing citable" is itself useful.

(c) Toolchain setup and feasibility spike, under the 40-minute cap above:
    get a working Lean environment, then attempt ONE proof — that
    `forall y, not (y in x)` has exactly one solution x, and that x is the
    empty set (k=0) — as the go/no-go gate for everything downstream. If
    this succeeds, proceed to Phase B/C. If it does not close within the
    cap, record why (toolchain didn't build in time / the claim itself
    didn't close in time / the formalization doesn't actually support
    expressing "exactly one solution" the way this needs) and stop the run
    there — Phase B/C do not run without a working feasibility spike.

## Phase B (inquiry): refine kappa(R) using the real artifact from Phase A

If Phase A's feasibility spike succeeded, measure the actual size of the
Lean formalization actually used (the formula-syntax datatype, the
satisfaction relation, and — if the hereditarily-finite route was taken —
the finite-set model and its coincides-with-V argument): a token or line
count in Lean's own units. Report this as a real measured artifact
alongside `KAPPA-TABLE.md`'s existing BLC-bit lower bound for the same row,
explicitly flagging that Lean tokens and BLC bits are different units under
different conventions (per `BN-function.md` Section 6's invariance-up-to-a-
constant point) — do not invent a false conversion between them. Record as
a finding; do not edit `KAPPA-TABLE.md`'s existing BLC-bit row in place,
since that row's convention is fixed for comparability with the other five
systems — add this as new, separately-labeled information instead.

## Phase C (build, incremental, one item per k): the small-n table

Starting at k=0 (already handled by Phase A's feasibility spike — record it
as k=0's table row directly, do not re-prove it), for k=1, 2, 3, ... in
strict order: construct phi_k(x) (build on the structure of phi_{k-1}
where that helps — e.g. "x's elements are exactly the sets satisfying
phi_{k-1}" is a natural recursive step for the von Neumann encoding, but
verify this pattern actually produces a correct, provable formula rather
than assuming it), count its symbols under Phase A's fixed convention, and
attempt to prove in Lean that it has exactly one solution, equal to k,
under the per-k budget above. On success: record (k, formula, symbol count,
reference to the Lean proof) as a finding and move to k+1. On failure: stop
per the hard-bounds section — do not continue to k+1.

Cross-check against Phase A(b)'s sourced figures if any were found, and
record agreement or disagreement explicitly rather than silently.

## Phase D (inquiry): the aggregated answer

Once Phase C stops (by success-exhaustion is not expected; by budget is the
normal case), write the combined table: for each k reached, kappa(R)
[Phase A/B's figure, in its stated unit] + n_k [Phase C's per-k symbol
count] = total cost, alongside the growth-rate context already established
(uncomputable; dominates every function whose totality first-order set
theory can prove, per `BN-function.md` Section 7). State plainly: the
largest k reached, why the run stopped there (budget vs. genuine proof
difficulty vs. toolchain limits), and that this says nothing about Rayo's
actual number (which uses a googol-symbol budget) beyond confirming the
same qualitative point Phase 4 of the original run found for the
Turing-complete rows — that bootstrapping is expensive relative to a tiny
budget and only stops mattering once the budget is large.

## Explicitly out of scope

- Anything about Rayo's actual number at googol-scale — this run is about
  the smallest naturals only.
- Skipping ahead past a stalled k "to see how far the pattern could go
  anyway" — a stalled k is the honest stopping point, not a data point to
  route around.
- Silently falling back from a Lean-mechanized proof to an unverified
  hand-argument for any k reported as "proved" — if the cap is hit, that k
  is blocked, not downgraded-and-kept.
- Treating Phase A(b)'s literature search as exhaustive if it finds
  nothing — record absence of a citable source as absence, not as proof
  none exists.
