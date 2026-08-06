# Plan: mapping specification cost against reachable growth for BN(R, n)

Goal (frozen): for the reference systems $R$ already identified in
`BN-function.md` (Busy Beaver's Turing machines, BLC, single/multi-row BMS,
Loader's-number-style type theories, Rayo's first-order set theory), build
an actual table of $(\kappa(R), \text{growth rate of } BN(R,\cdot))$ pairs,
grounded in real leaderboard/proof data rather than restated folklore, and
use it to say something concrete about whether growth rate scales cheaply
or expensively with specification cost. This table does not currently
exist anywhere (checked: bbchallenge.org and the Code Golf "Pole Position"
bignum bakeoff each track one fixed $R$ across $n$; Googology Wiki ranks
growth rates qualitatively; none price $\kappa(R)$). Building it is new
synthesis, not a lookup.

Mode: open. Whether a clean "compactness law" exists relating $\kappa(R)$
to growth rate is not known at the time of writing — this may end up being
"no clean law, here is the scattered data" rather than a theorem.

## Phase 0 — audit and ground the existing partial lists

Before adding anything new, pin down what the existing partial resources
actually claim, since Section 9 of `BN-function.md` and the previous
discussion already leaned on some of these from memory:

- **Busy Beaver champions.** Confirm the current state of bbchallenge.org's
  results: which $BB(k)$ are proven exact (as of writing, believed exact
  through $k=5$, proven 2024), and what the best certified lower bound for
  $k=6$ is, with the actual witness machine and who found it. Record the
  proof status (proven exact / proven lower bound only / conjectural) for
  each, not just the numeral.
- **Bignum bakeoff / "Pole Position: fewest bytes, biggest number"
  (Code Golf StackExchange).** Pull the current leaderboard: byte count,
  author, language/encoding (BLC vs. other), and what growth-rate class
  each entry is claimed to reach. Cross-check the three figures already
  taken from the video transcripts (49 bytes / Buchholz's ordinal, 52
  bytes / BMS, 233 bytes / beats Loader's number) against the actual thread
  rather than trusting the paraphrase in `BN-function.md`.
- **Googology Wiki.** Locate its comparison/ranking pages for large-number
  systems (FOOT, BIG FOOT, Rayo's function variants, the oodle/array
  hierarchy) and record what growth-rate ordering they assert and on what
  basis (proof vs. community consensus vs. unverified claim) — this wiki
  is not peer-reviewed and prior work in this repo
  has found community sources need independent verification before being
  treated as fact.

Output of Phase 0: a short `FINDINGS.md` section per source, each entry
with what was actually checked and its current state, distinguishing
proven results from community claims.

## Phase 1 — define $\kappa(R)$ operationally

`BN-function.md` defines $\kappa(R)$ conceptually (the size of a full
specification of $R$'s grammar and evaluation/proof rules in a fixed
reference meta-language) but does not fix that meta-language or a counting
convention. Before computing any $\kappa(R)$ values:

- Choose one fixed reference meta-language for writing down specifications
  of $R$ (a natural candidate: a minimal universal Turing machine or a
  small combinator calculus, so that $\kappa(R)$ itself is measured in the
  same kind of unit — bits — as the BLC-based $n$ values already in use).
- Decide what must be included in a "full specification" of each $R$: for
  a Turing machine, essentially nothing beyond the state/symbol counts
  already counted as $n$ (so $\kappa \approx 0$ — the rules of TM
  computation are the meta-language's own primitive, not extra payload);
  for BLC, the interpreter/reduction-rule implementation; for BMS, the
  matrix-reduction algorithm; for a PTO-based system, the proof-checker
  for that theory's axioms and inference rules; for Rayo's function, a
  satisfaction-relation evaluator for first-order set theory.
- Write down this convention explicitly and flag the arbitrary choices —
  this is a definitional decision, not a discovered fact, and the plan's
  conclusions will be conditional on it.

Output of Phase 1: a short methodology note fixing the meta-language and
counting rules, committed alongside `BN-function.md`.

## Phase 2 — populate the table

Using Phase 1's convention, estimate $\kappa(R)$ for each row of
`BN-function.md`'s Section 7 table:

| $R$ | $\kappa(R)$ estimate | growth rate | source |
|---|---|---|---|
| Turing machines | (from Phase 1) | uncomputable, faster than any computable function | Radó 1962 |
| BLC | interpreter size | uncomputable | Tromp |
| single-row BMS | reduction-rule size | $\varepsilon_0$ | Kale's proof (linked in transcript) |
| multi-row BMS / PTO systems up to $\Pi^1_1\text{-CA}_0$ | proof-checker size | $\psi(\Omega_\omega)$ (Buchholz) | Phase 0 |
| System F / Calculus of Constructions (Loader's number) | type-checker size | PTO of System F/CoC | Phase 0 |
| first-order set theory (Rayo's function) | satisfaction-relation evaluator size | dominates every function provably total in the theory | Rayo 2007 |

Each row needs an actual estimate, not a placeholder — if a real estimate
is infeasible for a given row (e.g. formalizing a full ZFC satisfaction
evaluator is a large undertaking), say so explicitly in the table rather
than guessing a number, per this repo's standing rule against reporting
unfinished work as resolved.

## Phase 3 — small-$n$ empirical check

For the $R$ where exact or near-exact search is tractable (small Turing
machines; short BLC programs), independently compute or look up $BN(R,n)$
for a handful of small $n$ (e.g. $n=1$ bit, $n=10$ symbols, and the largest
$n$ for which the relevant leaderboard/proof already has a settled entry)
and sanity-check them against Phase 0's ground-truth data. This is a
verification step, not a new search effort — do not attempt original
exhaustive search over machine/program space; that is far outside what is
feasible by hand or by a single agent session, and the point is to confirm
the table in Phase 2 against reality at the few points where reality is
actually known, not to extend the frontier.

## Phase 4 — look for (or rule out) a compactness law

With Phase 2's table populated and Phase 3's spot-checks done, examine
whether growth rate as a function of $\kappa(R)$ looks like it follows any
recognizable pattern (linear, exponential, or no discernible relationship
at all across only ~6 data points). With this few systems in the table, a
firm law is unlikely to be establishable — the realistic output of this
phase is a documented, honest read of what the data does and does not
support, not a proof of a new theorem. If the data is too sparse to say
anything, report that plainly rather than overfitting a "law" to six
points.

## Documentation

Match the conventions used elsewhere in this repo: this `PLAN.md` for the
phased plan, a `FINDINGS.md` recording Phase 0's audit and Phase 4's
conclusions (or lack thereof) with sources and dates, and updates to
`BN-function.md` itself if Phase 1's operational definition of $\kappa(R)$
refines or corrects what is currently only stated conceptually there.

## Explicitly out of scope

- Attempting to extend any existing Busy Beaver or bignum-bakeoff record
  (finding a shorter program or a larger $BB(6)$ lower bound) — this plan
  is about *comparing* existing systems, not competing on any one of them.
- Treating Googology Wiki claims as verified facts without checking their
  cited basis (Phase 0).
- Claiming a "compactness law" is established from a table of a handful of
  systems — six data points is a sketch, not a theorem, and Phase 4 must
  say so if that is what the data supports.
