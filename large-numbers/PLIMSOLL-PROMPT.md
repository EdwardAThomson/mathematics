Goal (frozen): for the reference systems R already identified in
`large-numbers/BN-function.md` (Busy Beaver's Turing machines, Binary Lambda
Calculus, single/multi-row Bashicu Matrix System, Loader's-number-style type
theories, Rayo's first-order set theory), build an actual table of
(kappa(R), growth rate of BN(R,.)) pairs, grounded in real leaderboard/proof
data rather than restated folklore, and use it to say something concrete
about whether growth rate scales cheaply or expensively with specification
cost. This table does not currently exist anywhere (checked: bbchallenge.org
and the Code Golf "Pole Position" bignum bakeoff each track one fixed R
across n; Googology Wiki ranks growth rates qualitatively; none price
kappa(R)). Building it is new synthesis, not a lookup.

Mode: open. Whether a clean "compactness law" exists relating kappa(R) to
growth rate is not known at the time of writing — this may end up being "no
clean law, here is the scattered data" rather than a theorem. Do not force a
law onto six data points; report what the data does and does not support.

Background already committed in this directory: `BN-function.md` (the
formal definition of BN(R,n), admissibility conditions A1-A5, kappa(R) as a
concept, Sections 6-9 covering known instances and the open question) and
`PLAN.md` (the phased research plan this prompt operationalizes). Read both
before doing anything else; do not re-derive what they already establish.

Every item below is either `build` (an artifact that works, verified by
running it) or `inquiry` (a question investigated, verified by evidence that
the investigation happened — a source fetched, a citation recorded, a
computation run and its output captured — never by whether the resulting
claim is true). Do not write a verify that checks a conclusion's
correctness; that is not available for open questions and pretending
otherwise produces a tick on nothing.

`FINDINGS.md` is rendered by the harness from recorded findings; no item may
write it, assemble it, or declare it in `scope`/`assembles`. Every "record
as a finding" instruction below means: use the harness's own finding
mechanism for that item, not a hand-written edit to that file.

## Phase 0 (inquiry): audit and ground the existing partial lists

Before adding anything new, pin down what the existing partial resources
actually claim, since `BN-function.md` Section 9 and the plan behind this
prompt leaned on some of these from memory or from paraphrased video
transcripts. Each of the following is its own item — they fail
independently, so do not merge them:

(a) BB(1) through BB(5) on bbchallenge.org: confirm "proven exact," and
    record the specific proof citation and date (the 2024 5-state proof by
    name/reference, not just "2024 proof").

(b) BB(6), current best certified lower bound: record the witness machine
    (its transition table or a link to it), who found it, and whether the
    bound is community-verified, peer-reviewed, or still informal.

(c) The Code Golf StackExchange "Pole Position: fewest bytes, biggest
    number" thread's current top entries: byte count, author,
    language/encoding (BLC vs. other), claimed growth-rate class for each.

(d) Cross-check the three figures `BN-function.md` currently states from
    paraphrasing the video transcripts rather than the thread itself: 49
    bytes reaching Buchholz's ordinal, 52 bytes reaching BMS, 233 bytes
    beating Loader's number. Confirm or correct each against the actual
    thread (author, exact byte count, exact claim). If any figure is wrong,
    record it as a finding requiring a follow-up correction to
    `BN-function.md`, not a silent fix.

(e) Googology Wiki's comparison/ranking page for FOOT / BIG FOOT: record the
    growth-rate ordering it asserts and on what basis (a cited proof, a
    cited external claim, or unsourced wiki consensus) — Googology Wiki is
    not peer-reviewed and prior work in this repo found
    community sources need independent verification before being treated as
    fact.

(f) Googology Wiki's ranking of Rayo's function variants: same treatment.

(g) Googology Wiki's page(s) on the oodle / array notation hierarchy: same
    treatment.

Evidence contract for every Phase 0 item's recorded finding: `source`
(exact URL(s) fetched), `fetched` (date — these are live/community pages
that can have changed since this prompt was written), `claim` (a direct
quote or tightly-anchored paraphrase, not a restatement from memory of the
video transcripts), `status` (one of proven / certified-lower-bound /
conjectural / community-consensus / unverified-claim / not-found). If a
source cannot be reached or a claim cannot be located, record that
explicitly as `not-found` with what was tried — an omitted entry reads as
"not investigated," which is worse than "investigated, found nothing
usable."

If any Phase 0 finding contradicts what `BN-function.md` currently states,
say so plainly in that finding and flag the specific section/line to
correct; do not silently proceed on a claim Phase 0 itself just falsified.

## Phase 1 (inquiry + build): define kappa(R) operationally

`BN-function.md` defines kappa(R) conceptually but does not fix a reference
meta-language or counting convention. Before computing any kappa(R) value:

- Choose one fixed reference meta-language for writing specifications of R
  (a natural candidate: a minimal universal Turing machine or a small
  combinator calculus, so kappa(R) is measured in the same kind of unit —
  bits — as the BLC-based n values already in use). State the candidate
  considered and why it was chosen.
- Decide what must be included in a "full specification" of each R: for a
  Turing machine, essentially nothing beyond the state/symbol counts already
  counted as n; for BLC, the interpreter/reduction-rule implementation; for
  BMS, the matrix-reduction algorithm; for a proof-theoretic-ordinal-based
  system, the proof-checker for that theory's axioms and inference rules;
  for Rayo's function, a satisfaction-relation evaluator for first-order set
  theory.
- Write this convention down explicitly and flag the arbitrary choices in
  it — this is a definitional decision, not a discovered fact, and every
  later conclusion is conditional on it.

Output: a methodology note (`METHODOLOGY.md`), committed alongside
`BN-function.md`. Verify: the file exists, states the chosen meta-language,
and for each of the five R families in the Phase 2 table below states what
counts toward its kappa(R) — a structural check, not a check that the
convention is "correct" (there is no ground truth to check it against).

## Phase 2 (inquiry): populate the table

Using Phase 1's convention and Phase 0's audited data, estimate kappa(R) for
each row of `BN-function.md` Section 7's table (Turing machines, BLC,
single-row BMS, multi-row BMS / proof-theoretic-ordinal systems, System F /
Calculus of Constructions, first-order set theory). Each row needs an actual
estimate with its derivation shown, not a placeholder. If a real estimate is
infeasible for a given row (e.g. formalizing a full ZFC satisfaction
evaluator is a large undertaking on its own), say so explicitly in the table
rather than guessing a number. Output: the table, committed to a dedicated
`KAPPA-TABLE.md` (`FINDINGS.md` cannot be an item's output — see above),
each cell traceable to either a Phase 0 finding or a Phase 1 methodology
rule, and each cell's derivation also recorded as its own finding.

## Phase 3 (build): small-n empirical check

For the R where exact or near-exact search is tractable (small Turing
machines; short BLC programs), independently compute or look up BN(R,n) for
a handful of small n and sanity-check against Phase 0's ground-truth data.
This is a verification step, not a new search effort — do not attempt
original exhaustive search over machine/program space. Build items here get
real verifies (the computation runs, produces a number, and that number is
checked against the Phase 0 citation) with a negative control where
practical (e.g. confirm the checker rejects a deliberately wrong BB(4)
value).

## Phase 4 (inquiry): look for, or rule out, a compactness law

With Phase 2's table and Phase 3's spot-checks in hand, examine whether
growth rate as a function of kappa(R) shows any recognizable pattern. With
only around six data points a firm law is unlikely to be establishable —
report a documented, honest read of what the data does and does not
support. If the data is too sparse to say anything, report that plainly.
This phase's item is inquiry-only: there is no artifact to build, only a
conclusion to record with its reasoning and caveats.

## Documentation

Match the conventions used elsewhere in this repo: a recorded finding per this prompt's Phase 0, 2 and 4
items (evidence contract above; `FINDINGS.md` itself is rendered by the
harness, never written directly), `KAPPA-TABLE.md` per Phase 2,
`METHODOLOGY.md` per Phase 1, and updates to `BN-function.md` itself where
Phase 0 or Phase 1 corrects or refines what it currently states only
conceptually.

## Explicitly out of scope

- Attempting to extend any existing Busy Beaver or bignum-bakeoff record
  (finding a shorter program or a larger BB(6) lower bound) — this is about
  comparing existing systems, not competing on any one of them.
- Treating Googology Wiki claims as verified facts without checking their
  cited basis (Phase 0e-g).
- Claiming a "compactness law" is established from a table of a handful of
  systems — six data points is a sketch, not a theorem, and Phase 4 must say
  so if that is what the data supports.
- Original exhaustive search over Turing-machine or program space (Phase 3
  is a spot-check against known results, not a new search).
