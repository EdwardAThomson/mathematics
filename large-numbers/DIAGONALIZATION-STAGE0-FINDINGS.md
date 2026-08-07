# Stage 0 findings: prior art for the diagonalization construction

Three parallel research agents (cloud-isolated), per `DIAGONALIZATION-PLAN.md`.
All three findings below are sourced; see each agent's cited URLs.

## 1. Mathlib's `ModelTheory` — reusable, but not the hard part

`Mathlib.ModelTheory.Semantics` has a full, mature satisfaction relation
(`Realize`, `Sentence.Realize`, `Theory.Model`) for arbitrary first-order
languages, plus compactness, Löwenheim-Skolem, and completeness
(`Satisfiability.lean`). But `Realize` is a **meta-level Lean `Prop`**, not a
formula of the object language itself — Mathlib has no internalized syntax,
no Gödel-coding of formulas as data, and (confirmed via a 2021-2022 Zulip
thread) both incompleteness theorems are explicitly open, unmerged goals
there. Mathlib alone would not get Stage 2 started.

## 2. `FormalizedFormalLogic/Foundation` — the actual reusable asset

A real, independent, active Lean 4 library (264 stars, 1,421 commits, led by
Shogo Saito, independently confirmed via Freek Wiedijk's "Formalizing 100
Theorems" tracker) with **sorry-free proofs of both Gödel incompleteness
theorems**. It already has internal Gödel coding
(`Bootstrapping/Syntax/{Formula,Term,Proof}/Coding.lean`), an internal
fixed-point/diagonal lemma (`Bootstrapping/FixedPoint.lean`:
`T ⊢ fixedpoint θ ↔ θ/[⌜fixedpoint θ⌝]`), Tarski's undefinability proved from
it, and — closest to our own approach — a `SetTheory/` tree (`HFS`, `ZF`,
`Z`, `TransitiveModel`, `Ordinal`) built over hereditarily finite sets, the
same model `rayo-lean/` already uses. Not in Mathlib; a separate dependency.

**Scale reference, from a second, independent source (question 2's agent):**
Russell O'Connor's Coq incompleteness formalization is 46 files, ~45,000
lines total. Lawrence Paulson's Isabelle version does the equivalent
diagonal-lemma step in under 450 lines — a sourced, concrete illustration
that the choice of encoding style and proof assistant changes the effort by
an order of magnitude, not just a constant factor.

**Closest existing precedent for an internal FOST satisfaction predicate:**
Paulson's ZF-Constructible Isabelle library has a real satisfaction
predicate `M, ms ⊨ φ`, defined by recursion on formula syntax, for a
**set-sized model M** (used in his relative-consistency-of-AC proof, later
extended to a forcing relation by Gunther/Pagano/Sánchez Terraf). This is
satisfaction *in a model*, not truth-in-the-full-universe-V — a real gap
from what Rayo's construction needs — but the closest thing found to Stage
2's requirement, and it exists in Isabelle, not Lean.

## 3. Rayo's function itself: no formalization, and a citation to correct

**No formalization of Rayo's function exists anywhere** — not a stub, not
an internal `Sat` predicate, not a diagonal lemma, in any proof assistant.
Confirmed independently by all three agents.

**Citation error in our own `rayo-notes/literature-notes.md`:** the prior
run cited `web.mit.edu/arayo/www/fc.pdf` ("On Specifying Truth-Conditions")
as the primary source for Rayo's `Sat` construction, noting only that the
PDF wasn't machine-text-extractable at the time. This agent fetched and
full-text-searched that PDF directly: it contains **zero** occurrences of
"Rayo's number," "googol," or "paradox" — it is a different paper entirely,
about ontological commitment in arithmetic/modal discourse. **The actual
primary source is Rayo's own account in his 2019 MIT Press book "On the
Brink of Paradox," Chapter 9.4, "The Big Number Duel"**
(`web.mit.edu/arayo/www/brink-duel.pdf`), which the agent did successfully
fetch and read in full. `literature-notes.md` needs correcting; see below.

**What Rayo's chapter actually says about the paradox** (notably: Rayo
himself never uses the words "Berry" or "paradox" anywhere in it — that
framing is entirely a later overlay from Wikipedia/Googology Wiki writers,
not Rayo's own account): the duel's rules banned "semantic vocabulary —
expressions like 'names' or 'refers to.'" A naive Berry-style formula
("named in ≤10^100 symbols") would have been disallowed outright for
containing "named." The winning entry instead "relied on a second order
language... to characterize a non-semantic substitute for the notion of
being named" — using `Sat` plus second-order quantification as a syntactic
proxy, sidestepping the paradox by construction rather than by proving a
diagonal lemma. **This is asserted in prose, not proven** — no rigorous
treatment of its consistency exists anywhere, per this search.

## 4. Adjacent, genuinely rigorous work — and why it takes a different route

Every *rigorous* (proven, not asserted) Berry-paradox-style construction
found uses a categorically different escape from Rayo's:

- **Boolos (1989)**, "A New Proof of the Gödel Incompleteness Theorem" —
  shifts "nameable" from *true* to *provable*, avoiding contradiction by
  proving non-provability rather than a semantic falsehood. This is not
  what Rayo's construction does.
- **Kikuchi, Kurahashi & Sakai (2012)** — rigorous, unmechanized, shows
  Boolos's proof is a special case of Chaitin's Kolmogorov-complexity proof.
- **Grego (2022 bachelor's thesis, Charles University)** — the most careful
  non-mechanized treatment found, states the exact danger plainly: "for n
  sufficiently large, the formula naming it has less than n symbols" — and
  resolves it via Boolos's provable/true shift, not Rayo's second-order
  proxy.
- **Paulson's Isabelle AFP incompleteness entry** deliberately does **not**
  use the Boolos/Berry route at all — it uses Świerczkowski's HF-set/
  derivability-conditions method, citing Boolos only as informal contrast.

So even the most Berry-paradox-adjacent *formalized* work in existence
avoids the specific style of self-reference Rayo's construction uses.

## What this changes about the plan

Stage 1 (encode formulas as sets) is now lower-risk than before Stage 0: real
prior art (`Foundation`) exists to draw structural patterns from, even
though it isn't a drop-in dependency.

Stage 2-3 as originally scoped — formalize *Rayo's own* diagonalization —
is now known to be riskier than "a hard formalization of known math." It
would mean formalizing something **nobody has ever given a fully rigorous
proof of, informally or mechanically** — Rayo's own account is a prose
sketch, not a theorem. That is closer to original research than to
formalization, and the honest risk assessment has to reflect that.

There is a lower-risk alternative that still demonstrates the same
underlying phenomenon (diagonalization beats naive enumeration): target the
**Boolos-style** construction instead of Rayo's own. It is rigorously
proven in the literature, has real formalized precedent to build from
(O'Connor's Coq work, Paulson's AFP entry, `Foundation`'s incompleteness
proofs), and — because it proves non-*provability* rather than needing a
full truth-in-V satisfaction predicate — sidesteps exactly the part of
Stage 2 that was the biggest source of uncertainty. It would demonstrate
"diagonalization is dramatically more efficient than enumeration" just as
concretely, on a well-precedented construction rather than an untested one.
