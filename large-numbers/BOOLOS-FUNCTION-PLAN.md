# Work breakdown: a Boolos-style big-number function

Lower-risk of the two forks from `DIAGONALIZATION-PLAN.md`. Real precedent
exists (`FormalizedFormalLogic/Foundation`, O'Connor's Coq work, Paulson's
Isabelle work — see `DIAGONALIZATION-STAGE0-FINDINGS.md`); this is adapting
and reusing established, working machinery, not building it from nothing.

**Read first:** `BN-function.md`, `RAYO-EXPLAINER.md` (the last three
sections especially), `DIAGONALIZATION-PLAN.md`,
`DIAGONALIZATION-STAGE0-FINDINGS.md`. Do not re-derive what they establish.

**Important scope note, decide this before starting anything:** the striking
"3× per step, forever" result from `rayo-lean/`'s K0-K6 work was dramatic
*because bare first-order set theory has no arithmetic primitives at all* —
naming even "6" costs thousands of symbols. Peano Arithmetic, the natural
base theory for a Boolos-style construction, already has `0`, successor,
`+`, `×` built in — a naive numeral for k already costs roughly O(log k)
symbols (positional encoding) or O(k) (successor chains), nothing like
FOST's blowup. So a Boolos-style function's interesting property is *not*
"beats naive enumeration by orders of magnitude at tiny k" — it's that it
eventually dominates every function PA can prove total, a growth-*class*
argument, not a small-n efficiency table. Decide up front which of these
two different kinds of result you actually want before scoping the work,
because they lead to different deliverables.

## Phase B0 — Pin the definition down on paper, before any code

1. Fix the base theory: **Peano Arithmetic (PA)**, not full ZFC/set theory.
   This keeps the language tiny (`0, S, +, ×, =, <, ¬, ∧, ∃, ∀`, variables,
   parens) and — critically — avoids reopening the "which second-order
   semantics" ambiguity that afflicts Rayo's own construction (§4 of
   `DIAGONALIZATION-STAGE0-FINDINGS.md`). PA is also what `Foundation`'s
   existing incompleteness proofs are built over, maximizing reuse.
2. Define precisely: a formula `φ(x)` (one free variable, PA's language)
   **T-names** `k` when `T ⊢ ∀x(φ(x) ↔ x=k)` — provable unique denotation,
   not true unique denotation. This is the swap that avoids Tarski's
   undefinability barrier (provability is expressible in the object
   language; truth is not).
3. Define `BoolosBig_T(n) = sup{ k : some φ with |φ| ≤ n T-names k }`.
4. **Prove, on paper, that this is well-defined** — this is the exact step
   Rayo's own account skips (per `DIAGONALIZATION-STAGE0-FINDINGS.md` §3,
   it's asserted, never proven). For a fixed n, the set of formulas of
   length ≤ n is finite and enumerable, and "does T prove ∀x(φ(x)↔x=k)" is
   semi-decidable (T's proof relation is r.e.) — write out the actual
   argument for why the sup is finite and well-defined, not just why it
   feels like it should be.
5. Output of this phase: a written proof sketch, human-checked, *before*
   touching Lean. If it doesn't close — if there's a real obstruction to
   even the PA/provability version being well-defined — that is itself the
   finding, and Phase B1 should not start until this is resolved or the
   plan is revised.

## Phase B1 — Formalize the T-names predicate, reusing Foundation

`Foundation` already has internal Gödel coding of PA formulas, an internal
provability predicate `Prov_T`, and a proven diagonal/fixed-point lemma
(`Bootstrapping/FixedPoint.lean`). The "T-names" predicate from B0 should be
directly expressible using its existing coding and `Prov_T` machinery —
check this concretely (does `Foundation` already have a "formula names a
unique value" notion, or something close enough to adapt?) before writing
anything new. Vendor or depend on `Foundation` rather than reimplementing
its coding/diagonal-lemma machinery from scratch — that would be redoing
work Stage 0 found already exists, sorry-free.

## Phase B2 — Small-n table, mechanically verified

Same spirit as `rayo-lean/`'s K0-K6, adapted to PA: for small n, exhibit a
formula T-naming the largest k you can find, and mechanically verify T
actually proves it (i.e. produce and check the actual PA-derivation, via
`Foundation`'s `Prov_T`/proof-search machinery, not just assert it).
Same discipline as before: every value is an upper bound from an exhibited
witness, never claimed minimal; record the honest largest-k-reached and why
it stopped there, per the resource-cap discipline in
`DIAGONALIZATION-PLAN.md`.

## Phase B3 — The growth-class argument (if that's the goal — see the scope note above)

Separately from B2's table: connect `BoolosBig_T` to a known growth-class
result — e.g. that it eventually dominates every PA-provably-total
function, tying back to Gödel's speedup theorem or standard incompleteness
consequences. This is a different deliverable from B2's table (a
qualitative/asymptotic claim, not a small-n number) and could be scoped as
its own separate piece of work rather than bundled in.

## Rough sizing, from real reference points

O'Connor's Coq incompleteness work (comparable diagonal-lemma-plus-coding
scope) was ~45,000 lines; Paulson's Isabelle version did the analogous
piece in under 450 lines. Building on `Foundation` (which already has the
hard parts done, sorry-free) should land much closer to Paulson's end of
that range than O'Connor's — but that's an expectation, not a bound; treat
it as informative rather than a promise, per this project's own rule
against reporting an estimate as settled.
