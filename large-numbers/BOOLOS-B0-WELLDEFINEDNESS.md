# Phase B0: well-definedness of a Boolos-style big-number function

Phase B0 of `BOOLOS-FUNCTION-PLAN.md` (the lower-risk fork of
`DIAGONALIZATION-PLAN.md`). The plan is explicit that B0 is **a written proof
sketch, human-checked, *before* touching Lean** — and that it is the exact
step Rayo's own account skips (`DIAGONALIZATION-STAGE0-FINDINGS.md` §3: the
well-definedness of the naming construction is *asserted, never proven*,
anywhere, informally or mechanically). This note is that proof.

**What this delivers, and what it does not.** It proves, rigorously and by
hand, that the Boolos-style function `BoolosBig_T(n)` is a well-defined
natural number for every `n` — the B0 go/no-go gate. It does **not** contain
any Lean: see "Why no Lean here" at the end. It closes the gate (the
construction *is* well-defined), it isolates the two hypotheses that are
actually load-bearing, it corrects one imprecision in the plan's own framing,
and it makes the B2-vs-B3 scope decision the plan asked to settle up front.

---

## 1. Setup and definitions

Fix the base theory **T = Peano Arithmetic (PA)** over the usual first-order
language `L = {0, S, +, ×, =, <}` with logical symbols `¬, ∧, ∀`, parentheses,
and variables `v₀, v₁, v₂, …` (the other connectives/quantifiers `∨, →, ↔, ∃`
are abbreviations, matching the convention already used in
`rayo-lean/Rayo/Syntax.lean`). PA is chosen over full set theory for the
reasons in `BOOLOS-FUNCTION-PLAN.md` Phase B0.1: it keeps `L` tiny, it is the
base theory `FormalizedFormalLogic/Foundation` already builds its
incompleteness proofs over, and — critically — it avoids reopening the
"which second-order semantics" ambiguity that afflicts Rayo's own construction
(`DIAGONALIZATION-STAGE0-FINDINGS.md` §4).

For `k ∈ ℕ` let `k̄ := Sᵏ(0)` be the **canonical numeral**, a closed `L`-term.
Write `|φ|` for the length of `φ` as a symbol string over `L`, under the
project's standing convention (`RAYO-EXPLAINER.md`): **each symbol occurrence
costs 1, and a variable occurrence costs 1 regardless of its index** (`v₁` and
`v₁₁₅` both cost 1).

> **Definition (T-names).** An `L`-formula `φ` with exactly one free variable
> `x` **T-names** `k ∈ ℕ` iff
> ```
>     T ⊢ ∀x ( φ(x) ↔ x = k̄ ).
> ```
> This is *provable* unique denotation, not *true* unique denotation — the
> Boolos swap (`BOOLOS-FUNCTION-PLAN.md` B0.2). Its point is discussed in §5;
> it is **not** needed for this section's theorem.

> **Definition (the function).**
> ```
>     BoolosBig_T(n) := sup { k ∈ ℕ : ∃φ,  φ has one free variable,
>                                          |φ| ≤ n,  and  φ T-names k },
> ```
> with the convention `BoolosBig_T(n) = 0` when the set is empty (mirroring
> `BN-function.md` §3's `BN(R,n)=0`-if-nothing-qualifies convention).

This is exactly the `BN(R, n)` schema of `BN-function.md` §3, instantiated at
`R = (PA, provable-naming)`: `L` is the language, the one-free-variable
formulas that T-name something are `dom⟦·⟧`, and `⟦φ⟧ = k` when `φ` T-names
`k`.

---

## 2. The two hypotheses that are load-bearing

The theorem below needs exactly two things. Naming them explicitly *is* the
value of B0 — Rayo's prose sketch uses both silently.

- **(H1) T is consistent.** This is `BN-function.md`'s admissibility
  condition **A4**. It is what makes T-naming *functional* (§3, Lemma 1). An
  inconsistent T proves everything, so every `φ` would T-name every `k` and
  the sup would be `+∞` — vacuously "unbounded," the Berry-paradox failure
  mode A4 is designed to rule out.
- **(H2) Formulas are counted up to α-equivalence** (renaming of bound
  variables). This one is *not* in `BN-function.md`'s A1–A5, and it is the
  subtler finding — see §4. Under the project's "a variable costs 1 whatever
  its index" convention with `ℕ`-indexed variables, the *raw* set of formulas
  of length `≤ n` is **infinite**, and finiteness (§3, Lemma 2) fails without
  quotienting by α.

T also needs to extend Robinson arithmetic Q (PA does), so that `T ⊢ k̄ ≠ m̄`
for `k ≠ m` — used once, in Lemma 1.

---

## 3. Theorem and proof

> **Theorem (B0).** If T is consistent, then for every `n ∈ ℕ`,
> `BoolosBig_T(n)` is a well-defined natural number, and `BoolosBig_T` is
> monotone non-decreasing in `n`.

The proof is two lemmas and a one-line combination.

### Lemma 1 (T-naming is functional — uses H1)

*If `φ` T-names `k` and `φ` T-names `k'`, then `k = k'`.*

**Proof.** By hypothesis `T ⊢ ∀x(φ(x) ↔ x = k̄)` and
`T ⊢ ∀x(φ(x) ↔ x = k̄')`. Chaining the two biconditionals,
`T ⊢ ∀x(x = k̄ ↔ x = k̄')`. Instantiate `x := k̄`:
`T ⊢ (k̄ = k̄ ↔ k̄ = k̄')`, and since `T ⊢ k̄ = k̄` (reflexivity of `=`),
`T ⊢ k̄ = k̄'`. Now suppose `k ≠ k'`. Then `Q ⊆ T` proves distinct numerals
unequal, `T ⊢ ¬(k̄ = k̄')`, so T proves both `k̄ = k̄'` and its negation — T
is inconsistent, contradicting **H1**. Hence `k = k'`. ∎

So `φ ↦ (the unique k it T-names, if any)` is a **partial function** from
formulas to `ℕ`. This is precisely where consistency is spent, and it is the
formal content of "the rules must not be self-contradictory."

### Lemma 2 (finitely many candidate formulas — uses H2)

*For each `n`, the set `Φₙ` of one-free-variable `L`-formulas with `|φ| ≤ n`,
taken up to α-equivalence, is finite.*

**Proof.** A formula with `|φ| ≤ n` has at most `n` symbol occurrences, hence
at most `n` variable occurrences, hence mentions at most `n` distinct
variables. Renaming its one free variable to a fixed symbol `x` (a logical
equivalence that preserves length) and α-renaming its bound variables into a
fixed pool `{w₁, …, wₙ}` (`n` names always suffice, since there are `≤ n`
occurrences), every such formula is α-equivalent to one over the **finite**
alphabet
```
    Σₙ = {0, S, +, ×, =, <, ¬, ∧, ∀, (, )} ∪ {x, w₁, …, wₙ}.
```
There are at most `|Σₙ|ⁿ⁺¹` strings of length `≤ n` over `Σₙ`, finitely many;
a fortiori finitely many formulas, a fortiori finitely many α-classes. So
`Φₙ` (mod α) is finite. ∎

Both objects Lemma 2 quietly relies on are α-invariant, which is what makes
the quotient legitimate:

- **length** is α-invariant, because a variable costs 1 regardless of index
  (the project convention) — so renaming bound variables never changes `|φ|`;
- **T-naming** is α-invariant, because α-equivalent formulas are provably
  equivalent in pure first-order logic, so `T ⊢ ∀x(φ ↔ x=k̄)` holds for `φ`
  iff it holds for any α-variant of `φ`.

### Combination

By Lemma 1 the map `name : Φₙ ⇀ ℕ` (send each α-class to the unique `k` it
T-names, undefined if none) is a well-defined partial function on the
**finite** set `Φₙ` (Lemma 2). Its image
```
    Ψₙ = { k : some φ ∈ Φₙ T-names k }
```
is therefore a finite subset of `ℕ`. A finite subset of `ℕ` is either empty
(then `BoolosBig_T(n) = 0` by convention) or has a maximum; either way
`BoolosBig_T(n) = sup Ψₙ = max Ψₙ` is a well-defined natural number.
Monotonicity is immediate: `n ≤ n'` gives `Φₙ ⊆ Φₙ'`, hence `Ψₙ ⊆ Ψₙ'`, hence
`max Ψₙ ≤ max Ψₙ'`. ∎

**The gate is passed.** The PA/provability version of the construction is
well-defined, with the two hypotheses above discharged rather than assumed.

---

## 4. The α-equivalence obstruction (the real finding)

The interesting part of B0 is **Lemma 2's failure without H2**, because it is
specific to this project's cost convention and is exactly the kind of gap the
plan wanted surfaced ("if there's a real obstruction to even the
PA/provability version being well-defined — that is itself the finding").

Under "a variable occurrence costs 1 regardless of index" with an infinite
supply `v₀, v₁, v₂, …` of variables, consider the formulas `vᵢ = vᵢ` for
`i = 0, 1, 2, …`. Each has the **same** length, and there are infinitely many
of them. So `{φ : |φ| ≤ n}`, taken **literally**, is infinite for every `n ≥`
(the length of a single equation). If you tried to define `BoolosBig_T(n)` as
a sup over that literal set, you would be taking a sup over an infinite index
set, and the finiteness argument that guarantees a maximum evaporates.

Two ways out, and it matters which you pick:

1. **Quotient by α-equivalence (H2, adopted here).** Sound because both
   length and T-naming are α-invariant under this convention (§3). The
   construction descends to α-classes and Lemma 2 holds. This is the honest
   minimal fix and costs nothing in the cost model.
2. **Change the convention to charge for variable identity** (e.g. `⌈log₂ i⌉`
   bits for `vᵢ`). Then `{φ : |φ| ≤ n}` is finite on the nose, no quotient
   needed. But `RAYO-EXPLAINER.md` deliberately rejected this — it "would
   penalize formulas that happen to need many simultaneously-live variables"
   — and flagged that the free-identity rule "is quietly absorbing a real cost
   that grows right alongside `nₖ`." B0 shows the other place that same
   quiet cost surfaces: **it is also what you must pay to make the sup
   well-defined at all**, unless you take route 1.

Either route closes B0; neither is wrong; but one of them has to be named, and
Rayo's account names neither. **Recommendation: adopt H2 (route 1)** — it
keeps the existing cost convention untouched and is the standard move
(bounded-length-formulas-up-to-α is a finite set is textbook), so it imports
no new controversy. This should be written into `METHODOLOGY.md` as a counting
rule if the Boolos line is pursued.

---

## 5. Truth vs. provability — a precisification of the plan

`BOOLOS-FUNCTION-PLAN.md` B0.2 attaches the Tarski-undefinability motivation
to the *definition* of T-names ("This is the swap that avoids Tarski's
undefinability barrier"). That is right about *why the swap is eventually
needed*, but it is worth separating two claims that the phrasing can blur,
because getting this wrong would misdirect Stage 2:

- **B0's sup is well-defined for the *truth* reading too.** Define `φ`
  *truth-names* `k` iff `ℕ ⊨ ∀x(φ(x) ↔ x = k̄)`, i.e. `φ` defines the
  singleton `{k}` in the standard model. Lemma 1 holds trivially (a formula
  true of exactly one number determines it — no consistency needed, since
  truth is automatically consistent), and Lemma 2 is unchanged. So
  `BoolosBig_T^{true}(n)` is *also* a well-defined natural number. **B0 does
  not, by itself, force the provability swap.**
- **The swap is forced one step later, at internalization (B2/B3).** The
  Rayo/Boolos payoff needs a formula that refers *inside the object language*
  to "is named by some short formula" — the self-referential/diagonal step.
  That predicate must be an `L`-formula.
  - `Provₜ(⌜ψ⌝)` **is** an `L`-formula (Σ₁, r.e. — search for a proof), so
    provable-naming, `∃(proof of ∀x(φ ↔ x=k̄))`, is internally expressible and
    can be diagonalized against. This is `Foundation`'s `Prov_T` +
    `Bootstrapping/FixedPoint.lean`.
  - `True(⌜ψ⌝)` is **not** an `L`-formula, by **Tarski's undefinability
    theorem**. So truth-naming cannot be internalized, and the diagonal step
    has nothing to bite on.

Net: the provability swap is what makes the *diagonalization* go through
(Stage 2/3), **not** what makes the *sup* well-defined (Stage B0). B0 closes
for both readings; only provability survives into the internal construction.
This is a mild but real correction to how B0.2 reads, and it means Stage 2's
first obligation is "express provable-naming internally," which `Foundation`
already essentially provides — not "rescue well-definedness," which §3 already
did.

A computability footnote, tying back to `BN-function.md` §6: with the
provability reading `Ψₙ` is r.e. (enumerate proofs), so `BoolosBig_T` is the
limit of a computable-from-below approximation but is itself **not
computable** (you never know you have found all short proofs) — the same
flavor as Busy Beaver. With the truth reading `Ψₙ` is not even r.e. (arithmetic
truth is not). Both are well-defined; the provability one is the one you can
actually approximate, which is a second, independent reason to prefer it.

---

## 6. Scope decision the plan asked to settle: B2 or B3?

`BOOLOS-FUNCTION-PLAN.md`'s scope note (lines 12–24) demands this be decided
*before* scoping any Lean, and B0 is where the decision becomes clear-cut.

The dramatic `rayo-lean` result ("~3× per step, forever; naming *6* costs
11,128 symbols") was dramatic **because bare first-order set theory has no
arithmetic primitives** — every number must be respelled from `∈` and logic.
**PA is different: it has `0, S, +, ×` built in.** The numeral `k̄` already
T-names `k` (`T ⊢ ∀x(x=k̄ ↔ x=k̄)` trivially) in `O(k)` symbols via successors,
or `O(log k)` via a positional `+`/`×` term. So a Boolos-style **small-n
table (B2)** over PA would show *none* of the FOST blow-up — it would be a
flat, unremarkable "naming `k` costs about `log k`" table. The "diagonalization
crushes enumeration by orders of magnitude at tiny `k`" phenomenon is a
FOST-specific artifact and **does not transfer to PA**.

What *is* real and interesting for PA is the **growth-class result (B3)**:
`BoolosBig_PA` eventually **dominates every PA-provably-total function**. The
mechanism is the diagonal one — a formula that provably-names a number defined
to exceed everything nameable by shorter formulas — and the separation is a
growth *class*, not a small-`n` numeral. Its natural home in this project is a
new `KAPPA-TABLE.md`-style data point:

> `R =` (PA + internal provable-naming/diagonalization) reaches growth class
> `≈ ε₀` (the proof-theoretic ordinal of PA — PA's provably-total functions
> are exactly the `<ε₀` functions of the fast-growing hierarchy), via a
> **provability-diagonalization** mechanism.

That is genuinely new information for the project's actual open question
(`BN-function.md` §8, Phase 4): the existing table reaches the `ε₀`
neighborhood via an **ordinal-notation** mechanism (single-row BMS). A Boolos
row reaches comparable territory via a **provability-diagonalization**
mechanism at a *different* `κ` (PA's axioms + a provability predicate, vs. a
matrix-expansion rule). Two different-`κ` mechanisms landing at the same
ordinal is exactly the kind of evidence Phase 4 needs to decide whether its
sub-Turing gradient is a compactness *law* or just the sequence googology
happened to formalize.

> **Recommendation: pursue B3, drop B2.** B2 over PA is an anticlimax that
> would not show the phenomenon; B3 is the real result and the one that feeds
> the project's central question. If a *small-n table* is wanted specifically
> to display the enumeration-vs-diagonalization gap concretely, the right base
> for that is **FOST, not PA** — i.e. it belongs with the `rayo-lean` line
> (and is close to task #4, "does letting formulas reuse each other save
> 20–70×"), not with the Boolos line.

**Caveat, kept honest:** B3's domination claim is the classical Boolos-1989
result and is *sourced*, but it is **not proven in this note** — only its
statement and mechanism are scoped here. B0 (well-definedness) is done; B3
(growth class) is the recommended next deliverable, still to be written.

---

## 7. Handoff: the Lean phases (B1+), and why not here

### Why no Lean here

The Lean toolchain **could not be provisioned in this remote session**: the
org egress policy denied the Lean release host
(`release.lean-lang.org:443` → `403` on CONNECT), and the agent-proxy README
is explicit that policy denials must be reported, not routed around. So no
`lake build` verification was possible from this environment. This is an
environment limitation only — the Stage 1 report shows `elan`/`lean4:v4.32.2`
installs and builds fine **on the laptop**, which is where the Lean work below
should run. Per this project's standing rule (no unverified Lean reported as
settled), this note therefore claims **only the paper proof**, which needs no
toolchain, and hands the machine-checked parts off rather than faking them.

### B1's dependency reality — a decision for the operator

`BOOLOS-FUNCTION-PLAN.md` B1 says to reuse `FormalizedFormalLogic/Foundation`
(internal PA coding, `Prov_T`, diagonal lemma — all sorry-free). That is the
right call *technically* — reimplementing it self-contained is O'Connor-scale
(~45k lines). But `Foundation` **depends on Mathlib**, whereas the current
`rayo-lean` project is deliberately **zero-dependency, no Mathlib** (its
`lake-manifest.json` lists no packages). So B1-as-Lean means one of:

1. **A separate Mathlib+Foundation sub-project** for the Boolos line, kept
   apart from the self-contained `rayo-lean`. Big build, but it is where the
   real internal-`Prov_T` diagonalization can actually be done. Greenlight
   this only if a *machine-checked* B3 is the goal.
2. **Keep B3 as a paper/literature result** (Boolos 1989 is rigorous and
   sourced; formalizing it adds assurance but not new mathematics). Cheapest;
   loses the "mechanically verified" badge the rest of the project prizes.
3. **A self-contained, scaled-down Lean artifact for B0 only** — verify the
   *combinatorial core* of §3 (functional partial naming over a finite
   candidate set has a maximum) with **no** `Prov_T`, no coding, no Mathlib.
   This fits the existing project, is small, and is the natural "verified B0"
   to run on the laptop now.

> **Recommended order:** do (3) now on the laptop (cheap, in-project, gives a
> verified B0), then decide (1) vs (2) for B3 as a separate question — don't
> let the Mathlib decision block B0.

### (3) stated precisely, for the laptop to verify

The B0 core, abstracted away from PA so it needs no proof theory, is:

> Given a finite list `Φ : List α` (the length-`≤ n` formula representatives),
> a partial map `name : α → Option ℕ` (Lemma 1 gives that it is
> well-defined per formula), the set of values
> `{ k : ∃ φ ∈ Φ, name φ = some k }` is finite and, if nonempty, has a
> maximum.

In the self-contained `rayo-lean` style (Lean 4 core `List`, no Mathlib) this
is a `List.filterMap name Φ` fact about a hand-rolled `natListMax` (Lean 4
core has no `List.maximum?` without Mathlib/Std, so a five-line fold-based
version was written instead). It is a handful of lines and carries the whole
mathematical content of the well-definedness gate.

**Done, on the laptop, 2026-08-07 — `rayo-lean/Rayo/BoolosB0Core.lean`.**
`Rayo.exists_max_of_finite_naming` states and proves exactly the boxed claim
above (`Φ.filterMap name = [] ∨ ∃ m, (∃ φ ∈ Φ, name φ = some m) ∧ ∀ φ ∈ Φ, ∀
v, name φ = some v → v ≤ m` — finite-or-has-a-genuine-maximum, not merely an
upper bound). `lake build` is clean from `lake clean` (15/15 modules,
including this one); no `sorry`, no `admit`; `#print axioms` on all three
theorems in the file (`exists_max_of_finite_naming`,
`le_of_mem_natListMax`, `mem_of_natListMax_eq_some`) shows only `propext`
(plus `Quot.sound` on two of the three) — the same bar as K0-K6 and
`Encoding.lean`, no `Classical.choice`, no `sorryAx`. The B0 gate is now
machine-verified, not just paper-proved.

### The T-names predicate, for if/when B1 (option 1) proceeds

Building on `Foundation`, the object of B1 is
```
    TNames (φ k) :=  Prov_T  ⌜ ∀x ( φ(x) ↔ x = numeral k ) ⌝
```
using `Foundation`'s internal coding `⌜·⌝`, its provability predicate
`Prov_T`, and its numeral term — then B3's diagonal step is an application of
`Bootstrapping/FixedPoint.lean` (`T ⊢ fixedpoint θ ↔ θ/[⌜fixedpoint θ⌝]`) to
the predicate "names a value larger than anything a shorter formula names."
Check first whether `Foundation` already has a "formula names a unique value"
notion to adapt, before writing this from scratch (`BOOLOS-FUNCTION-PLAN.md`
B1).

---

## 8. Summary

- **B0 gate: PASSED.** `BoolosBig_PA(n)` is a well-defined `ℕ` for every `n`
  (§3), monotone in `n`. Rayo's skipped step is now discharged for the PA
  provability version.
- **Two load-bearing hypotheses, both named:** (H1) consistency of T
  (= `BN-function.md` A4), used for functionality; (H2) counting formulas up
  to α-equivalence, used for finiteness — the latter *not* in A1–A5 and the
  genuine finding (§4), because the project's "variables are free" convention
  makes the raw formula set infinite.
- **One correction to the plan (§5):** the provability swap is needed for
  *internalization/diagonalization* (Stage 2/3, Tarski), **not** for B0's
  well-definedness, which closes for the truth reading too. Provability is
  still the right choice — it is the internalizable and the approximable one.
- **Scope settled (§6): pursue B3 (growth-class domination, `≈ ε₀` via
  provability-diagonalization), drop B2** (a small-n PA table shows nothing —
  PA has numerals). B3 gives Phase 4 a genuinely new data point.
- **Lean handoff (§7):** blocked in this remote env by egress policy; do the
  self-contained verified-B0-core on the laptop now; treat Mathlib+Foundation
  as a separate greenlight for a machine-checked B3.
