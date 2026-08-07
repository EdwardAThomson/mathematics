/-
`RayoBoolos.TNames` — Phase B1 of `BOOLOS-FUNCTION-PLAN.md`: formalize the
`T-names` predicate from `BOOLOS-B0-WELLDEFINEDNESS.md` §1 using
`FormalizedFormalLogic/Foundation`'s internal Gödel coding and provability
predicate, over `T = 𝗣𝗔` (full Peano arithmetic, `Foundation`'s `𝗣𝗔`).

Recall the paper definition (`BOOLOS-B0-WELLDEFINEDNESS.md` §1):

    φ T-names k   iff   T ⊢ ∀x (φ(x) ↔ x = k̄)

`Foundation` gives us, ready-made:
  - `ArithmeticSemisentence 1`  — a formula in the language of arithmetic
    (`ℒₒᵣ = {0, S, +, ×, =, <}`) with exactly one free variable, matching
    `BOOLOS-B0-WELLDEFINEDNESS.md`'s φ exactly (same fixed language, same
    "one free variable" shape).
  - `Semiterm.numeral k`        — the canonical numeral k̄, a closed term.
  - `𝗣𝗔`                        — the theory (`Peano`, with induction for
    every formula — matches the paper's "T = PA").
  - `T ⊢ σ`                     — `Foundation`'s (meta-level) provability
    relation, used below to state and prove the *paper* T-naming fact.
  - `Arithmetic.provabilityPred T σ : ArithmeticSentence` — the *internal*,
    object-language provability predicate (`Bootstrapping/Syntax/Proof/
    Basic.lean`): a genuine formula of `ℒₒᵣ` expressing "T proves σ",
    built from `Foundation`'s Σ₁ proof-search/coding machinery. This is
    what makes `TNames` below an object-language-expressible predicate,
    not a meta-level `Prop` — the internality `BOOLOS-B0-WELLDEFINEDNESS.md`
    §5 says the diagonal step needs.

Two formalizations of "T-names" are given, matching the two roles the plan
needs:

  - `namesSentence φ k : ArithmeticSentence`  — the *statement*
    `∀x(φ(x) ↔ x = k̄)`, an ordinary object-language sentence.
  - `TNames φ k : ArithmeticSentence`         — `provabilityPred 𝗣𝗔
    (namesSentence φ k)`, i.e. `Prov_𝗣𝗔(⌜∀x(φ(x) ↔ x=k̄)⌝)` — *also* an
    object-language sentence (this is the point: the "names" relation
    itself, not just its object, lives inside the language, so it can be
    diagonalized against in Stage 2/B3).
  - `TNamesMeta φ k : Prop := 𝗣𝗔 ⊢ namesSentence φ k` — the meta-level
    provability fact used to state and prove B0-style lemmas (functionality,
    the well-definedness combination) about the *paper* construction; tied
    back to `TNames` by `tNames_iff_provable` below via `Foundation`'s own
    soundness/completeness bridge (`provable_sound` in the standard-
    provability derivation-condition file), so nothing here is a
    reformulation that quietly drops internality — `TNames` is the real
    internal predicate, `TNamesMeta` is just its provability-in-the-
    metatheory reading, proved equivalent to `ℕ ⊨ TNames φ k` below.
-/

module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping

/-- The paper's `∀x(φ(x) ↔ x = k̄)` sentence, `BOOLOS-B0-WELLDEFINEDNESS.md`
Definition (T-names), spelled out as an object-language `ArithmeticSentence`
of `Foundation`'s `ℒₒᵣ`. -/
noncomputable def namesSentence (φ : ArithmeticSemisentence 1) (k : ℕ) : ArithmeticSentence :=
  “∀ x, !φ x ↔ x = !!(Semiterm.numeral k)”

/-- **`TNames`, internal.** `BOOLOS-FUNCTION-PLAN.md` Phase B1 /
`BOOLOS-B0-WELLDEFINEDNESS.md` §7: `TNames(φ, k) := Prov_T ⌜∀x(φ(x) ↔
x=k̄)⌝`, cashed out concretely as `Foundation`'s internal
`provabilityPred`. This is itself an `ArithmeticSentence` — an
object-language formula, not a meta-level `Prop` — which is the whole
point: it can be substituted into, quantified over, and diagonalized
against exactly like any other formula of `ℒₒᵣ`. -/
noncomputable def TNames (φ : ArithmeticSemisentence 1) (k : ℕ) : ArithmeticSentence :=
  provabilityPred 𝗣𝗔 (namesSentence φ k)

/-- The paper-level (meta) reading of T-names: `T ⊢ ∀x(φ(x) ↔ x=k̄)`,
exactly `BOOLOS-B0-WELLDEFINEDNESS.md`'s Definition (T-names) with
`T = 𝗣𝗔`. Used to restate and re-prove the B0 lemmas (Lemma 1
functionality, in `TNamesFunctional.lean`) about the concrete PA
instance, on top of the abstract combinatorial core already verified in
`rayo-lean/Rayo/BoolosB0Core.lean`. -/
def TNamesMeta (φ : ArithmeticSemisentence 1) (k : ℕ) : Prop :=
  𝗣𝗔 ⊢ namesSentence φ k

/-- The internal predicate `TNames φ k` and the meta-level provability fact
`TNamesMeta φ k` agree on standard truth: `TNames φ k` is true in the
standard model iff `𝗣𝗔` really does prove `namesSentence φ k`. This is
`Foundation`'s `standardProvability` soundness/completeness
(`provable_complete`, `Bootstrapping/DerivabilityCondition/PeanoMinus.lean`)
specialized to `T = 𝗣𝗔`, and it is what licenses treating the internal
`TNames` formula as "the same fact" as the paper's `T-names` relation
rather than a look-alike. -/
theorem tNames_iff_provable (φ : ArithmeticSemisentence 1) (k : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ TNames φ k ↔ TNamesMeta φ k := by
  unfold TNames TNamesMeta
  constructor
  · intro h
    simpa [models_iff] using h
  · intro h
    have hp : (𝗜𝚺₁ : ArithmeticTheory) ⊢ provabilityPred 𝗣𝗔 (namesSentence φ k) :=
      provable_D1 h
    have hmod : ℕ↓[ℒₒᵣ] ⊧* (𝗜𝚺₁ : ArithmeticTheory) := inferInstance
    exact models_of_provable hmod hp

end RayoBoolos

#print axioms RayoBoolos.namesSentence
#print axioms RayoBoolos.TNames
#print axioms RayoBoolos.tNames_iff_provable
