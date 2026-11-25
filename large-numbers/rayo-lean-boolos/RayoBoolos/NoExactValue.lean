/-
`RayoBoolos.NoExactValue`: what a theory can prove about its own naming
function (`PROVABLE-NAMING-REPORT.md` §6, Theorem 8).

The arithmetic sentences "`Big_T(n) ≤ k`" (`bigLe`), "`Big_T(n) ≥ k`"
(`bigGe`) and "`Big_T(n) = k`" (`bigEq`) list the finitely many formulas of
size at most `n` outside the theory (size is not arithmetized) and use
`Foundation`'s standard provability predicate and its Σ₁ graph of numeral
substitution. `bigLe_true_iff` and `bigGe_true_iff` check that they mean
what they should in `ℕ`.

For consistent, computably axiomatized `T ⊇ 𝗜𝚺₁`:
* `provable_bigGe`: every true lower bound is provable (Σ₁ completeness);
* `not_provable_bigLe`: for `n ≥ 1`, `T` proves no upper bound at all, since
  an upper bound implies that one fixed sentence is unprovable, which
  implies `Con(T)` inside `𝗜𝚺₁`, against Gödel's second theorem;
* `not_provable_bigEq`: hence no exact value.
-/

module

public import RayoBoolos.UpperBound

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic
open Bootstrapping Bootstrapping.Arithmetic

section
variable (T : ArithmeticTheory) [T.Δ₁]

/-- `upperF(c, k)`: for every `m`, if `T` proves `N(m̄)` (where `c` codes `N`), then `m ≤ k`. -/
noncomputable def upperF : 𝚷₁.Semisentence 2 := .mkPi
  “c k. ∀ m, ∀ y, !ssnum y c m → !(provable T) y → m ≤ k”

/-- `lowerF(c, k)`: for some `m ≥ k`, `T` proves `N(m̄)` (where `c` codes `N`). -/
noncomputable def lowerF : 𝚺₁.Semisentence 2 := .mkSigma
  “c k. ∃ m, ∃ y, k ≤ m ∧ !ssnum y c m ∧ !(provable T) y”

/-- The formulas with one free variable and size at most `n`. -/
noncomputable def formsFin (n : ℕ) : Finset (ArithmeticSemisentence 1) :=
  (formsUpTo_finite n 1).toFinset

/-- The arithmetic sentence "`Big_T(n) ≤ k`". -/
noncomputable def bigLe (n k : ℕ) : ArithmeticSentence :=
  (formsFin n).conj' fun φ => (upperF T).val/[⌜nameTemplate φ⌝, ↑k]

/-- The arithmetic sentence "`Big_T(n) ≥ k`" (some formula of size `≤ n` names a number `≥ k`). -/
noncomputable def bigGe (n k : ℕ) : ArithmeticSentence :=
  (formsFin n).disj' fun φ => (lowerF T).val/[⌜nameTemplate φ⌝, ↑k]

/-- The arithmetic sentence "`Big_T(n) = k`". -/
noncomputable def bigEq (n k : ℕ) : ArithmeticSentence := bigGe T n k ⋏ bigLe T n k

end

section semantics
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : ArithmeticTheory) [T.Δ₁]

lemma substNumeral_quote_nat (N : ArithmeticSemisentence 1) (m : ℕ) :
    substNumeral (⌜N⌝ : V) (m : V) = ⌜(N/[↑m] : ArithmeticSentence)⌝ := by
  simp [substNumeral, Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_coe₁]

lemma eval_upperF (c k : V) :
    (upperF T).val.Evalb (M := V) ![c, k] ↔ ∀ m : V, Provable T (substNumeral c m) → m ≤ k := by
  simp [upperF]

lemma eval_lowerF (c k : V) :
    (lowerF T).val.Evalb (M := V) ![c, k] ↔ ∃ m : V, k ≤ m ∧ Provable T (substNumeral c m) := by
  simp [lowerF]

lemma models_subst2 (θ : ArithmeticSemisentence 2) (N : ArithmeticSemisentence 1) (k : ℕ) :
    V↓[ℒₒᵣ] ⊧ (θ/[⌜N⌝, ↑k] : ArithmeticSentence) ↔ θ.Evalb (M := V) ![⌜N⌝, (k : V)] := by
  simp [models_iff, Semiformula.eval_substs, numeral_eq_natCast]

lemma models_upper (N : ArithmeticSemisentence 1) (k : ℕ) :
    V↓[ℒₒᵣ] ⊧ ((upperF T).val/[⌜N⌝, ↑k] : ArithmeticSentence) ↔
      ∀ m : V, Provable T (substNumeral ⌜N⌝ m) → m ≤ k := by
  rw [models_subst2, eval_upperF]

lemma models_lower (N : ArithmeticSemisentence 1) (k : ℕ) :
    V↓[ℒₒᵣ] ⊧ ((lowerF T).val/[⌜N⌝, ↑k] : ArithmeticSentence) ↔
      ∃ m : V, k ≤ m ∧ Provable T (substNumeral ⌜N⌝ m) := by
  rw [models_subst2, eval_lowerF]

lemma models_bigLe (n k : ℕ) :
    V↓[ℒₒᵣ] ⊧ bigLe T n k ↔ ∀ φ ∈ formsFin n,
      ∀ m : V, Provable T (substNumeral ⌜nameTemplate φ⌝ m) → m ≤ k := by
  have : ∀ φ, V↓[ℒₒᵣ] ⊧ ((upperF T).val/[⌜nameTemplate φ⌝, ↑k] : ArithmeticSentence) ↔ _ :=
    fun φ => models_upper T (nameTemplate φ) k
  simp only [bigLe, models_iff] at this ⊢
  simp [this]

lemma models_bigGe (n k : ℕ) :
    V↓[ℒₒᵣ] ⊧ bigGe T n k ↔ ∃ φ ∈ formsFin n,
      ∃ m : V, k ≤ m ∧ Provable T (substNumeral ⌜nameTemplate φ⌝ m) := by
  have : ∀ φ, V↓[ℒₒᵣ] ⊧ ((lowerF T).val/[⌜nameTemplate φ⌝, ↑k] : ArithmeticSentence) ↔ _ :=
    fun φ => models_lower T (nameTemplate φ) k
  simp only [bigGe, models_iff] at this ⊢
  simp [this]

end semantics

section main
variable (T : ArithmeticTheory) [T.Δ₁]

lemma provable_template_iff [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSemisentence 1) (m : ℕ) :
    Provable T (substNumeral (⌜nameTemplate φ⌝ : ℕ) m) ↔ NamesIn T φ m := by
  have h := substNumeral_quote_nat (V := ℕ) (nameTemplate φ) m
  simp only [natCast_nat] at h
  rw [h, provable_iff_provable, template_iff]

lemma mem_formsFin {n : ℕ} {φ : ArithmeticSemisentence 1} : φ ∈ formsFin n ↔ fSize φ ≤ n := by
  simp [formsFin]

/-- The sentence `bigLe T n k` is true exactly when `Big_T(n) ≤ k`. -/
theorem bigLe_true_iff [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (n k : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ bigLe T n k ↔ BoolosBigIn T n ≤ k := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance
  rw [models_bigLe]
  simp only [natCast_nat, provable_template_iff, mem_formsFin]
  constructor
  · intro h
    apply BoolosBigIn_le
    rintro v ⟨φ, hφ, hv⟩
    have := le_def.mp (h φ hφ v hv)
    omega
  · intro h φ hφ m hm
    have := le_trans (le_BoolosBigIn ⟨φ, hφ, hm⟩) h
    rw [le_def]
    omega

/-- The sentence `bigGe T n k` is true exactly when some formula of size at
most `n` names a number `≥ k` in `T` (for `k ≥ 1` this is `Big_T(n) ≥ k`). -/
theorem bigGe_true_iff [𝗣𝗔⁻ ⪯ T] (n k : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ bigGe T n k ↔ ∃ v ∈ namedValuesIn T n, k ≤ v := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance
  rw [models_bigGe]
  simp only [natCast_nat, provable_template_iff, mem_formsFin]
  constructor
  · rintro ⟨φ, hφ, m, hkm, hm⟩
    exact ⟨m, ⟨φ, hφ, hm⟩, (by rcases le_def.mp hkm with e | e <;> [exact e ▸ Nat.le_refl k; exact Nat.le_of_lt e])⟩
  · rintro ⟨v, ⟨φ, hφ, hv⟩, hkv⟩
    exact ⟨φ, hφ, v, by rw [le_def]; omega, hv⟩

lemma bigGe_sigma1 (n k : ℕ) : Hierarchy 𝚺 1 (bigGe T n k) := by
  simp only [bigGe, Hierarchy.finset_disj'_iff]
  intro φ _
  exact Hierarchy.rew _ (lowerF T).sigma_prop

/-- **Theorem 8(a).** Every true lower bound on `Big_T(n)` is provable in `T`. -/
theorem provable_bigGe [𝗜𝚺₁ ⪯ T] {n k : ℕ} (h : ∃ v ∈ namedValuesIn T n, k ≤ v) :
    T ⊢ bigGe T n k := by
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  exact sigma_one_completeness (bigGe_sigma1 T n k) ((bigGe_true_iff T n k).mpr h)

/-- **Theorem 8(b), strong form.** A consistent, computably axiomatized
`T ⊇ 𝗜𝚺₁` proves no upper bound at all on its own naming function. -/
theorem not_provable_bigLe [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T] {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) : T ⊬ bigLe T n k := by
  intro h
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ (𝗜𝚺₁ : ArithmeticTheory)) inferInstance
  let σ : ArithmeticSentence := (nameTemplate ⊤)/[↑(k + 1)]
  have h1 : T ⊢ bigLe T n k 🡒 ∼provabilityPred T σ := by
    apply Arithmetic.complete.{0} T
    intro M _ hM
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory hM
    have key := (models_bigLe (V := M) T n k)
    simp only [models_iff] at key ⊢
    rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg]
    intro hle hprov
    have hm := (key.mp hle) ⊤ (mem_formsFin.mpr (by simp [fSize]; omega)) ((k + 1 : ℕ) : M)
    rw [substNumeral_quote_nat] at hm
    have := hm (by simpa using hprov)
    simp at this
  have h2 : T ⊢ ∼provabilityPred T σ 🡒 T.consistent.val :=
    Entailment.WeakerThan.pbl
      (ProvabilityAbstraction.formalized_consistent_of_existance_unprovable
        (𝔅 := T.standardProvability) (σ := σ))
  exact consistent_unprovable T (h2 ⨀ (h1 ⨀ h))

/-- **Theorem 8(b).** `T` proves no exact value `Big_T(n) = k`. -/
theorem not_provable_bigEq [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T] {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) : T ⊬ bigEq T n k := fun h =>
  not_provable_bigLe T hn k (Entailment.K!_right h)

end main

end RayoBoolos

#print axioms RayoBoolos.bigLe_true_iff
#print axioms RayoBoolos.bigGe_true_iff
#print axioms RayoBoolos.provable_bigGe
#print axioms RayoBoolos.not_provable_bigLe
#print axioms RayoBoolos.not_provable_bigEq
