/-
`RayoBoolos.Decided`: sets a theory decides, and the upper half of the
general naming theorem (`GENERAL-NAMING-THEOREM.md` §4, Theorem 3).

* `DecidesIn T Θ A`: for every `i`, `T ⊢ Θ(ī)` if `i ∈ A` and `T ⊢ ¬Θ(ī)` if
  `i ∉ A` (`Θ` strongly represents `A` in `T`).
* `DecidesIn.unique`: a consistent `T ⊇ 𝗣𝗔⁻` decides at most one set with a
  given formula.
* `namesIn_decides_singleton`: if `φ` `T`-names `m`, then `φ` decides `{m}`
  in `T`. This is the step that bounds the naming function by Busy Beaver
  over decided oracles: the fixed program "ask 0, 1, 2, … until yes" runs at
  least `m` steps with oracle `{m}`.
-/

module

public import RayoBoolos.AnyTheory

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-- The sentence `Θ(ī)`. -/
noncomputable def instAt (Θ : ArithmeticSemisentence 1) (i : ℕ) : ArithmeticSentence :=
  “!Θ !!(Semiterm.numeral i)”

/-- `Θ` decides `A` in `T`. -/
def DecidesIn (T : ArithmeticTheory) (Θ : ArithmeticSemisentence 1) (A : Set ℕ) : Prop :=
  ∀ i : ℕ, (i ∈ A → T ⊢ instAt Θ i) ∧ (i ∉ A → T ⊢ ∼instAt Θ i)

lemma inconsistent_of_both {T : ArithmeticTheory} [Entailment.Consistent T]
    {σ : ArithmeticSentence} (h1 : T ⊢ σ) (h2 : T ⊢ ∼σ) : False :=
  (Entailment.not_inconsistent_iff_consistent.mpr inferInstance)
    (Entailment.inconsistent_of_provable_of_unprovable h1 h2)

/-- With a fixed formula, a consistent theory decides at most one set. -/
theorem DecidesIn.unique {T : ArithmeticTheory} [Entailment.Consistent T]
    {Θ : ArithmeticSemisentence 1} {A B : Set ℕ}
    (hA : DecidesIn T Θ A) (hB : DecidesIn T Θ B) : A = B := by
  ext i
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp only [ha, hb]
  · exact (inconsistent_of_both ((hA i).1 ha) ((hB i).2 hb)).elim
  · exact (inconsistent_of_both ((hB i).1 hb) ((hA i).2 ha)).elim

/-- **Theorem 3, first half.** A `T`-name of `m` decides `{m}` in `T`. -/
theorem namesIn_decides_singleton {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T]
    {φ : ArithmeticSemisentence 1} {m : ℕ} (h : NamesIn T φ m) :
    DecidesIn T φ {m} := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance
  intro i
  constructor
  · intro hi
    apply Arithmetic.complete.{0} T _ (fun (M : Type) _ hM ↦ ?_)
    have hm : M↓[ℒₒᵣ] ⊧ namesSentence φ m := models_of_provable hM h
    simp [namesSentence, models_iff] at hm
    simp only [Set.mem_singleton_iff] at hi
    subst hi
    simp [instAt, models_iff]
    exact (hm _).mpr rfl
  · intro hi
    apply Arithmetic.complete.{0} T _ (fun (M : Type) _ hM ↦ ?_)
    haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hM
    have hm : M↓[ℒₒᵣ] ⊧ namesSentence φ m := models_of_provable hM h
    simp [namesSentence, models_iff] at hm
    simp only [Set.mem_singleton_iff] at hi
    simp [instAt, models_iff]
    intro hφ
    have := (hm _).mp hφ
    exact hi (by simpa [numeral_eq_natCast] using this)

#print axioms namesIn_decides_singleton
#print axioms DecidesIn.unique

end RayoBoolos
