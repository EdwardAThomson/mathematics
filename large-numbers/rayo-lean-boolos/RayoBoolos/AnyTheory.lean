/-
`RayoBoolos.AnyTheory`: the choice of axioms does not matter for the lower
bound.

Everything in `Minimization.lean` and `Binary.lean` was stated for `𝗣𝗔`. The
proofs only ever used `𝗣𝗔⁻` (the finitely many basic axioms of ordered
semirings, with no induction at all). This file makes that explicit.

* `NamesIn T φ k` is `T ⊢ ∀x (φ(x) ↔ x = k̄)` for an arbitrary theory `T`.
* `logName_namesIn_base`: the short naming formulas already work in `𝗣𝗔⁻`.
* `NamesIn.unique`: a consistent `T ⊇ 𝗣𝗔⁻` names at most one value per
  formula. Soundness is not needed, only consistency.
* `BoolosBigIn T`: the provable-naming function of `T`.
* `BoolosBigIn_log_bound`: for every computable `f` there is ONE constant `C`
  such that `f n ≤ BoolosBigIn T (C + 6·log₂ n)` for every consistent
  `T ⊇ 𝗣𝗔⁻` and every `n`. The constant does not depend on `T`.
* `BoolosBigIn_mono_theory`: a stronger theory names at least as much.
* `BoolosBigIn_dominates_computable`, `BoolosBigIn_not_computable`: every
  one of these functions eventually dominates every computable function, and
  none is computable.
-/

module

public import RayoBoolos.Binary

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-- `φ` `T`-names `k`: `T ⊢ ∀x (φ(x) ↔ x = k̄)`. -/
def NamesIn (T : ArithmeticTheory) (φ : ArithmeticSemisentence 1) (k : ℕ) : Prop :=
  T ⊢ namesSentence φ k

theorem namesIn_PA_iff (φ : ArithmeticSemisentence 1) (k : ℕ) :
    NamesIn 𝗣𝗔 φ k ↔ TNamesMeta φ k := Iff.rfl

/-- Naming is preserved by strengthening the theory. -/
theorem NamesIn.mono {T U : ArithmeticTheory} [T ⪯ U] {φ : ArithmeticSemisentence 1} {k : ℕ}
    (h : NamesIn T φ k) : NamesIn U φ k :=
  Entailment.WeakerThan.pbl h

/-- `minGraph_names`, in the base theory `𝗣𝗔⁻`. -/
theorem minGraph_namesIn_base {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {f : ℕ → ℕ}
    (hf : ∀ y x : ℕ, θ.Evalb (M := ℕ) ![y, x] ↔ y = f x) (n : ℕ) :
    NamesIn 𝗣𝗔⁻ (minGraph θ ⇜ ![#0, Semiterm.numeral n]) (f n) := by
  have h2 : (𝗣𝗔⁻ : ArithmeticTheory) ⊢
      (minGraph θ ⇜ ![Semiterm.numeral (f n), Semiterm.numeral n]) := by
    have h := (sigma_one_completeness_iff_param (T := (𝗣𝗔⁻ : ArithmeticTheory))
      (minGraph_sigma1 hθ) (e := ![f n, n])).mp (minGraph_true hθ hf n)
    have heq : (fun x => (Semiterm.Operator.numeral ℒₒᵣ (![f n, n] x) : Semiterm ℒₒᵣ Empty 0))
        = (![Semiterm.numeral (f n), Semiterm.numeral n] : Fin 2 → Semiterm ℒₒᵣ Empty 0) := by
      funext x
      cases x using Fin.cases with
      | zero => rfl
      | succ x => cases x using Fin.cases with
        | zero => rfl
        | succ x => exact x.elim0
    rwa [heq] at h
  unfold NamesIn namesSentence
  apply Arithmetic.complete.{0} (𝗣𝗔⁻ : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  have hw : M↓[ℒₒᵣ] ⊧ (minGraph θ ⇜ ![Semiterm.numeral (f n), Semiterm.numeral n]) :=
    models_of_provable hM h2
  simp [models_iff] at hw ⊢
  intro x
  constructor
  · intro hx
    exact minGraph_unique θ hx hw
  · rintro rfl
    exact hw

/-- `logName_names`, in the base theory `𝗣𝗔⁻`. -/
theorem logName_namesIn_base {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {f : ℕ → ℕ}
    (hf : ∀ y x : ℕ, θ.Evalb (M := ℕ) ![y, x] ↔ y = f x) (n : ℕ) :
    NamesIn 𝗣𝗔⁻ (logName θ n) (f n) := by
  have hN := minGraph_namesIn_base hθ hf n
  unfold NamesIn namesSentence at hN ⊢
  apply Arithmetic.complete.{0} (𝗣𝗔⁻ : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  have hw := models_of_provable hM hN
  simp [models_iff] at hw
  simp [models_iff]
  intro x
  rw [eval_logName]
  exact hw x

/-- A consistent theory containing `𝗣𝗔⁻` names at most one value per formula.
Only consistency is used, not soundness. -/
theorem NamesIn.unique {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    {φ : ArithmeticSemisentence 1} {k1 k2 : ℕ}
    (h1 : NamesIn T φ k1) (h2 : NamesIn T φ k2) : k1 = k2 := by
  by_contra hne
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance
  have hbot : T ⊢ (⊥ : ArithmeticSentence) := by
    apply Arithmetic.complete.{0} T _ (fun (M : Type) _ hM ↦ ?_)
    haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hM
    have hm1 : M↓[ℒₒᵣ] ⊧ namesSentence φ k1 := models_of_provable hM h1
    have hm2 : M↓[ℒₒᵣ] ⊧ namesSentence φ k2 := models_of_provable hM h2
    simp [namesSentence, models_iff] at hm1 hm2
    have e1 := (hm1 (ORingStructure.numeral k1)).mpr rfl
    have := (hm2 _).mp e1
    exact absurd (by simpa [numeral_eq_natCast] using this) hne
  exact (Entailment.not_inconsistent_iff_consistent.mpr inferInstance)
    (Entailment.inconsistent_iff_provable_bot.mpr hbot)

/-- The values `T` can name with a formula of size at most `n`. -/
def namedValuesIn (T : ArithmeticTheory) (n : ℕ) : Set ℕ :=
  {k | ∃ φ : ArithmeticSemisentence 1, fSize φ ≤ n ∧ NamesIn T φ k}

theorem namedValuesIn_finite (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (n : ℕ) :
    (namedValuesIn T n).Finite := by
  have hcover : namedValuesIn T n ⊆
      ⋃ φ ∈ {φ : ArithmeticSemisentence 1 | fSize φ ≤ n}, {k | NamesIn T φ k} := by
    rintro k ⟨φ, hφ, hk⟩
    exact Set.mem_biUnion hφ hk
  apply Set.Finite.subset _ hcover
  apply Set.Finite.biUnion (formsUpTo_finite n 1)
  intro φ _
  rcases Set.eq_empty_or_nonempty {k | NamesIn T φ k} with he | ⟨k0, hk0⟩
  · rw [he]; exact Set.finite_empty
  · have : {k | NamesIn T φ k} = {k0} := by
      ext k; constructor
      · intro hk; exact NamesIn.unique hk hk0
      · rintro rfl; exact hk0
    rw [this]; exact Set.finite_singleton _

open Classical in
/-- The provable-naming function of an arbitrary theory `T`: the largest
number `T` can name with a formula of size at most `n`. (Defined as `0` in
the degenerate case that the set of named values is infinite, which cannot
happen for a consistent `T ⊇ 𝗣𝗔⁻`.) -/
noncomputable def BoolosBigIn (T : ArithmeticTheory) (n : ℕ) : ℕ :=
  if h : (namedValuesIn T n).Finite then h.toFinset.sup id else 0

theorem le_BoolosBigIn {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] {n k : ℕ}
    (hk : k ∈ namedValuesIn T n) : k ≤ BoolosBigIn T n := by
  unfold BoolosBigIn
  rw [dif_pos (namedValuesIn_finite T n)]
  apply Finset.le_sup (f := id)
  exact (Set.Finite.mem_toFinset _).mpr hk

/-- If every value `T` names within budget `n` is at most `b`, then
`BoolosBigIn T n ≤ b`. -/
theorem BoolosBigIn_le {T : ArithmeticTheory} {n b : ℕ}
    (h : ∀ k ∈ namedValuesIn T n, k ≤ b) : BoolosBigIn T n ≤ b := by
  unfold BoolosBigIn
  split
  · apply Finset.sup_le
    intro k hk
    exact h k ((Set.Finite.mem_toFinset _).mp hk)
  · exact Nat.zero_le _

/-- For `T = 𝗣𝗔` this is the function studied in the rest of the project. -/
theorem BoolosBigIn_PA (n : ℕ) : BoolosBigIn 𝗣𝗔 n = BoolosBig_PA n := by
  apply le_antisymm
  · exact BoolosBigIn_le fun k hk => namedValues_le_BoolosBig_PA hk
  · unfold BoolosBig_PA
    apply Finset.sup_le
    intro k hk
    exact le_BoolosBigIn (T := 𝗣𝗔) ((Set.Finite.mem_toFinset _).mp hk)

/-- **Stronger axioms never name less.** -/
theorem BoolosBigIn_mono_theory {T U : ArithmeticTheory} [T ⪯ U] [𝗣𝗔⁻ ⪯ U]
    [Entailment.Consistent U] (n : ℕ) : BoolosBigIn T n ≤ BoolosBigIn U n := by
  apply BoolosBigIn_le
  rintro k ⟨φ, hφ, hk⟩
  exact le_BoolosBigIn ⟨φ, hφ, hk.mono⟩

/-- **The lower bound does not depend on the axioms.** For every computable
`f` there is one constant `C`, the same for all theories, such that every
consistent `T ⊇ 𝗣𝗔⁻` names a number `≥ f n` within budget `C + 6·log₂ n`. -/
theorem BoolosBigIn_log_bound {f : ℕ → ℕ} (hf : Computable f) :
    ∃ C, ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
      ∀ n, f n ≤ BoolosBigIn T (C + 6 * Nat.log2 n) := by
  obtain ⟨θ, hθ, hθf⟩ := computable_graph hf
  refine ⟨fSize (minGraph θ) + 5, fun T _ _ n => ?_⟩
  exact le_BoolosBigIn ⟨logName θ n, fSize_logName_le θ n, (logName_namesIn_base hθ hθf n).mono⟩

/-- More budget never names less. -/
theorem BoolosBigIn_mono {T : ArithmeticTheory} [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] {n m : ℕ}
    (h : n ≤ m) : BoolosBigIn T n ≤ BoolosBigIn T m := by
  apply BoolosBigIn_le
  rintro k ⟨φ, hφ, hk⟩
  exact le_BoolosBigIn ⟨φ, hφ.trans h, hk⟩

lemma twelve_log2_le (m : ℕ) : 12 * Nat.log2 m ≤ m + 64 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 24 with hlt | hge
    · rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; simp [Nat.log2_def]
      · have : Nat.log2 m < 5 := (Nat.log2_lt (by omega)).mpr (by omega)
        omega
    · have hlog : Nat.log2 m = Nat.log2 (m / 2) + 1 := by
        rw [Nat.log2_def]; simp [show 2 ≤ m by omega]
      have := ih (m / 2) (by omega)
      omega

/-- **Every consistent `T ⊇ 𝗣𝗔⁻` has a provable-naming function that
eventually dominates every computable function.** The threshold `N` does not
depend on `T`. -/
theorem BoolosBigIn_dominates_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ N, ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
      ∀ m > N, f m ≤ BoolosBigIn T m := by
  obtain ⟨C, hC⟩ := BoolosBigIn_log_bound (runMax_computable hf)
  refine ⟨2 * C + 64, fun T _ _ m hm => ?_⟩
  have h12 := twelve_log2_le m
  calc f m ≤ runMax f m := le_runMax f (le_refl m)
    _ ≤ BoolosBigIn T (C + 6 * Nat.log2 m) := hC T m
    _ ≤ BoolosBigIn T m := BoolosBigIn_mono (by omega)

/-- **No consistent `T ⊇ 𝗣𝗔⁻` has a computable provable-naming function.** -/
theorem BoolosBigIn_not_computable (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    ¬ Computable (BoolosBigIn T) := by
  intro h
  have h1 : Computable (fun n => BoolosBigIn T n + 1) := Computable.succ.comp h
  obtain ⟨N, hN⟩ := BoolosBigIn_dominates_computable h1
  have := hN T (N + 1) (Nat.lt_succ_self N)
  omega

end RayoBoolos

#print axioms RayoBoolos.NamesIn.unique
#print axioms RayoBoolos.BoolosBigIn_PA
#print axioms RayoBoolos.BoolosBigIn_mono_theory
#print axioms RayoBoolos.BoolosBigIn_log_bound
#print axioms RayoBoolos.BoolosBigIn_dominates_computable
#print axioms RayoBoolos.BoolosBigIn_not_computable
