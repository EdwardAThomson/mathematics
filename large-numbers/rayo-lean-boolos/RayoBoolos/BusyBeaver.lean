/-
`RayoBoolos.BusyBeaver`: the Busy Beaver lower bound, for every theory.

`Minimization.lean` and `Binary.lean` name the values of *total* computable
functions. Nothing in the argument needs totality. If a program halts on an
input, its output can be named cheaply, because the naming formula only has
to be confirmed at that one input. This file proves that, and reads off the
lower half of the Busy Beaver sandwich.

* `partrec_graph`: every partial recursive function has a `Σ₁` graph.
* `logName_namesIn_partial`: if `θ` is `Σ₁`, single-valued in `ℕ`, and true
  at `(v, n)`, then `logName θ n` names `v` already in `𝗣𝗔⁻`.
* `BoolosBigIn_partrec_bound`: for every partial recursive `g` there is one
  constant `C` such that every value `v ∈ g n` satisfies
  `v ≤ BoolosBigIn T (C + 6·log₂ n)`, for every consistent `T ⊇ 𝗣𝗔⁻`.
* `BB N`: the largest output of any halting program with code number `≤ N`
  (Mathlib's `Nat.Partrec.Code`, run on input `0`). `BBtime N`: the largest
  halting time of such a program.
* `BB_le_BoolosBigIn`, `BBtime_le_BoolosBigIn`:
  `BB N ≤ BoolosBigIn T (C + 6·log₂ N)`, and likewise for halting times.

Since `log₂ N` is the length in bits of a program with code number `N`, the
last statement reads: a program of `s` bits that halts produces a number that
`T` can name in about `6·s` symbols.
-/

module

public import RayoBoolos.AnyTheory

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Naming a single value of a partial function -/

/-- Every partial recursive function has a `Σ₁` graph formula, correct in `ℕ`. -/
lemma partrec_graph {g : ℕ →. ℕ} (hg : Partrec g) :
    ∃ θ : ArithmeticSemisentence 2, Hierarchy 𝚺 1 θ ∧
      ∀ y x : ℕ, θ.Evalb (M := ℕ) ![y, x] ↔ y ∈ g x := by
  let F : List.Vector ℕ 1 →. ℕ := fun v ↦ g (v.get 0)
  have hF : Partrec F := by
    change Partrec fun v : List.Vector ℕ 1 ↦ g (v.get 0)
    exact hg.comp (Primrec.to_comp <| Primrec.vector_get.comp .id (.const (0 : Fin 1)))
  refine ⟨codeOfPartrec' F, by simp [codeOfPartrec'], fun y x => ?_⟩
  have := codeOfPartrec'_spec (Nat.Partrec'.of_part hF) (y := y) (v := ![x])
  simpa [F] using this

/-- In the standard model, `minGraph θ` holds at `(v, n)` whenever `θ` is
`Σ₁`, single-valued at `n`, and true at `(v, n)`. -/
lemma minGraph_true_at {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {v n : ℕ}
    (huniq : ∀ y : ℕ, θ.Evalb (M := ℕ) ![y, n] → y = v)
    (hv : θ.Evalb (M := ℕ) ![v, n]) :
    (minGraph θ).Evalb (M := ℕ) ![v, n] := by
  obtain ⟨s₀, hs₀⟩ := exists_bd hθ (Or.inr ⟨rfl, rfl⟩) ![v, n] hv
  rw [eval_minGraph]
  refine ⟨max s₀ v, ⟨le_def.mpr (Nat.eq_or_lt_of_le (Nat.le_max_right _ _)), ?_⟩, ?_⟩
  · have := bd_mono θ ![v, n] (le_max_left s₀ v) hs₀
    simpa [snoc_two] using this
  · intro s' _ y' _ h
    have : θ.Evalb (M := ℕ) ![y', n] := of_bd θ ![y', n] s' (by simpa [snoc_two] using h)
    exact huniq y' this

/-- Minimization naming at a single point, in `𝗣𝗔⁻`. -/
theorem minGraph_namesIn_partial {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {v n : ℕ}
    (huniq : ∀ y : ℕ, θ.Evalb (M := ℕ) ![y, n] → y = v)
    (hv : θ.Evalb (M := ℕ) ![v, n]) :
    NamesIn 𝗣𝗔⁻ (minGraph θ ⇜ ![#0, Semiterm.numeral n]) v := by
  have h2 : (𝗣𝗔⁻ : ArithmeticTheory) ⊢
      (minGraph θ ⇜ ![Semiterm.numeral v, Semiterm.numeral n]) := by
    have h := (sigma_one_completeness_iff_param (T := (𝗣𝗔⁻ : ArithmeticTheory))
      (minGraph_sigma1 hθ) (e := ![v, n])).mp (minGraph_true_at hθ huniq hv)
    have heq : (fun x => (Semiterm.Operator.numeral ℒₒᵣ (![v, n] x) : Semiterm ℒₒᵣ Empty 0))
        = (![Semiterm.numeral v, Semiterm.numeral n] : Fin 2 → Semiterm ℒₒᵣ Empty 0) := by
      funext x
      cases x using Fin.cases with
      | zero => rfl
      | succ x => cases x using Fin.cases with
        | zero => rfl
        | succ x => exact x.elim0
    rwa [heq] at h
  unfold NamesIn namesSentence
  apply Arithmetic.complete.{0} (𝗣𝗔⁻ : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  have hw : M↓[ℒₒᵣ] ⊧ (minGraph θ ⇜ ![Semiterm.numeral v, Semiterm.numeral n]) :=
    models_of_provable hM h2
  simp [models_iff] at hw ⊢
  intro x
  constructor
  · intro hx
    exact minGraph_unique θ hx hw
  · rintro rfl
    exact hw

/-- The short naming formula, at a single point, in `𝗣𝗔⁻`. -/
theorem logName_namesIn_partial {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {v n : ℕ}
    (huniq : ∀ y : ℕ, θ.Evalb (M := ℕ) ![y, n] → y = v)
    (hv : θ.Evalb (M := ℕ) ![v, n]) :
    NamesIn 𝗣𝗔⁻ (logName θ n) v := by
  have hN := minGraph_namesIn_partial hθ huniq hv
  unfold NamesIn namesSentence at hN ⊢
  apply Arithmetic.complete.{0} (𝗣𝗔⁻ : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  have hw := models_of_provable hM hN
  simp [models_iff] at hw
  simp [models_iff]
  intro x
  rw [eval_logName]
  exact hw x

/-- **Outputs of halting computations are cheap to name, in every theory.**
For every partial recursive `g` there is one constant `C` such that whenever
`g n` is defined with value `v`, every consistent `T ⊇ 𝗣𝗔⁻` names `v` within
budget `C + 6·log₂ n`. -/
theorem BoolosBigIn_partrec_bound {g : ℕ →. ℕ} (hg : Partrec g) :
    ∃ C, ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
      ∀ n v, v ∈ g n → v ≤ BoolosBigIn T (C + 6 * Nat.log2 n) := by
  obtain ⟨θ, hθ, hθg⟩ := partrec_graph hg
  refine ⟨fSize (minGraph θ) + 5, fun T _ _ n v hv => ?_⟩
  have huniq : ∀ y : ℕ, θ.Evalb (M := ℕ) ![y, n] → y = v :=
    fun y hy => Part.mem_unique ((hθg y n).mp hy) hv
  exact le_BoolosBigIn
    ⟨logName θ n, fSize_logName_le θ n, (logName_namesIn_partial hθ huniq ((hθg v n).mpr hv)).mono⟩

/-! ### Busy Beaver -/

open Nat.Partrec (Code)

/-- The output of program number `e` on input `0`, if it halts. -/
def progOut (e : ℕ) : Part ℕ := Code.eval (Denumerable.ofNat Code e) 0

lemma progOut_partrec : Partrec progOut :=
  Code.eval_part.comp (Computable.ofNat Code) (Computable.const 0)

/-- The halting time of program number `e` on input `0`, if it halts: the
least step bound at which Mathlib's bounded evaluator returns a result. -/
def progTime (e : ℕ) : Part ℕ :=
  Nat.rfind fun k => Part.some (Code.evaln k (Denumerable.ofNat Code e) 0).isSome

lemma progTime_partrec : Partrec progTime := by
  refine Partrec.rfind ?_
  have h1 : Computable fun p : ℕ × ℕ => Code.evaln p.2 (Denumerable.ofNat Code p.1) 0 :=
    Code.primrec_evaln.to_comp.comp
      ((Computable.snd.pair ((Computable.ofNat Code).comp Computable.fst)).pair (Computable.const 0))
  exact (Primrec.option_isSome.to_comp.comp h1).partrec.to₂

/-- Outputs of halting programs with code number at most `N`. -/
def outputsUpTo (N : ℕ) : Set ℕ := {v | ∃ e ≤ N, v ∈ progOut e}

/-- Halting times of halting programs with code number at most `N`. -/
def timesUpTo (N : ℕ) : Set ℕ := {v | ∃ e ≤ N, v ∈ progTime e}

lemma partUpTo_finite (g : ℕ → Part ℕ) (N : ℕ) : {v | ∃ e ≤ N, v ∈ g e}.Finite := by
  have hcover : {v | ∃ e ≤ N, v ∈ g e} ⊆ ⋃ e ∈ {e : ℕ | e ≤ N}, {v | v ∈ g e} := by
    rintro v ⟨e, he, hv⟩
    exact Set.mem_biUnion he hv
  apply Set.Finite.subset _ hcover
  apply Set.Finite.biUnion (Set.finite_le_nat N)
  intro e _
  rcases Set.eq_empty_or_nonempty {v | v ∈ g e} with he | ⟨v0, hv0⟩
  · rw [he]; exact Set.finite_empty
  · have : {v | v ∈ g e} = {v0} := by
      ext v; constructor
      · intro hv; exact Part.mem_unique hv hv0
      · rintro rfl; exact hv0
    rw [this]; exact Set.finite_singleton _

/-- **Busy Beaver, output form**: the largest output of a halting program
with code number at most `N`. -/
noncomputable def BB (N : ℕ) : ℕ := (partUpTo_finite progOut N).toFinset.sup id

/-- **Busy Beaver, time form**: the largest halting time of a halting
program with code number at most `N`. -/
noncomputable def BBtime (N : ℕ) : ℕ := (partUpTo_finite progTime N).toFinset.sup id

lemma log2_mono {a b : ℕ} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    have : Nat.log2 0 = 0 := by rw [Nat.log2_def]; simp
    omega
  · exact (Nat.le_log2 (by omega)).mpr (le_trans (Nat.log2_self_le (by omega)) h)

private theorem sup_partUpTo_le {g : ℕ → Part ℕ} (hg : Partrec g) :
    ∃ C, ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
      ∀ N, (partUpTo_finite g N).toFinset.sup id ≤ BoolosBigIn T (C + 6 * Nat.log2 N) := by
  obtain ⟨C, hC⟩ := BoolosBigIn_partrec_bound hg
  refine ⟨C, fun T _ _ N => ?_⟩
  apply Finset.sup_le
  intro v hv
  obtain ⟨e, he, hve⟩ := (Set.Finite.mem_toFinset _).mp hv
  have hmono : C + 6 * Nat.log2 e ≤ C + 6 * Nat.log2 N := by
    have := log2_mono he; omega
  exact le_trans (hC T e v hve) (BoolosBigIn_mono hmono)

/-- **Busy Beaver lower bound.** One constant `C` works for every consistent
theory `T ⊇ 𝗣𝗔⁻`: `BB N ≤ BoolosBigIn T (C + 6·log₂ N)`. -/
theorem BB_le_BoolosBigIn :
    ∃ C, ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
      ∀ N, BB N ≤ BoolosBigIn T (C + 6 * Nat.log2 N) :=
  sup_partUpTo_le progOut_partrec

/-- **Busy Beaver lower bound, time form.** -/
theorem BBtime_le_BoolosBigIn :
    ∃ C, ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
      ∀ N, BBtime N ≤ BoolosBigIn T (C + 6 * Nat.log2 N) :=
  sup_partUpTo_le progTime_partrec

end RayoBoolos

#print axioms RayoBoolos.BoolosBigIn_partrec_bound
#print axioms RayoBoolos.BB_le_BoolosBigIn
#print axioms RayoBoolos.BBtime_le_BoolosBigIn
