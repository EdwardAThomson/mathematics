/-
`RayoBoolos.OmegaHalting`: the halting problem reduces to "does this formula
name a number in `T`?", for every consistent `T ⊇ 𝗣𝗔⁻`. This is the core of
Theorem 1 (and Lemma 0(a, b)) of `large-numbers/OMEGA-FOR-NAMING.md`: the
naming probability `Ω_T` decides membership in the set `N_T` of naming
formulas, and through this file's family of formulas, `N_T` decides halting.

* `haltGraph θ (s, x)`: "`s` is the least bound at which `θ(·, x)` has a
  bounded witness". Every quantifier is bounded, so it is `Δ₀`
  (`haltGraph_delta0`). That is the point: a *false* instance is refutable
  in `𝗣𝗔⁻`, so the construction needs consistency of `T` only, not
  `Σ₁`-soundness. (`minGraph` of `Minimization.lean` is `Σ₁` and would not
  do: a consistent but `Σ₁`-unsound `T` could prove a false instance.)
* `haltName θ n = haltGraph θ (·, n̄)`.
* `namesIn_haltName_iff`: for `Σ₁` `θ`, `haltName θ n` names *some* number
  in `T` iff `∃ v, θ(v, n)` holds in `ℕ`.
* `halting_iff_named`: one formula family works for every such `T`:
  program `e` halts iff `haltName θ e` names a number in `T`.
* `named_not_computable`: hence `e ↦ [haltName θ e names something in T]`
  is not computable, for every consistent `T ⊇ 𝗣𝗔⁻`.

Not here (paper only): that `e ↦ ⌜haltName θ e⌝` is computable, the real
number `Ω_T` itself, and the measure bookkeeping by which `Ω_T` computes
`N_T`.
-/

module

public import RayoBoolos.BusyBeaver
public import RayoBoolos.Decided

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-- `haltGraph θ (s, x)`: `θ(·, x)` has a witness bounded by `s`, and by no
smaller bound. All quantifiers are bounded. -/
noncomputable def haltGraph (θ : ArithmeticSemisentence 2) : ArithmeticSemisentence 2 :=
  “s x. (∃ y <⁺ s, !(bd θ) y x s) ∧ ∀ s' < s, ∀ y <⁺ s', ¬!(bd θ) y x s'”

lemma haltGraph_delta0 {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) :
    Hierarchy 𝚺 0 (haltGraph θ) := by
  have h0 : Hierarchy 𝚺 0 (bd θ) := hierarchy_bd hθ (Or.inr ⟨rfl, rfl⟩)
  have h0' : Hierarchy 𝚷 0 (bd θ) := Hierarchy.zero_eq_alt h0
  simp [haltGraph, h0, h0']

lemma eval_haltGraph {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (θ : ArithmeticSemisentence 2) (s x : M) :
    (haltGraph θ).Evalb (M := M) ![s, x] ↔
      (∃ y ≤ s, (bd θ).Evalb (M := M) ![y, x, s]) ∧
        ∀ s' < s, ∀ y ≤ s', ¬ (bd θ).Evalb (M := M) ![y, x, s'] := by
  simp [haltGraph, Semiformula.eval_substs]

/-- The selected bound is unique in every model of `𝗣𝗔⁻`. -/
lemma haltGraph_unique {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (θ : ArithmeticSemisentence 2) {s s' x : M}
    (h : (haltGraph θ).Evalb (M := M) ![s, x]) (h' : (haltGraph θ).Evalb (M := M) ![s', x]) :
    s = s' := by
  rw [eval_haltGraph] at h h'
  obtain ⟨⟨y, hy, hB⟩, hmin⟩ := h
  obtain ⟨⟨y', hy', hB'⟩, hmin'⟩ := h'
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · exact absurd hB (hmin' s hlt y hy)
  · exact heq
  · exact absurd hB' (hmin s' hgt y' hy')

/-- If `θ(·, n)` has a solution in `ℕ`, some bound is selected. -/
lemma haltGraph_true {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {n : ℕ}
    (hex : ∃ v, θ.Evalb (M := ℕ) ![v, n]) :
    ∃ s, (haltGraph θ).Evalb (M := ℕ) ![s, n] := by
  classical
  have hP : ∃ s : ℕ, ∃ y : ℕ, y ≤ s ∧ (bd θ).Evalb (M := ℕ) ![y, n, s] := by
    obtain ⟨v, hv⟩ := hex
    obtain ⟨s₀, hs₀⟩ := exists_bd hθ (Or.inr ⟨rfl, rfl⟩) ![v, n] hv
    refine ⟨max s₀ v, v, le_max_right _ _, ?_⟩
    have := bd_mono θ ![v, n] (le_max_left s₀ v) hs₀
    simpa [snoc_two] using this
  refine ⟨Nat.find hP, ?_⟩
  rw [eval_haltGraph]
  obtain ⟨y, hy, hB⟩ := Nat.find_spec hP
  refine ⟨⟨y, le_def.mpr (Nat.eq_or_lt_of_le hy), hB⟩, fun s' hs' y' hy' hB' => ?_⟩
  have hy'' : y' ≤ s' := by
    rcases le_def.mp hy' with h | h
    · exact h.le
    · exact h.le
  exact Nat.find_min hP hs' ⟨y', hy'', hB'⟩

/-- If `θ(·, n)` has no solution in `ℕ`, no bound is selected. -/
lemma haltGraph_false {θ : ArithmeticSemisentence 2} {n : ℕ}
    (hno : ∀ v, ¬ θ.Evalb (M := ℕ) ![v, n]) (s : ℕ) :
    ¬ (haltGraph θ).Evalb (M := ℕ) ![s, n] := by
  rw [eval_haltGraph]
  rintro ⟨⟨y, _, hB⟩, _⟩
  exact hno y (of_bd θ ![y, n] s (by simpa [snoc_two] using hB))

/-- The naming formula: `haltGraph θ (·, n̄)`. -/
noncomputable def haltName (θ : ArithmeticSemisentence 2) (n : ℕ) : ArithmeticSemisentence 1 :=
  haltGraph θ ⇜ ![#0, Semiterm.numeral n]

lemma numeral_vec2 (a b : ℕ) :
    (fun x => (Semiterm.Operator.numeral ℒₒᵣ (![a, b] x) : Semiterm ℒₒᵣ Empty 0))
      = (![Semiterm.numeral a, Semiterm.numeral b] : Fin 2 → Semiterm ℒₒᵣ Empty 0) := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x => cases x using Fin.cases with
    | zero => rfl
    | succ x => exact x.elim0

/-- Halting case: `haltName θ n` names the selected bound, already in `𝗣𝗔⁻`. -/
theorem haltName_namesIn {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {n s : ℕ}
    (hs : (haltGraph θ).Evalb (M := ℕ) ![s, n]) :
    NamesIn 𝗣𝗔⁻ (haltName θ n) s := by
  have h2 : (𝗣𝗔⁻ : ArithmeticTheory) ⊢
      (haltGraph θ ⇜ ![Semiterm.numeral s, Semiterm.numeral n]) := by
    have h := (sigma_one_completeness_iff_param (T := (𝗣𝗔⁻ : ArithmeticTheory))
      (Hierarchy.of_zero (haltGraph_delta0 hθ)) (e := ![s, n])).mp hs
    rwa [numeral_vec2] at h
  unfold NamesIn namesSentence haltName
  apply Arithmetic.complete.{0} (𝗣𝗔⁻ : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  have hw : M↓[ℒₒᵣ] ⊧ (haltGraph θ ⇜ ![Semiterm.numeral s, Semiterm.numeral n]) :=
    models_of_provable hM h2
  simp [models_iff] at hw ⊢
  intro x
  constructor
  · intro hx
    exact haltGraph_unique θ hx hw
  · rintro rfl
    exact hw

/-- Non-halting case: no consistent `T ⊇ 𝗣𝗔⁻` makes `haltName θ n` name
anything. Uses consistency only. -/
theorem haltName_not_namesIn {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {n : ℕ}
    (hno : ∀ v, ¬ θ.Evalb (M := ℕ) ![v, n])
    (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (k : ℕ) :
    ¬ NamesIn T (haltName θ n) k := by
  intro hN
  have hneg : (𝗣𝗔⁻ : ArithmeticTheory) ⊢
      ((∼haltGraph θ) ⇜ ![Semiterm.numeral k, Semiterm.numeral n]) := by
    have hS1 : Hierarchy 𝚺 1 (∼haltGraph θ) :=
      Hierarchy.of_zero (Hierarchy.neg (haltGraph_delta0 hθ))
    have htrue : (∼haltGraph θ).Evalb (M := ℕ) ![k, n] := by
      simpa using haltGraph_false hno k
    have h := (sigma_one_completeness_iff_param (T := (𝗣𝗔⁻ : ArithmeticTheory))
      hS1 (e := ![k, n])).mp htrue
    rwa [numeral_vec2] at h
  have hT : T ⊢ ((∼haltGraph θ) ⇜ ![Semiterm.numeral k, Semiterm.numeral n]) :=
    Entailment.WeakerThan.pbl hneg
  have hpos : T ⊢ instAt (haltName θ n) k := ((namesIn_decides_singleton hN) k).1 rfl
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance
  have hbot : T ⊢ (⊥ : ArithmeticSentence) := by
    apply Arithmetic.complete.{0} T _ (fun (M : Type) _ hM ↦ ?_)
    have h1 := models_of_provable hM hT
    have h2 := models_of_provable hM hpos
    simp [models_iff, instAt, haltName, Semiformula.eval_substs] at h1 h2
    exact h1 h2
  exact (Entailment.not_inconsistent_iff_consistent.mpr inferInstance)
    (Entailment.inconsistent_iff_provable_bot.mpr hbot)

/-- **`haltName θ n` names some number in `T` iff `θ(·, n)` has a solution.**
For every consistent `T ⊇ 𝗣𝗔⁻`; soundness is not needed. -/
theorem namesIn_haltName_iff {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ)
    (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (n : ℕ) :
    (∃ k, NamesIn T (haltName θ n) k) ↔ ∃ v, θ.Evalb (M := ℕ) ![v, n] := by
  constructor
  · rintro ⟨k, hk⟩
    by_contra h
    push Not at h
    exact haltName_not_namesIn hθ h T k hk
  · intro hex
    obtain ⟨s, hs⟩ := haltGraph_true hθ hex
    exact ⟨s, (haltName_namesIn hθ hs).mono⟩

/-- **The halting problem reduces to provable naming.** One formula family
`haltName θ` works for every consistent `T ⊇ 𝗣𝗔⁻`: program `e` (Mathlib's
`Nat.Partrec.Code`, on input `0`) halts iff `haltName θ e` `T`-names a
number. -/
theorem halting_iff_named :
    ∃ θ : ArithmeticSemisentence 2,
      ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
        ∀ e : ℕ, (progOut e).Dom ↔ ∃ k, NamesIn T (haltName θ e) k := by
  obtain ⟨θ, hθ, hθg⟩ := partrec_graph progOut_partrec
  refine ⟨θ, fun T _ _ e => ?_⟩
  rw [namesIn_haltName_iff hθ T e]
  constructor
  · intro hd
    exact ⟨(progOut e).get hd, (hθg _ e).mpr (Part.get_mem hd)⟩
  · rintro ⟨v, hv⟩
    exact Part.dom_iff_mem.mpr ⟨v, (hθg v e).mp hv⟩

open Nat.Partrec (Code) in
/-- Halting for programs numbered by `ℕ` is not computable. -/
lemma progOut_dom_not_computable : ¬ ComputablePred (fun e : ℕ => (progOut e).Dom) := by
  intro h
  obtain ⟨f, hf, hp⟩ := ComputablePred.computable_iff.mp h
  apply ComputablePred.halting_problem 0
  refine ComputablePred.computable_iff.mpr ⟨fun c => f (Encodable.encode c), hf.comp Computable.encode, ?_⟩
  funext c
  have := congrFun hp (Encodable.encode c)
  simpa [progOut, Denumerable.ofNat_encode] using this

/-- **Deciding provable naming is as hard as halting**, in every consistent
`T ⊇ 𝗣𝗔⁻`, already on one fixed family of formulas. -/
theorem named_not_computable :
    ∃ θ : ArithmeticSemisentence 2,
      ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
        ¬ ComputablePred (fun e : ℕ => ∃ k, NamesIn T (haltName θ e) k) := by
  obtain ⟨θ, hθ⟩ := halting_iff_named
  exact ⟨θ, fun T _ _ h => progOut_dom_not_computable (h.of_eq fun e => (hθ T e).symm)⟩

end RayoBoolos

#print axioms RayoBoolos.namesIn_haltName_iff
#print axioms RayoBoolos.halting_iff_named
#print axioms RayoBoolos.named_not_computable
