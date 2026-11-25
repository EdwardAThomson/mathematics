/-
`RayoBoolos.Minimization` — `BoolosBig_PA` eventually dominates **every
computable function**, and is therefore not computable. This is Theorem 1
(in its domination form) and the non-computability corollary of
`large-numbers/BOOLOS-IS-BUSY-BEAVER-CLASS.md`.

`BoolosBig.lean` proves domination only for functions `𝗣𝗔` proves total,
because it derives the naming fact from `𝗣𝗔 ⊢ ∀x ∃!y θ(y, x)`. That
hypothesis is not needed. To `𝗣𝗔`-name `f n` it is enough that, for this one
`n`, a single true `Σ₁` sentence is provable (`Σ₁`-completeness), together
with a uniqueness statement that follows from the linear order alone.

Route, all in this file:

1. `bd θ`: `θ` with one extra variable `s` and every existential quantifier
   bounded by `s`. In `ℕ`: `bd θ` implies `θ` (`of_bd`), is monotone in `s`
   (`bd_mono`), and for `Σ₁` `θ` true at some point, some `s` works
   (`exists_bd`). Syntactically `bd θ` is `Δ₀` (`hierarchy_bd`).
2. `minGraph θ (y, x)`: "some `s ≥ y` gives `θ(y, x)` a bounded witness, and
   every `y' ≤ s' ≤ s` with a bounded witness at `s'` equals `y`". It is `Σ₁`
   (`minGraph_sigma1`), true of `(f n, n)` in `ℕ` when `θ` defines the graph
   of `f` (`minGraph_true`), and selects at most one `y` in every model of
   `𝗣𝗔⁻` (`minGraph_unique`).
3. `minGraph_names`: hence `minGraph θ (·, n̄)` `𝗣𝗔`-names `f n`.
4. `computable_graph`: every computable function has such a `θ`
   (`Foundation`'s `codeOfPartrec'`).
5. `BoolosBig_PA_dominates_computable`, `BoolosBig_PA_not_computable`.

The wrapper in step 2 differs slightly from the least-witness formula `μ` of
the paper note: instead of asserting minimality of `s`, it asserts that
everything found below `s` agrees with `y`. Uniqueness then needs only
totality of `≤`, and no negated occurrence of an unbounded quantifier.

Numerals here are still unary, so the size bound is linear in `n` and the
argument goes through a running maximum of `f` up to `n²`. The sharper
`C_f + 6·log₂(n+2)` bound of the paper note needs binary numerals and is
not mechanized; neither are the Busy Beaver sandwich (Theorems 2 and 3) or
the theory-independence corollary.
-/

module

public import RayoBoolos.BoolosBig
public import Foundation.FirstOrder.Arithmetic.R0.Representation

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Bounding the unbounded existentials of a formula -/

/-- Weaken a term by one extra bound variable, added in *last* position. -/
def tLift {n : ℕ} : Semiterm ℒₒᵣ Empty n → Semiterm ℒₒᵣ Empty (n + 1)
  |  .bvar x => .bvar x.castSucc
  |  .fvar x => x.elim
  | .func f v => .func f (fun i => tLift (v i))

/-- `bd φ` is `φ` with one extra bound variable `s`, in last position, and
every existential quantifier `∃x` replaced by `∃x < s`. -/
def bd : {n : ℕ} → Semiformula ℒₒᵣ Empty n → Semiformula ℒₒᵣ Empty (n + 1)
  | _,    .verum => ⊤
  | _,   .falsum => ⊥
  | _,  .rel r v => .rel r (fun i => tLift (v i))
  | _, .nrel r v => .nrel r (fun i => tLift (v i))
  | _,  .and φ ψ => bd φ ⋏ bd ψ
  | _,   .or φ ψ => bd φ ⋎ bd ψ
  | _,    .all φ => ∀¹ (bd φ)
  | n,    .exs φ =>
    ∃¹[Semiformula.Operator.LT.lt.operator ![#0, #(Fin.last (n + 1))]] (bd φ)

@[simp] lemma bd_verum {n : ℕ} : bd (⊤ : Semiformula ℒₒᵣ Empty n) = ⊤ := rfl
@[simp] lemma bd_falsum {n : ℕ} : bd (⊥ : Semiformula ℒₒᵣ Empty n) = ⊥ := rfl
@[simp] lemma bd_rel {n k : ℕ} (r : (ℒₒᵣ : Language).Rel k) (v : Fin k → Semiterm ℒₒᵣ Empty n) :
    bd (.rel r v) = .rel r (fun i => tLift (v i)) := rfl
@[simp] lemma bd_nrel {n k : ℕ} (r : (ℒₒᵣ : Language).Rel k) (v : Fin k → Semiterm ℒₒᵣ Empty n) :
    bd (.nrel r v) = .nrel r (fun i => tLift (v i)) := rfl
@[simp] lemma bd_and {n : ℕ} (φ ψ : Semiformula ℒₒᵣ Empty n) : bd (φ ⋏ ψ) = bd φ ⋏ bd ψ := rfl
@[simp] lemma bd_or {n : ℕ} (φ ψ : Semiformula ℒₒᵣ Empty n) : bd (φ ⋎ ψ) = bd φ ⋎ bd ψ := rfl
@[simp] lemma bd_all {n : ℕ} (φ : Semiformula ℒₒᵣ Empty (n + 1)) : bd (∀¹ φ) = ∀¹ (bd φ) := rfl
@[simp] lemma bd_exs {n : ℕ} (φ : Semiformula ℒₒᵣ Empty (n + 1)) :
    bd (∃¹ φ) = ∃¹[Semiformula.Operator.LT.lt.operator ![#0, #(Fin.last (n + 1))]] (bd φ) := rfl

@[simp] lemma val_tLift {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) (b : Fin n → ℕ) (s : ℕ) :
    (tLift t).val (b <: s) Empty.elim = t.val b Empty.elim := by
  induction t with
  | bvar x => simp [tLift]
  | fvar x => exact x.elim
  | func f v ih => simp [tLift, Function.comp_def, ih]

lemma cons_snoc {n : ℕ} (x : ℕ) (b : Fin n → ℕ) (s : ℕ) : (x :> (b <: s)) = ((x :> b) <: s) :=
  Matrix.vecCons_assoc x s b

/-! Semantics of `bd` in the standard model. -/

/-- A bounded witness is a witness: `bd φ` implies `φ`. -/
lemma of_bd {n : ℕ} (φ : Semiformula ℒₒᵣ Empty n) (b : Fin n → ℕ) (s : ℕ) :
    (bd φ).Evalb (M := ℕ) (b <: s) → φ.Evalb (M := ℕ) b := by
  induction φ using Semiformula.rec' with
  | hverum => intro _; simp
  | hfalsum => intro h; simp at h
  | hrel r v => intro h; simpa [Function.comp_def] using h
  | hnrel r v => intro h; simpa [Function.comp_def] using h
  | hand φ ψ ihφ ihψ =>
    intro h
    have h' : (bd φ).Evalb (M := ℕ) (b <: s) ∧ (bd ψ).Evalb (M := ℕ) (b <: s) := by
      simpa using h
    simpa using ⟨ihφ b h'.1, ihψ b h'.2⟩
  | hor φ ψ ihφ ihψ =>
    intro h
    have h' : (bd φ).Evalb (M := ℕ) (b <: s) ∨ (bd ψ).Evalb (M := ℕ) (b <: s) := by
      simpa using h
    simpa using h'.imp (ihφ b) (ihψ b)
  | hall φ ih =>
    intro h
    have h' : ∀ x : ℕ, (bd φ).Evalb (M := ℕ) (x :> (b <: s)) := by simpa using h
    simp only [Semiformula.eval_all]
    intro x
    exact ih (x :> b) (by simpa [cons_snoc] using h' x)
  | hexs φ ih =>
    intro h
    have h' : ∃ x : ℕ, x < s ∧ (bd φ).Evalb (M := ℕ) (x :> (b <: s)) := by
      simpa using h
    obtain ⟨x, _, hx⟩ := h'
    simp only [Semiformula.eval_ex]
    exact ⟨x, ih (x :> b) (by simpa [cons_snoc] using hx)⟩

/-- `bd φ` is monotone in the bound. -/
lemma bd_mono {n : ℕ} (φ : Semiformula ℒₒᵣ Empty n) (b : Fin n → ℕ) {s s' : ℕ} (hs : s ≤ s') :
    (bd φ).Evalb (M := ℕ) (b <: s) → (bd φ).Evalb (M := ℕ) (b <: s') := by
  induction φ using Semiformula.rec' with
  | hverum => intro _; simp
  | hfalsum => intro h; simp at h
  | hrel r v => intro h; simpa [Function.comp_def] using h
  | hnrel r v => intro h; simpa [Function.comp_def] using h
  | hand φ ψ ihφ ihψ =>
    intro h
    have h' : (bd φ).Evalb (M := ℕ) (b <: s) ∧ (bd ψ).Evalb (M := ℕ) (b <: s) := by
      simpa using h
    simpa using ⟨ihφ b h'.1, ihψ b h'.2⟩
  | hor φ ψ ihφ ihψ =>
    intro h
    have h' : (bd φ).Evalb (M := ℕ) (b <: s) ∨ (bd ψ).Evalb (M := ℕ) (b <: s) := by
      simpa using h
    simpa using h'.imp (ihφ b) (ihψ b)
  | hall φ ih =>
    intro h
    have h' : ∀ x : ℕ, (bd φ).Evalb (M := ℕ) (x :> (b <: s)) := by simpa using h
    simp only [bd_all, Semiformula.eval_all]
    intro x
    simpa [cons_snoc] using ih (x :> b) (by simpa [cons_snoc] using h' x)
  | hexs φ ih =>
    intro h
    have h' : ∃ x : ℕ, x < s ∧ (bd φ).Evalb (M := ℕ) (x :> (b <: s)) := by
      simpa using h
    obtain ⟨x, hxs, hx⟩ := h'
    have : ∃ x : ℕ, x < s' ∧ (bd φ).Evalb (M := ℕ) (x :> (b <: s')) :=
      ⟨x, lt_of_lt_of_le hxs hs, by simpa [cons_snoc] using ih (x :> b) (by simpa [cons_snoc] using hx)⟩
    simpa using this

/-- Semantics of `bd` on a bounded universal quantifier. -/
lemma eval_bd_ball {n : ℕ} (t : Semiterm ℒₒᵣ Empty (n + 1)) (φ : Semiformula ℒₒᵣ Empty (n + 1))
    (b : Fin n → ℕ) (s : ℕ) :
    (bd (∀¹[Semiformula.Operator.LT.lt.operator ![#0, t]] φ)).Evalb (M := ℕ) (b <: s) ↔
      ∀ x : ℕ, x < t.val (x :> b) Empty.elim → (bd φ).Evalb (M := ℕ) ((x :> b) <: s) := by
  simp [ball, Semiformula.imp_eq, Semiformula.Operator.lt_def, cons_snoc, Function.comp_def,
    imp_iff_not_or]

/-- Semantics of `bd` on a bounded existential quantifier. -/
lemma eval_bd_bexs {n : ℕ} (t : Semiterm ℒₒᵣ Empty (n + 1)) (φ : Semiformula ℒₒᵣ Empty (n + 1))
    (b : Fin n → ℕ) (s : ℕ) :
    (bd (∃¹[Semiformula.Operator.LT.lt.operator ![#0, t]] φ)).Evalb (M := ℕ) (b <: s) ↔
      ∃ x : ℕ, x < s ∧ x < t.val (x :> b) Empty.elim ∧ (bd φ).Evalb (M := ℕ) ((x :> b) <: s) := by
  simp [bexs, Semiformula.Operator.lt_def, cons_snoc, Function.comp_def]

lemma nat_collect (P : ℕ → ℕ → Prop) (hP : ∀ x s s', s ≤ s' → P x s → P x s') (T : ℕ)
    (h : ∀ x < T, ∃ s, P x s) : ∃ S, ∀ x < T, P x S := by
  induction T with
  | zero => exact ⟨0, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  | succ T ih =>
    obtain ⟨S, hS⟩ := ih (fun x hx => h x (Nat.lt_succ_of_lt hx))
    obtain ⟨s, hs⟩ := h T (Nat.lt_succ_self T)
    refine ⟨max S s, fun x hx => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hlt | rfl
    · exact hP x S _ (le_max_left _ _) (hS x hlt)
    · exact hP x s _ (le_max_right _ _) hs

/-- For a `Σ₁` (or `Δ₀`) formula true in `ℕ`, some bound works. -/
lemma exists_bd {Γ : Polarity} {r n : ℕ} {φ : Semiformula ℒₒᵣ Empty n} (h : Hierarchy Γ r φ) :
    (r = 0 ∨ (Γ = 𝚺 ∧ r = 1)) → ∀ b : Fin n → ℕ, φ.Evalb (M := ℕ) b →
      ∃ s, (bd φ).Evalb (M := ℕ) (b <: s) := by
  induction h with
  | verum => intro _ b _; exact ⟨0, by simp⟩
  | falsum => intro _ b h; simp at h
  | rel => intro _ b h; exact ⟨0, by simpa [Function.comp_def] using h⟩
  | nrel => intro _ b h; exact ⟨0, by simpa [Function.comp_def] using h⟩
  | and hp hq ihp ihq =>
    intro hr b h
    have h' := (by simpa using h : _ ∧ _)
    obtain ⟨s₁, h₁⟩ := ihp hr b h'.1
    obtain ⟨s₂, h₂⟩ := ihq hr b h'.2
    exact ⟨max s₁ s₂, by
      simpa using ⟨bd_mono _ b (le_max_left s₁ s₂) h₁, bd_mono _ b (le_max_right s₁ s₂) h₂⟩⟩
  | or hp hq ihp ihq =>
    intro hr b h
    rcases (by simpa using h : _ ∨ _) with h' | h'
    · obtain ⟨s, hs⟩ := ihp hr b h'
      exact ⟨s, by simpa using Or.inl hs⟩
    · obtain ⟨s, hs⟩ := ihq hr b h'
      exact ⟨s, by simpa using Or.inr hs⟩
  | @ball Γ r n φ t pos hp ih =>
    intro hr b h
    obtain ⟨t', rfl⟩ := Rew.positive_iff.mp pos
    have h' : ∀ x : ℕ, x < t'.val b Empty.elim → φ.Evalb (M := ℕ) (x :> b) := by
      simpa using h
    obtain ⟨S, hS⟩ := nat_collect (fun x s => (bd φ).Evalb (M := ℕ) ((x :> b) <: s))
      (fun x s s' hs => bd_mono φ (x :> b) hs) (t'.val b Empty.elim)
      (fun x hx => ih hr (x :> b) (h' x hx))
    refine ⟨S, (eval_bd_ball _ _ b S).mpr ?_⟩
    intro x hx
    exact hS x (by simpa using hx)
  | @bexs Γ r n φ t pos hp ih =>
    intro hr b h
    have h' : ∃ x : ℕ, x < t.val (x :> b) Empty.elim ∧ φ.Evalb (M := ℕ) (x :> b) := by
      simpa using h
    obtain ⟨x, hxt, hx⟩ := h'
    obtain ⟨s, hs⟩ := ih hr (x :> b) hx
    refine ⟨max s (x + 1), (eval_bd_bexs _ _ b _).mpr ⟨x, ?_, hxt, ?_⟩⟩
    · exact lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _)
    · exact bd_mono φ (x :> b) (le_max_left _ _) hs
  | @exs r n φ hp ih =>
    intro hr b h
    obtain ⟨x, hx⟩ := (by simpa using h : ∃ x : ℕ, φ.Evalb (M := ℕ) (x :> b))
    obtain ⟨s, hs⟩ := ih hr (x :> b) hx
    have : ∃ y : ℕ, y < max s (x + 1) ∧ (bd φ).Evalb (M := ℕ) ((y :> b) <: max s (x + 1)) :=
      ⟨x, lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _),
        bd_mono φ (x :> b) (le_max_left _ _) hs⟩
    exact ⟨max s (x + 1), by simpa [cons_snoc] using this⟩
  | all hp ih => intro hr; rcases hr with hr | ⟨hΓ, _⟩ <;> simp at *
  | @sigma r n φ hp ih =>
    intro hr b h
    have hr0 : r = 0 := by rcases hr with hr | ⟨_, hr⟩ <;> omega
    obtain ⟨x, hx⟩ := (by simpa using h : ∃ x : ℕ, φ.Evalb (M := ℕ) (x :> b))
    obtain ⟨s, hs⟩ := ih (Or.inl hr0) (x :> b) hx
    have : ∃ y : ℕ, y < max s (x + 1) ∧ (bd φ).Evalb (M := ℕ) ((y :> b) <: max s (x + 1)) :=
      ⟨x, lt_of_lt_of_le (Nat.lt_succ_self x) (le_max_right _ _),
        bd_mono φ (x :> b) (le_max_left _ _) hs⟩
    exact ⟨max s (x + 1), by simpa [cons_snoc] using this⟩
  | pi hp ih => intro hr; rcases hr with hr | ⟨hΓ, _⟩ <;> simp at *
  | dummy_sigma hp ih => intro hr; rcases hr with hr | ⟨_, hr⟩ <;> omega
  | dummy_pi hp ih => intro hr; rcases hr with hr | ⟨hΓ, _⟩ <;> simp at *

/-! `bd φ` is `Δ₀`. -/

lemma tLift_positive {n : ℕ} {t : Semiterm ℒₒᵣ Empty (n + 1)} (ht : t.Positive) :
    (tLift t).Positive := by
  induction t with
  | bvar x =>
    have hx : 0 < x := by simpa using ht
    simpa [tLift] using Fin.castSucc_pos_iff.mpr hx
  | fvar x => exact x.elim
  | func f v ih =>
    have hv : ∀ i, (v i).Positive := by simpa using ht
    simpa [tLift] using fun i => ih i (hv i)

lemma bd_ball {n : ℕ} (t : Semiterm ℒₒᵣ Empty (n + 1)) (φ : Semiformula ℒₒᵣ Empty (n + 1)) :
    bd (∀¹[Semiformula.Operator.LT.lt.operator ![#0, t]] φ) =
      ∀¹[Semiformula.Operator.LT.lt.operator ![#0, tLift t]] (bd φ) := by
  simp [ball, Semiformula.imp_eq, Semiformula.Operator.lt_def, Matrix.fun_eq_vec_two, tLift]

lemma bd_bexs {n : ℕ} (t : Semiterm ℒₒᵣ Empty (n + 1)) (φ : Semiformula ℒₒᵣ Empty (n + 1)) :
    bd (∃¹[Semiformula.Operator.LT.lt.operator ![#0, t]] φ) =
      ∃¹[Semiformula.Operator.LT.lt.operator ![#0, #(Fin.last (n + 1))]]
        (Semiformula.Operator.LT.lt.operator ![#0, tLift t] ⋏ bd φ) := by
  simp [bexs, Semiformula.Operator.lt_def, Matrix.fun_eq_vec_two, tLift]

lemma last_positive (n : ℕ) : (#(Fin.last (n + 1)) : Semiterm ℒₒᵣ Empty (n + 1 + 1)).Positive := by
  simpa using Fin.last_pos

lemma hierarchy_bd {Γ : Polarity} {r n : ℕ} {φ : Semiformula ℒₒᵣ Empty n} (h : Hierarchy Γ r φ) :
    (r = 0 ∨ (Γ = 𝚺 ∧ r = 1)) → Hierarchy 𝚺 0 (bd φ) := by
  induction h with
  | verum => intro _; simp
  | falsum => intro _; simp
  | rel => intro _; simp
  | nrel => intro _; simp
  | and hp hq ihp ihq => intro hr; simpa using ⟨ihp hr, ihq hr⟩
  | or hp hq ihp ihq => intro hr; simpa using ⟨ihp hr, ihq hr⟩
  | @ball Γ r n φ t pos hp ih =>
    intro hr
    rw [bd_ball]
    exact Hierarchy.ball (tLift_positive pos) (ih hr)
  | @bexs Γ r n φ t pos hp ih =>
    intro hr
    rw [bd_bexs]
    exact Hierarchy.bexs (last_positive n) (by simpa using ih hr)
  | @exs r n φ hp ih =>
    intro hr
    rw [bd_exs]
    exact Hierarchy.bexs (last_positive n) (ih hr)
  | all hp ih => intro hr; rcases hr with hr | ⟨hΓ, _⟩ <;> simp at *
  | @sigma r n φ hp ih =>
    intro hr
    have hr0 : r = 0 := by rcases hr with hr | ⟨_, hr⟩ <;> omega
    rw [bd_exs]
    exact Hierarchy.bexs (last_positive n) (ih (Or.inl hr0))
  | pi hp ih => intro hr; rcases hr with hr | ⟨hΓ, _⟩ <;> simp at *
  | dummy_sigma hp ih => intro hr; rcases hr with hr | ⟨_, hr⟩ <;> omega
  | dummy_pi hp ih => intro hr; rcases hr with hr | ⟨hΓ, _⟩ <;> simp at *

/-! ### The minimization wrapper -/

/-- `minGraph θ (y, x)`: there is a bound `s ≥ y` at which `θ(y, x)` has a
bounded witness, and every `y' ≤ s' ≤ s` with a bounded witness at `s'`
equals `y`. Uniqueness of `y` follows from linearity of the order alone. -/
noncomputable def minGraph (θ : ArithmeticSemisentence 2) : ArithmeticSemisentence 2 :=
  “y x. ∃ s, (y ≤ s ∧ !(bd θ) y x s) ∧ ∀ s' <⁺ s, ∀ y' <⁺ s', !(bd θ) y' x s' → y' = y”

lemma minGraph_sigma1 {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) :
    Hierarchy 𝚺 1 (minGraph θ) := by
  have h0 : Hierarchy 𝚺 0 (bd θ) := hierarchy_bd hθ (Or.inr ⟨rfl, rfl⟩)
  have hS : Hierarchy 𝚺 1 (bd θ) := Hierarchy.of_zero h0
  have hP : Hierarchy 𝚷 1 (bd θ) := Hierarchy.of_zero h0
  simp [minGraph, hS, hP]

lemma eval_minGraph {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (θ : ArithmeticSemisentence 2) (y x : M) :
    (minGraph θ).Evalb (M := M) ![y, x] ↔
      ∃ s, (y ≤ s ∧ (bd θ).Evalb (M := M) ![y, x, s]) ∧
        ∀ s' ≤ s, ∀ y' ≤ s', (bd θ).Evalb (M := M) ![y', x, s'] → y' = y := by
  simp [minGraph, Semiformula.eval_substs]

lemma snoc_two (a b c : ℕ) : (![a, b] <: c) = ![a, b, c] := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact i.elim0

/-- In the standard model, `minGraph θ` holds of `(f n, n)` whenever `θ` is a
`Σ₁` definition of the graph of `f`. -/
lemma minGraph_true {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {f : ℕ → ℕ}
    (hf : ∀ y x : ℕ, θ.Evalb (M := ℕ) ![y, x] ↔ y = f x) (n : ℕ) :
    (minGraph θ).Evalb (M := ℕ) ![f n, n] := by
  obtain ⟨s₀, hs₀⟩ := exists_bd hθ (Or.inr ⟨rfl, rfl⟩) ![f n, n] ((hf (f n) n).mpr rfl)
  rw [eval_minGraph]
  refine ⟨max s₀ (f n), ⟨le_def.mpr (Nat.eq_or_lt_of_le (Nat.le_max_right _ _)), ?_⟩, ?_⟩
  · have := bd_mono θ ![f n, n] (le_max_left s₀ (f n)) hs₀
    simpa [snoc_two] using this
  · intro s' _ y' _ h
    have : θ.Evalb (M := ℕ) ![y', n] := of_bd θ ![y', n] s' (by simpa [snoc_two] using h)
    exact (hf y' n).mp this

/-- Uniqueness of the value selected by `minGraph θ`, in any model of `𝗣𝗔⁻`,
from linearity of the order alone. -/
lemma minGraph_unique {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (θ : ArithmeticSemisentence 2) {y y' x : M}
    (h : (minGraph θ).Evalb (M := M) ![y, x]) (h' : (minGraph θ).Evalb (M := M) ![y', x]) :
    y = y' := by
  rw [eval_minGraph] at h h'
  obtain ⟨s, ⟨hys, hB⟩, hmin⟩ := h
  obtain ⟨s', ⟨hys', hB'⟩, hmin'⟩ := h'
  rcases le_total s s' with hle | hle
  · exact hmin' s hle y hys hB
  · exact (hmin s' hle y' hys' hB').symm

/-- **Minimization naming.** If `θ` is a `Σ₁` formula defining the graph of
`f` in the standard model, then for every `n` the formula `minGraph θ (·, n̄)`
`𝗣𝗔`-names `f n`. No totality proof inside `𝗣𝗔` is required. -/
theorem minGraph_names {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {f : ℕ → ℕ}
    (hf : ∀ y x : ℕ, θ.Evalb (M := ℕ) ![y, x] ↔ y = f x) (n : ℕ) :
    TNamesMeta (minGraph θ ⇜ ![#0, Semiterm.numeral n]) (f n) := by
  have h2 : (𝗣𝗔 : ArithmeticTheory) ⊢
      (minGraph θ ⇜ ![Semiterm.numeral (f n), Semiterm.numeral n]) := by
    have h := (sigma_one_completeness_iff_param (T := (𝗣𝗔 : ArithmeticTheory))
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
  unfold TNamesMeta namesSentence
  apply Arithmetic.complete.{0} (𝗣𝗔 : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hM
  have hw : M↓[ℒₒᵣ] ⊧ (minGraph θ ⇜ ![Semiterm.numeral (f n), Semiterm.numeral n]) :=
    models_of_provable hM h2
  simp [models_iff] at hw ⊢
  intro x
  constructor
  · intro hx
    exact minGraph_unique θ hx hw
  · rintro rfl
    exact hw

/-! ### Domination of every computable function -/

/-- Every computable function has a `Σ₁` graph formula, correct in `ℕ`.
(`Foundation`'s arithmetization of partial recursive functions.) -/
lemma computable_graph {g : ℕ → ℕ} (hg : Computable g) :
    ∃ θ : ArithmeticSemisentence 2, Hierarchy 𝚺 1 θ ∧
      ∀ y x : ℕ, θ.Evalb (M := ℕ) ![y, x] ↔ y = g x := by
  let F : List.Vector ℕ 1 →. ℕ := fun v ↦ Part.some (g (v.get 0))
  have hF : Partrec F := by
    change Partrec fun v : List.Vector ℕ 1 ↦ Part.some (g (v.get 0))
    exact hg.comp (Primrec.to_comp <| Primrec.vector_get.comp .id (.const (0 : Fin 1)))
  refine ⟨codeOfPartrec' F, by simp [codeOfPartrec'], fun y x => ?_⟩
  have := codeOfPartrec'_spec (Nat.Partrec'.of_part hF) (y := y) (v := ![x])
  simpa [F, eq_comm] using this

/-- The naming formula has size linear in `n` (unary numerals). -/
theorem fSize_minGraphAt_le (θ : ArithmeticSemisentence 2) (n : ℕ) :
    fSize (minGraph θ ⇜ (![#0, Semiterm.numeral n] : Fin 2 → Semiterm ℒₒᵣ Empty 1)) ≤
      fSize (minGraph θ) * (2 * n + 1) := by
  have hb : ∀ i : Fin 2, tSize ((Rew.subst (![#0, Semiterm.numeral n] : Fin 2 → Semiterm ℒₒᵣ Empty 1))
      (Semiterm.bvar i)) ≤ 2 * n + 1 := by
    intro i
    cases i using Fin.cases with
    | zero => simp [tSize]
    | succ j =>
      cases j using Fin.cases with
      | zero => simpa using tSize_numeral_le 1 n
      | succ k => exact k.elim0
  exact fSize_rew_le (minGraph θ) (Rew.subst ![#0, Semiterm.numeral n]) (2 * n + 1) (by omega) hb

/-- Running maximum of `f`. -/
def runMax (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | m + 1 => max (runMax f m) (f (m + 1))

lemma le_runMax (f : ℕ → ℕ) {i m : ℕ} (h : i ≤ m) : f i ≤ runMax f m := by
  induction m with
  | zero => have : i = 0 := by omega
            subst this; exact le_refl _
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact le_trans (ih (by omega)) (le_max_left _ _)
    · have : i = m + 1 := by omega
      subst this; exact le_max_right _ _

lemma runMax_computable {f : ℕ → ℕ} (hf : Computable f) : Computable (runMax f) := by
  have h : Computable₂ (fun (_ : ℕ) (p : ℕ × ℕ) => max p.2 (f (p.1 + 1))) :=
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂
  have := Computable.nat_rec (f := fun a : ℕ => a) (g := fun _ : ℕ => f 0)
    Computable.id (Computable.const (f 0)) h
  refine this.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => simp [runMax, ← ih]

/-- For every computable `f` there is a constant `c` such that the running
maximum of `f` up to `n * n` is nameable within budget `c * (2 * n + 1)`. -/
theorem computable_names_le {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c, 1 ≤ c ∧ ∀ n, runMax f (n * n) ≤ BoolosBig_PA (c * (2 * n + 1)) := by
  have hg : Computable (fun n => runMax f (n * n)) :=
    (runMax_computable hf).comp (Primrec.nat_mul.to_comp.comp Computable.id Computable.id)
  obtain ⟨θ, hθ, hθf⟩ := computable_graph hg
  refine ⟨fSize (minGraph θ), fSize_pos _, fun n => ?_⟩
  exact namedValues_le_BoolosBig_PA
    ⟨minGraph θ ⇜ ![#0, Semiterm.numeral n], fSize_minGraphAt_le θ n, minGraph_names hθ hθf n⟩

/-- **`BoolosBig_PA` eventually dominates every computable function.** No
assumption that `𝗣𝗔` proves `f` total, and no monotonicity assumption. -/
theorem BoolosBig_PA_dominates_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ N, ∀ m > N, BoolosBig_PA m ≥ f m := by
  obtain ⟨c, hc, hnames⟩ := computable_names_le hf
  set N0 := 4 * c + 4 with hN0_def
  refine ⟨N0 * N0, fun m hm => ?_⟩
  set n := Nat.sqrt m + 1 with hn_def
  have hsqrt_ge : N0 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
  have hn_sq_ge_m : m ≤ n * n := by
    have hthis := Nat.succ_le_succ_sqrt m
    simp only [hn_def] at hthis ⊢
    omega
  have hc_bound : c * (2 * n + 1) ≤ m := by
    have hsq_le : Nat.sqrt m * Nat.sqrt m ≤ m := Nat.sqrt_le m
    have hstep : c * (2 * n + 1) ≤ Nat.sqrt m * Nat.sqrt m := by
      simp only [hn_def]
      nlinarith [hsqrt_ge]
    exact le_trans hstep hsq_le
  calc f m ≤ runMax f (n * n) := le_runMax f hn_sq_ge_m
    _ ≤ BoolosBig_PA (c * (2 * n + 1)) := hnames n
    _ ≤ BoolosBig_PA m := BoolosBig_PA_mono hc_bound

/-- **`BoolosBig_PA` is not computable.** -/
theorem BoolosBig_PA_not_computable : ¬ Computable BoolosBig_PA := by
  intro h
  have h1 : Computable (fun n => BoolosBig_PA n + 1) := Computable.succ.comp h
  obtain ⟨N, hN⟩ := BoolosBig_PA_dominates_computable h1
  have := hN (N + 1) (Nat.lt_succ_self N)
  omega

end RayoBoolos

#print axioms RayoBoolos.minGraph_names
#print axioms RayoBoolos.BoolosBig_PA_dominates_computable
#print axioms RayoBoolos.BoolosBig_PA_not_computable
