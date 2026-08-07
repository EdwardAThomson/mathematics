/-
`RayoBoolos.BoolosBig` — Step 5 of `BOOLOS-B1-B3-REPORT.md` / the fix
identified by `BOOLOS-B3-PAPER-VERIFICATION.md`: a concrete
`BoolosBig_PA : ℕ → ℕ`, monotone, matching `BOOLOS-B0-WELLDEFINEDNESS.md`'s
`BoolosBig_T(n) = sup{k : some φ with |φ| ≤ n T-names k}`, and the genuine
eventual-domination theorem `∀ f PA-provably-total, ∃ N, ∀ m > N,
BoolosBig_PA(m) ≥ f(m)`.

**Definitional choice, flagged as the paper-verification note asked**: the
abstract finite-max machinery for this already exists, but only for an
abstract carrier type, in the sibling Mathlib-free `rayo-lean/` project
(`Rayo.exists_max_of_finite_naming`, `Rayo/BoolosB0Core.lean`). I checked
whether `rayo-lean-boolos` can import it directly: a `path`-requiring it in
`lakefile.toml` and `lake update` resolves cleanly (same toolchain,
`v4.32.2`), so the dependency shapes ARE compatible — but a `module`-style
file (which every file in this project's `RayoBoolos` library is) cannot
`import` a non-`module` file at all (confirmed: `error: cannot import
non-module Rayo.BoolosB0Core from module`, even with plain `import` rather
than `public import`); it would have needed a second, non-`module` file in
between as an adapter. Given Mathlib is already a dependency of this project
(via `Foundation`), reproving the tiny finite-max fact directly against
Mathlib's `Set.Finite`/`Finset.sup` API is *less* machinery than building
that adapter, so that is the route taken below — no cross-project import
needed after all.

**Second definitional choice**: "formula size" cannot be `Foundation`'s own
`Semiformula.complexity` — that function is a pure *logical-nesting-depth*
measure (`rel`/`nrel` contribute `0` regardless of their term arguments, and
`complexity_rew` shows it is literally invariant under all rewriting/
substitution). Using it here would make `BoolosBig_PA` insensitive to
numeral size entirely — e.g. `n` would be nameable by a complexity-`0`
formula for every `n`, making `BoolosBig_PA` unboundedly infinite at every
size and breaking well-definedness outright. So this file defines its own
`tSize`/`fSize`, a genuine symbol/node count (over terms *and* their
argument positions), matching the paper's actual "formula length" reading
and its `O(n)`-numeral-cost finding (`Semiterm.numeral n` is built as an
explicit `n`-fold `+1` chain — see `Operator.numeral` — so `tSize` of it is
linear in `n`, by construction of `tSize` below, not by coincidence).
-/

module

public import RayoBoolos.Domination
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Ring

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### A genuine symbol-count size measure for `ℒₒᵣ` syntax -/

/-- Structural symbol count of a term: `1` per node (`bvar`, or a `func`
application), plus recursively every argument. Since `ArithmeticSemiterm`
formulas here always have `ξ = Empty` (no free "meta"-variables — see
`ArithmeticSemisentence`), the `fvar` case is vacuous. -/
def tSize {n : ℕ} : Semiterm ℒₒᵣ Empty n → ℕ
  |  .bvar _ => 1
  |  .fvar x => x.elim
  | .func _ v => 1 + Finset.univ.sum (fun i => tSize (v i))

/-- Structural symbol count of a formula: `1` per logical node, plus (for
atomic `rel`/`nrel` nodes) the `tSize` of every term argument — unlike
`Semiformula.complexity`, this really does grow with the terms inside an
atomic formula, which is essential: it is exactly what makes numeral size
count. -/
def fSize {n : ℕ} : Semiformula ℒₒᵣ Empty n → ℕ
  |     .verum => 1
  |    .falsum => 1
  |   .rel _ v => 1 + Finset.univ.sum (fun i => tSize (v i))
  |  .nrel _ v => 1 + Finset.univ.sum (fun i => tSize (v i))
  |    .and φ ψ => 1 + fSize φ + fSize ψ
  |     .or φ ψ => 1 + fSize φ + fSize ψ
  |      .all φ => 1 + fSize φ
  |      .exs φ => 1 + fSize φ

@[simp] lemma tSize_pos {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) : 1 ≤ tSize t := by
  cases t with
  | bvar x => simp [tSize]
  | fvar x => exact x.elim
  | func f v => simp [tSize]

@[simp] lemma fSize_pos {n : ℕ} (φ : Semiformula ℒₒᵣ Empty n) : 1 ≤ fSize φ := by
  cases φ <;> simp [fSize] <;> omega

/-! ### Well-definedness: for every bound and every de Bruijn context, there
are only finitely many terms/formulas of `tSize`/`fSize` at most that bound.
This is the concrete, `ℒₒᵣ`-specific replacement for the abstract
finite-max machinery (see the module docstring for why it is reproved here
rather than imported from `rayo-lean/Rayo/BoolosB0Core.lean`). `ℒₒᵣ` has
exactly four function symbols (`zero one : Func 0`, `add mul : Func 2`, no
others at any arity — `Foundation.Syntax.Predicate.Language.ORing`), so the
"finitely many constructors, each of finite/fixed arity" argument is a
concrete four-way case split, not a generic fact about `Language`. -/

private theorem arity0_eq_empty {n : ℕ} (v : Fin 0 → Semiterm ℒₒᵣ Empty n) : v = ![] := by
  funext i; exact i.elim0

private theorem arity2_eq_cons {n : ℕ} (v : Fin 2 → Semiterm ℒₒᵣ Empty n) :
    v = ![v 0, v 1] := by
  funext i; fin_cases i <;> simp

theorem termsUpTo_finite : ∀ bound : ℕ, ∀ n : ℕ, {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ bound}.Finite := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | _ bound ih =>
    intro n
    match bound, ih with
    | 0, _ =>
      have hempty : {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ 0} = ∅ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        have := tSize_pos t
        omega
      rw [hempty]
      exact Set.finite_empty
    | b + 1, ih =>
      have ihb : {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b}.Finite := ih b (by omega) n
      apply Set.Finite.subset
        (s := (Set.range (Semiterm.bvar (n := n)) : Set (Semiterm ℒₒᵣ Empty n))
          ∪ {Semiterm.func Language.ORing.Func.zero ![]}
          ∪ {Semiterm.func Language.ORing.Func.one ![]}
          ∪ (Set.image2 (fun t1 t2 => Semiterm.func Language.ORing.Func.add ![t1, t2])
              {t | tSize t ≤ b} {t | tSize t ≤ b})
          ∪ (Set.image2 (fun t1 t2 => Semiterm.func Language.ORing.Func.mul ![t1, t2])
              {t | tSize t ≤ b} {t | tSize t ≤ b}))
      · exact ((((Set.finite_range _).union (Set.finite_singleton _)).union
          (Set.finite_singleton _)).union (Set.Finite.image2 _ ihb ihb)).union
          (Set.Finite.image2 _ ihb ihb)
      · intro t ht
        simp only [Set.mem_setOf_eq] at ht
        cases t with
        | bvar x => exact Or.inl (Or.inl (Or.inl (Or.inl ⟨x, rfl⟩)))
        | fvar x => exact x.elim
        | @func k f v =>
          cases f with
          | zero =>
            rw [arity0_eq_empty v]
            exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
          | one =>
            rw [arity0_eq_empty v]
            exact Or.inl (Or.inl (Or.inr rfl))
          | add =>
            have hsum : tSize (Semiterm.func Language.ORing.Func.add v) = 1 + tSize (v 0) + tSize (v 1) := by
              simp [tSize, Fin.sum_univ_succ]; omega
            rw [hsum] at ht
            have h0 : v 0 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have := tSize_pos (v 1); simp only [Set.mem_setOf_eq]; omega
            have h1 : v 1 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have := tSize_pos (v 0); simp only [Set.mem_setOf_eq]; omega
            rw [arity2_eq_cons v]
            exact Or.inl (Or.inr (Set.mem_image2_of_mem h0 h1))
          | mul =>
            have hsum : tSize (Semiterm.func Language.ORing.Func.mul v) = 1 + tSize (v 0) + tSize (v 1) := by
              simp [tSize, Fin.sum_univ_succ]; omega
            rw [hsum] at ht
            have h0 : v 0 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have := tSize_pos (v 1); simp only [Set.mem_setOf_eq]; omega
            have h1 : v 1 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have := tSize_pos (v 0); simp only [Set.mem_setOf_eq]; omega
            rw [arity2_eq_cons v]
            exact Or.inr (Set.mem_image2_of_mem h0 h1)

/-- The nine syntactic shapes a formula of `fSize ≤ b + 1` can have: the two
`0`-ary connectives, the four atomic shapes (`ℒₒᵣ` has two relation symbols,
`eq`/`lt`, each usable as `rel` or `nrel`), the two binary connectives, and
the two quantifiers. Indexing the cover by this `Fintype` (rather than one
long chain of `∪`) avoids hand-tracking `Or.inl`/`Or.inr` nesting depth. -/
private inductive FShape
  | ver | fal | eqr | ltr | eqn | ltn | andS | orS | allS | exsS
  deriving Fintype

private def FShape.piece (b n : ℕ) : FShape → Set (Semiformula ℒₒᵣ Empty n)
  | .ver => {Semiformula.verum}
  | .fal => {Semiformula.falsum}
  | .eqr => Set.image2 (fun t1 t2 => Semiformula.rel Language.ORing.Rel.eq ![t1, t2])
      {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} {t | tSize t ≤ b}
  | .ltr => Set.image2 (fun t1 t2 => Semiformula.rel Language.ORing.Rel.lt ![t1, t2])
      {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} {t | tSize t ≤ b}
  | .eqn => Set.image2 (fun t1 t2 => Semiformula.nrel Language.ORing.Rel.eq ![t1, t2])
      {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} {t | tSize t ≤ b}
  | .ltn => Set.image2 (fun t1 t2 => Semiformula.nrel Language.ORing.Rel.lt ![t1, t2])
      {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} {t | tSize t ≤ b}
  | .andS => Set.image2 (fun φ ψ => Semiformula.and φ ψ)
      {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ b} {φ | fSize φ ≤ b}
  | .orS => Set.image2 (fun φ ψ => Semiformula.or φ ψ)
      {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ b} {φ | fSize φ ≤ b}
  | .allS => Semiformula.all '' {φ : Semiformula ℒₒᵣ Empty (n + 1) | fSize φ ≤ b}
  | .exsS => Semiformula.exs '' {φ : Semiformula ℒₒᵣ Empty (n + 1) | fSize φ ≤ b}

theorem formsUpTo_finite : ∀ bound : ℕ, ∀ n : ℕ, {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ bound}.Finite := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | _ bound ih =>
    intro n
    match bound, ih with
    | 0, _ =>
      have hempty : {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ 0} = ∅ := by
        ext φ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        have := fSize_pos φ
        omega
      rw [hempty]
      exact Set.finite_empty
    | b + 1, ih =>
      have ihb : {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ b}.Finite := ih b (by omega) n
      have ihb1 : {φ : Semiformula ℒₒᵣ Empty (n + 1) | fSize φ ≤ b}.Finite := ih b (by omega) (n + 1)
      have htf : {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b}.Finite := termsUpTo_finite b n
      apply Set.Finite.subset (s := ⋃ i : FShape, FShape.piece b n i)
      · apply Set.finite_iUnion
        intro i
        cases i with
        | ver => exact Set.finite_singleton _
        | fal => exact Set.finite_singleton _
        | eqr => exact Set.Finite.image2 _ htf htf
        | ltr => exact Set.Finite.image2 _ htf htf
        | eqn => exact Set.Finite.image2 _ htf htf
        | ltn => exact Set.Finite.image2 _ htf htf
        | andS => exact Set.Finite.image2 _ ihb ihb
        | orS => exact Set.Finite.image2 _ ihb ihb
        | allS => exact Set.Finite.image _ ihb1
        | exsS => exact Set.Finite.image _ ihb1
      · intro φ hφ
        simp only [Set.mem_setOf_eq] at hφ
        cases φ with
        | verum => exact Set.mem_iUnion.mpr ⟨.ver, rfl⟩
        | falsum => exact Set.mem_iUnion.mpr ⟨.fal, rfl⟩
        | @rel n_ k r v =>
          cases r with
          | eq =>
            have h0 : v 0 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h1 := tSize_pos (v 1); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            have h1 : v 1 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h0 := tSize_pos (v 0); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            rw [arity2_eq_cons v]
            exact Set.mem_iUnion.mpr ⟨.eqr, Set.mem_image2_of_mem h0 h1⟩
          | lt =>
            have h0 : v 0 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h1 := tSize_pos (v 1); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            have h1 : v 1 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h0 := tSize_pos (v 0); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            rw [arity2_eq_cons v]
            exact Set.mem_iUnion.mpr ⟨.ltr, Set.mem_image2_of_mem h0 h1⟩
        | @nrel n_ k r v =>
          cases r with
          | eq =>
            have h0 : v 0 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h1 := tSize_pos (v 1); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            have h1 : v 1 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h0 := tSize_pos (v 0); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            rw [arity2_eq_cons v]
            exact Set.mem_iUnion.mpr ⟨.eqn, Set.mem_image2_of_mem h0 h1⟩
          | lt =>
            have h0 : v 0 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h1 := tSize_pos (v 1); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            have h1 : v 1 ∈ {t : Semiterm ℒₒᵣ Empty n | tSize t ≤ b} := by
              have h0 := tSize_pos (v 0); simp [fSize, Fin.sum_univ_succ] at hφ
              simp only [Set.mem_setOf_eq]; omega
            rw [arity2_eq_cons v]
            exact Set.mem_iUnion.mpr ⟨.ltn, Set.mem_image2_of_mem h0 h1⟩
        | and ψ₁ ψ₂ =>
          simp only [fSize] at hφ
          have h1 : ψ₁ ∈ {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ b} := by
            have := fSize_pos ψ₂; simp only [Set.mem_setOf_eq]; omega
          have h2 : ψ₂ ∈ {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ b} := by
            have := fSize_pos ψ₁; simp only [Set.mem_setOf_eq]; omega
          exact Set.mem_iUnion.mpr ⟨.andS, Set.mem_image2_of_mem h1 h2⟩
        | or ψ₁ ψ₂ =>
          simp only [fSize] at hφ
          have h1 : ψ₁ ∈ {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ b} := by
            have := fSize_pos ψ₂; simp only [Set.mem_setOf_eq]; omega
          have h2 : ψ₂ ∈ {φ : Semiformula ℒₒᵣ Empty n | fSize φ ≤ b} := by
            have := fSize_pos ψ₁; simp only [Set.mem_setOf_eq]; omega
          exact Set.mem_iUnion.mpr ⟨.orS, Set.mem_image2_of_mem h1 h2⟩
        | all ψ =>
          simp only [fSize] at hφ
          have hmem : ψ ∈ {φ : Semiformula ℒₒᵣ Empty (n + 1) | fSize φ ≤ b} := by
            simp only [Set.mem_setOf_eq]; omega
          exact Set.mem_iUnion.mpr ⟨.allS, Set.mem_image_of_mem _ hmem⟩
        | exs ψ =>
          simp only [fSize] at hφ
          have hmem : ψ ∈ {φ : Semiformula ℒₒᵣ Empty (n + 1) | fSize φ ≤ b} := by
            simp only [Set.mem_setOf_eq]; omega
          exact Set.mem_iUnion.mpr ⟨.exsS, Set.mem_image_of_mem _ hmem⟩

/-! ### `BoolosBig_PA`, concretely -/

/-- A `T-naming` formula names at most one value: `BOOLOS-B0-WELLDEFINEDNESS.md`
Lemma 1, over `T = 𝗣𝗔`. Proved via soundness (`ℕ` is a model of `𝗣𝗔`,
`Arithmetic.models_Peano`) rather than a syntactic consistency argument: if
`φ` T-names both `k1` and `k2`, both `∀x(φ(x)↔x=k̄1)` and `∀x(φ(x)↔x=k̄2)`
hold in the standard model, so `{x : ℕ | φ(x)} = {k1} = {k2}`. -/
theorem TNamesMeta_unique {φ : ArithmeticSemisentence 1} {k1 k2 : ℕ}
    (h1 : TNamesMeta φ k1) (h2 : TNamesMeta φ k2) : k1 = k2 := by
  have hm1 : ℕ↓[ℒₒᵣ] ⊧ namesSentence φ k1 := models_of_provable inferInstance h1
  have hm2 : ℕ↓[ℒₒᵣ] ⊧ namesSentence φ k2 := models_of_provable inferInstance h2
  simp [namesSentence, models_iff] at hm1 hm2
  have e1 : φ.Evalb (M := ℕ) ![k1] := (hm1 k1).mpr rfl
  exact (hm2 k1).mp e1

/-- The values nameable by a formula of `fSize ≤ n`: `BoolosBig_PA(n)`'s
defining set, `BOOLOS-B0-WELLDEFINEDNESS.md`'s `Ψₙ`. -/
def namedValues (n : ℕ) : Set ℕ := {k | ∃ φ : ArithmeticSemisentence 1, fSize φ ≤ n ∧ TNamesMeta φ k}

theorem namedValues_finite (n : ℕ) : (namedValues n).Finite := by
  have hcover : namedValues n ⊆ ⋃ φ ∈ {φ : ArithmeticSemisentence 1 | fSize φ ≤ n}, {k | TNamesMeta φ k} := by
    rintro k ⟨φ, hφ, hk⟩
    exact Set.mem_biUnion hφ hk
  apply Set.Finite.subset _ hcover
  apply Set.Finite.biUnion (formsUpTo_finite n 1)
  intro φ _
  rcases Set.eq_empty_or_nonempty {k | TNamesMeta φ k} with he | ⟨k0, hk0⟩
  · rw [he]; exact Set.finite_empty
  · have : {k | TNamesMeta φ k} = {k0} := by
      ext k; constructor
      · intro hk; exact TNamesMeta_unique hk hk0
      · rintro rfl; exact hk0
    rw [this]; exact Set.finite_singleton _

/-- **`BoolosBig_PA`, concretely**: the largest value nameable by a formula
of `fSize ≤ n` (or `0` if none), matching `BOOLOS-B0-WELLDEFINEDNESS.md`'s
`BoolosBig_T(n) = sup Ψₙ = max Ψₙ`. Defined via `Finset.sup`/`id` rather than
a `dite` + `Classical.choose` max extraction: `Finset.sup ∅ id = ⊥ = 0`
handles the empty case for free, and `Finset.le_sup` (`namedValues_le_BoolosBig_PA`
below) is the only property the domination argument actually needs — genuine
achievement of the sup is not required. -/
noncomputable def BoolosBig_PA (n : ℕ) : ℕ := (namedValues_finite n).toFinset.sup id

theorem namedValues_le_BoolosBig_PA {n k : ℕ} (hk : k ∈ namedValues n) : k ≤ BoolosBig_PA n := by
  apply Finset.le_sup (f := id)
  exact (Set.Finite.mem_toFinset _).mpr hk

theorem namedValues_mono {n m : ℕ} (h : n ≤ m) : namedValues n ⊆ namedValues m := by
  rintro k ⟨φ, hφ, hk⟩
  exact ⟨φ, hφ.trans h, hk⟩

/-- `BoolosBig_PA` is monotone: more budget can only name more (or equally
much). -/
theorem BoolosBig_PA_mono {n m : ℕ} (h : n ≤ m) : BoolosBig_PA n ≤ BoolosBig_PA m := by
  apply Finset.sup_mono
  intro k hk
  exact (Set.Finite.mem_toFinset _).mpr (namedValues_mono h ((Set.Finite.mem_toFinset _).mp hk))

/-! ### The `O(n)` numeral-size fact, mechanized -/

private theorem add_symbol_eq : (Language.Add.add : Language.Func ℒₒᵣ 2) = Language.ORing.Func.add := rfl
private theorem zero_symbol_eq : (Language.Zero.zero : Language.Func ℒₒᵣ 0) = Language.ORing.Func.zero := rfl
private theorem one_symbol_eq : (Language.One.one : Language.Func ℒₒᵣ 0) = Language.ORing.Func.one := rfl

private theorem add_operator_eq {l : ℕ} (v : Fin 2 → Semiterm ℒₒᵣ Empty l) :
    (Semiterm.Operator.Add.add : Semiterm.Operator ℒₒᵣ 2).operator v = Semiterm.func Language.ORing.Func.add v := by
  simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, add_symbol_eq,
    Rew.emb_eq_id, Rew.func]
  congr 1

private theorem zero_const_eq {n : ℕ} :
    ((Semiterm.Operator.Zero.zero : Semiterm.Operator ℒₒᵣ 0).operator ![] : Semiterm ℒₒᵣ Empty n) =
      Semiterm.func Language.ORing.Func.zero ![] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Zero.term_eq, zero_symbol_eq]

private theorem one_const_eq {n : ℕ} :
    ((Semiterm.Operator.One.one : Semiterm.Operator ℒₒᵣ 0).operator ![] : Semiterm ℒₒᵣ Empty n) =
      Semiterm.func Language.ORing.Func.one ![] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.One.term_eq, one_symbol_eq]

private theorem numeral_succ_eq {n z : ℕ} (hz : z ≠ 0) :
    (Semiterm.numeral (z + 1) : Semiterm ℒₒᵣ Empty n) =
      Semiterm.func Language.ORing.Func.add ![Semiterm.numeral z, Semiterm.numeral 1] := by
  show ((Semiterm.Operator.numeral ℒₒᵣ (z + 1) : Semiterm.Operator ℒₒᵣ 0).operator ![] : Semiterm ℒₒᵣ Empty n) = _
  rw [Semiterm.Operator.numeral_succ hz, Semiterm.Operator.operator_comp, add_operator_eq]
  congr 1
  funext x
  fin_cases x <;> rfl

theorem tSize_numeral_succ {n z : ℕ} (hz : z ≠ 0) :
    tSize (Semiterm.numeral (z + 1) : Semiterm ℒₒᵣ Empty n) =
      tSize (Semiterm.numeral z : Semiterm ℒₒᵣ Empty n) + tSize (Semiterm.numeral 1 : Semiterm ℒₒᵣ Empty n) + 1 := by
  rw [numeral_succ_eq hz]
  simp [tSize, Fin.sum_univ_succ]
  omega

theorem tSize_numeral_zero (n : ℕ) : tSize (Semiterm.numeral 0 : Semiterm ℒₒᵣ Empty n) = 1 := by
  show tSize ((Semiterm.Operator.numeral ℒₒᵣ 0 : Semiterm.Operator ℒₒᵣ 0).operator ![] : Semiterm ℒₒᵣ Empty n) = 1
  rw [Semiterm.Operator.numeral_zero, zero_const_eq]
  simp [tSize]

theorem tSize_numeral_one (n : ℕ) : tSize (Semiterm.numeral 1 : Semiterm ℒₒᵣ Empty n) = 1 := by
  show tSize ((Semiterm.Operator.numeral ℒₒᵣ 1 : Semiterm.Operator ℒₒᵣ 0).operator ![] : Semiterm ℒₒᵣ Empty n) = 1
  rw [Semiterm.Operator.numeral_one, one_const_eq]
  simp [tSize]

/-- The `O(n)`-numeral-cost fact `BOOLOS-B3-PAPER-VERIFICATION.md` §3 relies
on, mechanized directly against `Foundation`'s own recursive definition of
`Semiterm.numeral` (an explicit `n`-fold `1+1+…+1` chain, `Operator.numeral`)
rather than assumed: `tSize` of the numeral for `k` is linear in `k`. -/
theorem tSize_numeral_le (n k : ℕ) : tSize (Semiterm.numeral k : Semiterm ℒₒᵣ Empty n) ≤ 2 * k + 1 := by
  induction k with
  | zero => simp [tSize_numeral_zero]
  | succ z ih =>
    rcases Nat.eq_zero_or_pos z with hz | hz
    · subst hz; simp [tSize_numeral_one]
    · rw [tSize_numeral_succ (by omega), tSize_numeral_one]
      omega

/-! ### `fSize` under substitution: the previously-stuck bridging lemma, closed

A follow-up session's finding, contrary to the previous session's conclusion
recorded in the note this section used to contain: `Rewriting.app`/`▹` for
the concrete `Semiformula ℒₒᵣ Empty` instance **is** `rfl`-transparent on
`verum`/`falsum`/`and`/`or`. `Rewriting.app` for this instance is literally
`Semiformula.rew`, itself `rewAux` (`Foundation/FirstOrder/Basic/Syntax/
Rew.lean`) bundled into a `→ˡᶜ` hom; `rewAux` is a direct structural pattern
match on its formula argument, and `verum`/`falsum`/`and`/`or` are exactly
its non-recursing base-case patterns, so `ω ▹ Semiformula.verum =
Semiformula.verum` (and the `and`/`or` analogues) close by plain `rfl` —
verified directly before writing the lemmas below. It is not clear why the
previous attempt's `rfl` failed; possibly a different concrete goal shape
(e.g. under a bigger elaboration context) was actually tried. Recorded here
as named `@[simp]` facts so the induction below closes uniformly, alongside
`Foundation`'s own `Rewriting.app_all`/`app_exs` (quantifiers) and
`rew_rel_eq_comp`/`rew_nrel_eq_comp` (atomic, both already `@[simp]`). -/

/-- `tSize` is invariant under `Rew.bShift` — `bShift` (`= Rew.map Fin.succ
id`) only relabels bound-variable indices, it never adds or removes a
function-symbol node, so the symbol count is unchanged. -/
private theorem tSize_bShift {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) :
    tSize (Rew.bShift t) = tSize t := by
  induction t with
  | bvar x => simp [tSize, Rew.bShift, Rew.map]
  | fvar x => exact x.elim
  | func f v ih => simp [tSize, ih, Rew.func, Function.comp_apply]

/-- Term-level substitution bound: if every bound variable of a term is sent
by `ω` to a term of `tSize ≤ B` (`B ≥ 1`), the whole term's `tSize` blows up
by at most a factor `B`. The "term-level analogue" the module docstring
refers to — structural induction, closing via `Rew.func`'s existing
`@[simp]` lemma. -/
private theorem tSize_rew_le {n m : ℕ} (ω : Rew ℒₒᵣ Empty n Empty m) (B : ℕ) (hB : 1 ≤ B)
    (hω : ∀ i : Fin n, tSize (ω (Semiterm.bvar i)) ≤ B) :
    ∀ t : Semiterm ℒₒᵣ Empty n, tSize (ω t) ≤ tSize t * B := by
  intro t
  induction t with
  | bvar x => simpa [tSize] using hω x
  | fvar x => exact x.elim
  | func f v ih =>
    simp only [Rew.func, tSize, Function.comp_apply]
    calc 1 + Finset.univ.sum (fun i => tSize (ω (v i)))
        ≤ 1 + Finset.univ.sum (fun i => tSize (v i) * B) := by
          exact Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => ih i)) 1
      _ ≤ B + Finset.univ.sum (fun i => tSize (v i) * B) := by omega
      _ = (1 + Finset.univ.sum (fun i => tSize (v i))) * B := by
          rw [add_mul, one_mul, Finset.sum_mul]

/-- `ω.q` sends every bound variable of `Fin (n+1)` to a term of `tSize ≤ B`,
given `ω` does so on `Fin n` (`B ≥ 1`) — the inductive step needed to push
`tSize_rew_le`'s hypothesis under a quantifier, via `Foundation`'s
`q_bvar_zero`/`q_bvar_succ` plus `tSize_bShift` above. -/
private theorem q_bound {n m : ℕ} (ω : Rew ℒₒᵣ Empty n Empty m) (B : ℕ) (hB : 1 ≤ B)
    (hω : ∀ i : Fin n, tSize (ω (Semiterm.bvar i)) ≤ B) :
    ∀ i : Fin (n + 1), tSize (ω.q (Semiterm.bvar i)) ≤ B := by
  intro i
  cases i using Fin.cases with
  | zero => simpa [tSize] using hB
  | succ j => simpa [tSize_bShift] using hω j

/-- **The previously-stuck bridging lemma, closed.** Substitution blows up a
formula's `fSize` by at most a multiplicative factor `B`, when every bound
variable is sent to a term of `tSize ≤ B` (`B ≥ 1`). Structural induction on
`φ`, generalizing the codomain `m`/rewriting `ω`/bound `B` at each step
(needed for the quantifier cases, which recurse at `n + 1` against `ω.q`).
Uses plain `induction φ with` (raw-constructor case tags, matching how the
rest of this file splits on `Semiformula` — see `formsUpTo_finite` above),
**not** `Semiformula.rec'`: the latter states its `and`/`or`/`verum`/`falsum`
cases using the `⋏`/`⋎`/`⊤`/`⊥` `LogicalConnective` notation, which — despite
being `rfl`-equal to the raw `Semiformula.and`/`.or`/`.verum`/`.falsum`
constructors `fSize` pattern-matches on — is not syntactically what `simp`
matches against by default; the raw-constructor recursion sidesteps that
entirely. -/
private theorem rew_app_verum {n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ Empty n₁ Empty n₂) :
    ω ▹ (Semiformula.verum : Semiformula ℒₒᵣ Empty n₁) = Semiformula.verum := rfl

private theorem rew_app_falsum {n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ Empty n₁ Empty n₂) :
    ω ▹ (Semiformula.falsum : Semiformula ℒₒᵣ Empty n₁) = Semiformula.falsum := rfl

theorem fSize_rew_le {n : ℕ} (φ : Semiformula ℒₒᵣ Empty n) :
    ∀ {m : ℕ} (ω : Rew ℒₒᵣ Empty n Empty m) (B : ℕ), 1 ≤ B →
      (∀ i : Fin n, tSize (ω (Semiterm.bvar i)) ≤ B) → fSize (ω ▹ φ) ≤ fSize φ * B := by
  induction φ with
  | verum =>
    intro m ω B hB _
    rw [rew_app_verum]; simpa [fSize] using hB
  | falsum =>
    intro m ω B hB _
    rw [rew_app_falsum]; simpa [fSize] using hB
  | rel r v =>
    intro m ω B hB hω
    simp only [Semiformula.rew_rel_eq_comp, fSize]
    calc 1 + Finset.univ.sum (fun i => tSize (ω (v i)))
        ≤ 1 + Finset.univ.sum (fun i => tSize (v i) * B) :=
          Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => tSize_rew_le ω B hB hω (v i))) 1
      _ ≤ B + Finset.univ.sum (fun i => tSize (v i) * B) := by omega
      _ = (1 + Finset.univ.sum (fun i => tSize (v i))) * B := by
          rw [add_mul, one_mul, Finset.sum_mul]
  | nrel r v =>
    intro m ω B hB hω
    simp only [Semiformula.rew_nrel_eq_comp, fSize]
    calc 1 + Finset.univ.sum (fun i => tSize (ω (v i)))
        ≤ 1 + Finset.univ.sum (fun i => tSize (v i) * B) :=
          Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => tSize_rew_le ω B hB hω (v i))) 1
      _ ≤ B + Finset.univ.sum (fun i => tSize (v i) * B) := by omega
      _ = (1 + Finset.univ.sum (fun i => tSize (v i))) * B := by
          rw [add_mul, one_mul, Finset.sum_mul]
  | and φ ψ ihφ ihψ =>
    intro m ω B hB hω
    have h1 := ihφ ω B hB hω
    have h2 := ihψ ω B hB hω
    have hgoal : ω ▹ (Semiformula.and φ ψ) = Semiformula.and (ω ▹ φ) (ω ▹ ψ) := rfl
    rw [hgoal]
    simp only [fSize]
    have hring : fSize φ * B + fSize ψ * B + B = (1 + fSize φ + fSize ψ) * B := by ring
    omega
  | or φ ψ ihφ ihψ =>
    intro m ω B hB hω
    have h1 := ihφ ω B hB hω
    have h2 := ihψ ω B hB hω
    have hgoal : ω ▹ (Semiformula.or φ ψ) = Semiformula.or (ω ▹ φ) (ω ▹ ψ) := rfl
    rw [hgoal]
    simp only [fSize]
    have hring : fSize φ * B + fSize ψ * B + B = (1 + fSize φ + fSize ψ) * B := by ring
    omega
  | all φ ih =>
    intro m ω B hB hω
    have hq := q_bound ω B hB hω
    have hih := ih (ω.q) B hB hq
    have hgoal : ω ▹ (Semiformula.all φ) = Semiformula.all (ω.q ▹ φ) := rfl
    rw [hgoal]
    simp only [fSize]
    have hring : fSize φ * B + B = (1 + fSize φ) * B := by ring
    omega
  | exs φ ih =>
    intro m ω B hB hω
    have hq := q_bound ω B hB hω
    have hih := ih (ω.q) B hB hq
    have hgoal : ω ▹ (Semiformula.exs φ) = Semiformula.exs (ω.q ▹ φ) := rfl
    rw [hgoal]
    simp only [fSize]
    have hring : fSize φ * B + B = (1 + fSize φ) * B := by ring
    omega

/-- Specialized to `graphAt n := graph ⇜ ![#0, numeral n]`
(`ProvablyTotal.graphAt`, `Domination.lean`): its `fSize` is bounded by
`fSize graph * (2n + 1)`, i.e. `O(n)`, matching the paper-verification's
finding — the substitution vector's two components are `#0` (`tSize = 1`)
and `numeral n` (`tSize ≤ 2n + 1` by `tSize_numeral_le`), both `≤ 2n + 1`. -/
theorem fSize_graphAt_le {f : ℕ → ℕ} (P : ProvablyTotal f) (n : ℕ) :
    fSize (P.graphAt n) ≤ fSize P.graph * (2 * n + 1) := by
  have hb : ∀ i : Fin 2, tSize ((Rew.subst (![#0, Semiterm.numeral n] : Fin 2 → Semiterm ℒₒᵣ Empty 1))
      (Semiterm.bvar i)) ≤ 2 * n + 1 := by
    intro i
    cases i using Fin.cases with
    | zero => simp [tSize]
    | succ j =>
      cases j using Fin.cases with
      | zero => simpa using tSize_numeral_le 1 n
      | succ k => exact k.elim0
  exact fSize_rew_le P.graph (Rew.subst ![#0, Semiterm.numeral n]) (2 * n + 1) (by omega) hb

end RayoBoolos

#print axioms RayoBoolos.BoolosBig_PA_mono
#print axioms RayoBoolos.namedValues_le_BoolosBig_PA
#print axioms RayoBoolos.tSize_numeral_le
#print axioms RayoBoolos.fSize_rew_le
#print axioms RayoBoolos.fSize_graphAt_le
