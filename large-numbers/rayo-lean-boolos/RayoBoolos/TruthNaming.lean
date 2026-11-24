/-
`RayoBoolos.TruthNaming`: naming by truth, the first two middle rungs, and a
concrete instance of Claim B of `THE-LADDER.md` §3.

A formula `φ(x)` *names `m` by truth* when `m` is the only natural number
`φ` is true of in `ℕ` (`TruthNames`). For a level `Hierarchy Γ k` of the
arithmetical hierarchy (`Foundation`'s liberal classes), `TruthBig Γ k n` is
the largest number named by truth by a formula of that level with at most
`n` symbols. Paper proofs for every level are in
`large-numbers/MIDDLE-RUNGS.md`. This file proves:

* `TruthBig`, `TruthBig_mono`, `TruthBig_pi_le_sigma_succ`,
  `TruthBig_sigma_le_sigma_succ`: well defined, monotone in the budget and in
  the level, and `Π_k ⊆ Σ_{k+1}`.
* **Rung 1, lower half.** `BB_le_TruthBig_sigma1`: one constant `C` with
  `BB N ≤ TruthBig 𝚺 1 (C + 6·log₂ N)`.
* **Rung 1, upper half.** `TruthBig_sigma1_le_BB`: a function `h` with
  `TruthBig 𝚺 1 n ≤ BB (h n)`. Truth of a `Σ₁` sentence is found by proof
  search in `𝗣𝗔` (`Σ₁`-completeness one way, soundness the other).
* **The next rung.** `BB_lt_TruthBig_sigma2`: one constant `C` with
  `BB N < TruthBig 𝚺 2 (C + 6·log₂ N)`. The `Σ₂` formula says "`x` is one
  more than the largest output of a halting program with code `≤ N`".
* **Claim B, concretely.** `sigma2_record_gt_sigma1`: there are `C` and `h`
  with `TruthBig 𝚺 1 n < TruthBig 𝚺 2 (C + 6·log₂ (h n))` for every `n`.
  The record of `Σ₁`-truth naming at budget `n` is beaten by a `Σ₂` formula
  whose size grows only with the logarithm of `h n`.

`h` comes from `Foundation`'s Gödel numbering of formulas and is not bounded
explicitly here, as with `templateCode` in `UpperBound.lean`.
-/

module

public import RayoBoolos.UpperBound

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Naming by truth -/

/-- `φ` names `m` by truth: in `ℕ`, `φ(x)` holds exactly when `x = m`. -/
def TruthNames (φ : ArithmeticSemisentence 1) (m : ℕ) : Prop :=
  ∀ x : ℕ, φ.Evalb (M := ℕ) ![x] ↔ x = m

lemma TruthNames.unique {φ : ArithmeticSemisentence 1} {a b : ℕ}
    (ha : TruthNames φ a) (hb : TruthNames φ b) : a = b :=
  (hb a).mp ((ha a).mpr rfl)

/-- Numbers named by truth by a formula of level `Hierarchy Γ k` with at most
`n` symbols. -/
def truthValues (Γ : Polarity) (k n : ℕ) : Set ℕ :=
  {m | ∃ φ : ArithmeticSemisentence 1, Hierarchy Γ k φ ∧ fSize φ ≤ n ∧ TruthNames φ m}

theorem truthValues_finite (Γ : Polarity) (k n : ℕ) : (truthValues Γ k n).Finite := by
  have hcover : truthValues Γ k n ⊆
      ⋃ φ ∈ {φ : ArithmeticSemisentence 1 | fSize φ ≤ n}, {m | TruthNames φ m} := by
    rintro m ⟨φ, _, hφ, hm⟩
    exact Set.mem_biUnion hφ hm
  apply Set.Finite.subset _ hcover
  apply Set.Finite.biUnion (formsUpTo_finite n 1)
  intro φ _
  rcases Set.eq_empty_or_nonempty {m | TruthNames φ m} with he | ⟨m0, hm0⟩
  · rw [he]; exact Set.finite_empty
  · have : {m | TruthNames φ m} = {m0} := by
      ext m; constructor
      · intro hm; exact TruthNames.unique hm hm0
      · rintro rfl; exact hm0
    rw [this]; exact Set.finite_singleton _

/-- **The truth-naming function** of level `Hierarchy Γ k`: the largest number
named by truth by a formula of that level with at most `n` symbols (`0` if
there is none). -/
noncomputable def TruthBig (Γ : Polarity) (k n : ℕ) : ℕ :=
  (truthValues_finite Γ k n).toFinset.sup id

theorem le_TruthBig {Γ : Polarity} {k n m : ℕ} {φ : ArithmeticSemisentence 1}
    (hφ : Hierarchy Γ k φ) (hs : fSize φ ≤ n) (hm : TruthNames φ m) : m ≤ TruthBig Γ k n :=
  Finset.le_sup (f := id) ((Set.Finite.mem_toFinset _).mpr ⟨φ, hφ, hs, hm⟩)

theorem TruthBig_le_of {Γ : Polarity} {k n B : ℕ}
    (h : ∀ m ∈ truthValues Γ k n, m ≤ B) : TruthBig Γ k n ≤ B :=
  Finset.sup_le fun m hm => h m ((Set.Finite.mem_toFinset _).mp hm)

theorem TruthBig_le_of_class {Γ Γ' : Polarity} {k k' : ℕ}
    (hc : ∀ φ : ArithmeticSemisentence 1, Hierarchy Γ k φ → Hierarchy Γ' k' φ) {n m : ℕ}
    (hnm : n ≤ m) : TruthBig Γ k n ≤ TruthBig Γ' k' m := by
  apply TruthBig_le_of
  rintro v ⟨φ, hφ, hs, hv⟩
  exact le_TruthBig (hc φ hφ) (le_trans hs hnm) hv

theorem TruthBig_mono {Γ : Polarity} {k n m : ℕ} (h : n ≤ m) :
    TruthBig Γ k n ≤ TruthBig Γ k m :=
  TruthBig_le_of_class (fun _ hφ => hφ) h

/-- `Π_k` truth naming is part of `Σ_{k+1}` truth naming. -/
theorem TruthBig_pi_le_sigma_succ (k n : ℕ) : TruthBig 𝚷 k n ≤ TruthBig 𝚺 (k + 1) n :=
  TruthBig_le_of_class (fun _ hφ => hφ.accum 𝚺) le_rfl

theorem TruthBig_sigma_le_sigma_succ (k n : ℕ) : TruthBig 𝚺 k n ≤ TruthBig 𝚺 (k + 1) n :=
  TruthBig_le_of_class (fun _ hφ => hφ.accum 𝚺) le_rfl

/-! ### Substituting a binary numeral once -/

/-- `binWrap F n (y)`: `∃ x, x = bin(n) ∧ F(y, x)`. -/
noncomputable def binWrap (F : ArithmeticSemisentence 2) (n : ℕ) : ArithmeticSemisentence 1 :=
  “y. ∃ x, x = !!(bin 2 n) ∧ !F y x”

lemma eval_binWrap (F : ArithmeticSemisentence 2) (n y : ℕ) :
    (binWrap F n).Evalb (M := ℕ) ![y] ↔ F.Evalb (M := ℕ) ![y, n] := by
  simp [binWrap, val_bin]

lemma binWrap_sigma {F : ArithmeticSemisentence 2} {s : ℕ} (hF : Hierarchy 𝚺 (s + 1) F) (n : ℕ) :
    Hierarchy 𝚺 (s + 1) (binWrap F n) := by
  simp [binWrap, hF]

theorem fSize_binWrap_le (F : ArithmeticSemisentence 2) (n : ℕ) :
    fSize (binWrap F n) ≤ fSize F + 5 + 6 * Nat.log2 n := by
  have hb : ∀ i : Fin 2, tSize ((Rew.subst (![#1, #0] : Fin 2 → Semiterm ℒₒᵣ Empty 2)) (Semiterm.bvar i)) ≤ 1 := by
    intro i; cases i using Fin.cases with
    | zero => simp [tSize]
    | succ j => cases j using Fin.cases with
      | zero => simp [tSize]
      | succ k => exact k.elim0
  have h1 : fSize (F ⇜ (![#1, #0] : Fin 2 → Semiterm ℒₒᵣ Empty 2)) ≤ fSize F * 1 :=
    fSize_rew_le F (Rew.subst ![#1, #0]) 1 (le_refl 1) hb
  have h2 : fSize (“#0 = !!(bin 2 n)” : ArithmeticSemisentence 2) = 1 + (1 + tSize (bin 2 n)) := by
    simp [Semiformula.Operator.eq_def, fSize, Fin.sum_univ_succ, tSize]
  have h3 := tSize_bin_le 2 n
  have final : 1 + (1 + fSize (“#0 = !!(bin 2 n)” : ArithmeticSemisentence 2) +
      fSize (F ⇜ (![#1, #0] : Fin 2 → Semiterm ℒₒᵣ Empty 2))) ≤
        fSize F + 5 + 6 * Nat.log2 n := by omega
  unfold binWrap
  simp only [fSize]
  exact final

/-! ### Rung 1, lower half: Busy Beaver is reached by `Σ₁` truth -/

/-- For a partial recursive `g`, every value `v ∈ g e` is named by truth by a
`Σ₁` formula of size `C + 6·log₂ e`: "`x` is the output of `g` at `e`". No
search and no proofs are involved. -/
theorem TruthBig_sigma1_partrec_bound {g : ℕ →. ℕ} (hg : Partrec g) :
    ∃ C, ∀ e v, v ∈ g e → v ≤ TruthBig 𝚺 1 (C + 6 * Nat.log2 e) := by
  obtain ⟨θ, hθ, hθg⟩ := partrec_graph hg
  refine ⟨fSize θ + 5, fun e v hv => ?_⟩
  refine le_TruthBig (binWrap_sigma hθ e) (fSize_binWrap_le θ e) (fun x => ?_)
  rw [eval_binWrap, hθg]
  exact ⟨fun hx => Part.mem_unique hx hv, fun h => h ▸ hv⟩

private theorem sup_partUpTo_le_truth {g : ℕ → Part ℕ} (hg : Partrec g) :
    ∃ C, ∀ N, (partUpTo_finite g N).toFinset.sup id ≤ TruthBig 𝚺 1 (C + 6 * Nat.log2 N) := by
  obtain ⟨C, hC⟩ := TruthBig_sigma1_partrec_bound hg
  refine ⟨C, fun N => ?_⟩
  apply Finset.sup_le
  intro v hv
  obtain ⟨e, he, hve⟩ := (Set.Finite.mem_toFinset _).mp hv
  have hmono : C + 6 * Nat.log2 e ≤ C + 6 * Nat.log2 N := by
    have := log2_mono he; omega
  exact le_trans (hC e v hve) (TruthBig_mono hmono)

/-- **Busy Beaver lower bound for `Σ₁` truth naming.** -/
theorem BB_le_TruthBig_sigma1 :
    ∃ C, ∀ N, BB N ≤ TruthBig 𝚺 1 (C + 6 * Nat.log2 N) :=
  sup_partUpTo_le_truth progOut_partrec

theorem BBtime_le_TruthBig_sigma1 :
    ∃ C, ∀ N, BBtime N ≤ TruthBig 𝚺 1 (C + 6 * Nat.log2 N) :=
  sup_partUpTo_le_truth progTime_partrec

/-! ### Rung 1, upper half: `Σ₁` truth is found by proof search -/

lemma sentence_eval_subst (φ : ArithmeticSemisentence 1) (k : ℕ) :
    (ℕ↓[ℒₒᵣ] ⊧ (φ/[↑k] : ArithmeticSentence)) ↔ φ.Evalb (M := ℕ) ![k] := by
  simp [models_iff, Semiformula.eval_substs]

/-- **Truth search.** A partial recursive `g` which, given the code of a `Σ₁`
formula that names `m` by truth, returns `m`. -/
theorem exists_truth_search :
    ∃ g : ℕ →. ℕ, Partrec g ∧ ∀ (φ : ArithmeticSemisentence 1) (m : ℕ),
      Hierarchy 𝚺 1 φ → TruthNames φ m → m ∈ g (Encodable.encode φ) := by
  obtain ⟨g, hg, hsound, hdom⟩ := re_select (provAt_re 𝗣𝗔)
  refine ⟨g, hg, fun φ m hφ hm => ?_⟩
  have hcode : (⌜φ⌝ : ℕ) = Encodable.encode φ := Sentence.quote_eq_encode_nat _
  -- `𝗣𝗔` proves `φ(m̄)`, by `Σ₁`-completeness.
  have hσ : Hierarchy 𝚺 1 (φ/[↑m] : ArithmeticSentence) := by simp [hφ]
  have hprov : (𝗣𝗔 : ArithmeticTheory) ⊢ (φ/[↑m] : ArithmeticSentence) :=
    (sigma_one_completeness_iff hσ).mp ((sentence_eval_subst φ m).mpr ((hm m).mpr rfl))
  have hP : ProvAt 𝗣𝗔 (Encodable.encode φ) m := by
    rw [← hcode]; exact (provAt_spec 𝗣𝗔 φ m).mpr hprov
  have hd := hdom _ m hP
  have hv := hsound _ _ (Part.get_mem hd)
  -- Whatever the search returns is provable, hence true, hence `m`.
  have hv' : ProvAt 𝗣𝗔 ⌜φ⌝ ((g (Encodable.encode φ)).get hd) := by rw [hcode]; exact hv
  have htrue : ℕ↓[ℒₒᵣ] ⊧ (φ/[↑((g (Encodable.encode φ)).get hd)] : ArithmeticSentence) :=
    models_of_provable inferInstance ((provAt_spec 𝗣𝗔 φ _).mp hv')
  have heq : (g (Encodable.encode φ)).get hd = m :=
    (hm _).mp ((sentence_eval_subst φ _).mp htrue)
  rw [← heq]; exact Part.get_mem hd

open Nat.Partrec (Code) in
/-- **Busy Beaver upper bound for `Σ₁` truth naming.** There is a function
`h` (from the Gödel numbering, independent of everything else) with
`TruthBig 𝚺 1 n ≤ BB (h n)`. -/
theorem TruthBig_sigma1_le_BB : ∃ h : ℕ → ℕ, ∀ n, TruthBig 𝚺 1 n ≤ BB (h n) := by
  obtain ⟨g, hg, hsearch⟩ := exists_truth_search
  obtain ⟨cg, hcg⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hg)
  let prog : ArithmeticSemisentence 1 → ℕ := fun φ =>
    Encodable.encode (Code.comp cg (Code.const (Encodable.encode φ)))
  refine ⟨fun n => (formsUpTo_finite n 1).toFinset.sup prog, fun n => ?_⟩
  apply TruthBig_le_of
  rintro m ⟨φ, hφ, hs, hm⟩
  have hle : prog φ ≤ (formsUpTo_finite n 1).toFinset.sup prog :=
    Finset.le_sup (f := prog) ((Set.Finite.mem_toFinset _).mpr hs)
  have hout : m ∈ progOut (prog φ) := by
    have := hsearch φ m hφ hm
    simp only [progOut, prog, Denumerable.ofNat_encode]
    simpa [Code.eval, Code.eval_const, hcg] using this
  apply Finset.le_sup (f := id)
  exact (Set.Finite.mem_toFinset _).mpr ⟨prog φ, hle, hout⟩

/-! ### The next rung: `Σ₂` truth names one more than Busy Beaver -/

section Sigma2

/-- A `Σ₁` graph of `progOut`, fixed once. -/
noncomputable def outGraph : ArithmeticSemisentence 2 :=
  Classical.choose (partrec_graph progOut_partrec)

lemma outGraph_sigma1 : Hierarchy 𝚺 1 outGraph :=
  (Classical.choose_spec (partrec_graph progOut_partrec)).1

lemma outGraph_spec (v e : ℕ) : outGraph.Evalb (M := ℕ) ![v, e] ↔ v ∈ progOut e :=
  (Classical.choose_spec (partrec_graph progOut_partrec)).2 v e

/-- `ubOut (x, z)`: every output of a halting program with code `≤ z` is `< x`. -/
noncomputable def ubOut : ArithmeticSemisentence 2 :=
  “x z. ∀ e <⁺ z, ∀ v, !outGraph v e → v < x”

/-- `reachOut (x, z)`: below `x` every number is `≤` some such output. -/
noncomputable def reachOut : ArithmeticSemisentence 2 :=
  “x z. ∀ w < x, ∃ e <⁺ z, ∃ v, !outGraph v e ∧ w ≤ v”

/-- `succBB (x, z)`: `x` is one more than the largest output of a halting
program with code `≤ z`. -/
noncomputable def succBB : ArithmeticSemisentence 2 := ubOut ⋏ reachOut

lemma ubOut_pi1 : Hierarchy 𝚷 1 ubOut := by
  simp [ubOut, outGraph_sigma1]

lemma reachOut_sigma1 : Hierarchy 𝚺 1 reachOut := by
  simp [reachOut, outGraph_sigma1]

lemma succBB_sigma2 : Hierarchy 𝚺 2 succBB := by
  simp only [succBB, Hierarchy.and_iff]
  exact ⟨ubOut_pi1.accum 𝚺, reachOut_sigma1.accum 𝚺⟩

lemma eval_succBB (x N : ℕ) :
    succBB.Evalb (M := ℕ) ![x, N] ↔
      (∀ e ≤ N, ∀ v, v ∈ progOut e → v < x) ∧
        (∀ w < x, ∃ e ≤ N, ∃ v, v ∈ progOut e ∧ w ≤ v) := by
  simp [succBB, ubOut, reachOut, Semiformula.eval_substs, outGraph_spec]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun e he v hv => h1 e (le_def.mpr (Nat.eq_or_lt_of_le he)) v hv, fun w hw => ?_⟩
    obtain ⟨e, he, v, hv, hwv⟩ := h2 w hw
    refine ⟨e, ?_, v, hv, ?_⟩
    · rcases le_def.mp he with h | h <;> omega
    · exact hwv
  · rintro ⟨h1, h2⟩
    refine ⟨fun e he v hv => h1 e (by rcases le_def.mp he with h | h <;> omega) v hv,
      fun w hw => ?_⟩
    obtain ⟨e, he, v, hv, hwv⟩ := h2 w hw
    exact ⟨e, le_def.mpr (Nat.eq_or_lt_of_le he), v, hv, hwv⟩

open Nat.Partrec (Code) in
lemma zero_mem_progOut_zero : (0 : ℕ) ∈ progOut 0 := by
  have e : Denumerable.ofNat Code (Encodable.encode Code.zero) = Code.zero :=
    Denumerable.ofNat_encode _
  have h0 : Encodable.encode Code.zero = 0 := by
    simp [Code.encodeCode_eq, Code.encodeCode]
  rw [h0] at e
  simp only [progOut, e, Code.eval]
  exact Part.mem_some 0

lemma BB_mem (N : ℕ) : BB N ∈ outputsUpTo N := by
  have hne : (partUpTo_finite progOut N).toFinset.Nonempty :=
    ⟨0, (Set.Finite.mem_toFinset _).mpr ⟨0, Nat.zero_le _, zero_mem_progOut_zero⟩⟩
  obtain ⟨v, hv, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  have : BB N = v := hsup
  rw [this]
  exact (Set.Finite.mem_toFinset _).mp hv

lemma le_BB {N e v : ℕ} (he : e ≤ N) (hv : v ∈ progOut e) : v ≤ BB N :=
  Finset.le_sup (f := id) ((Set.Finite.mem_toFinset _).mpr ⟨e, he, hv⟩)

/-- `succBB` holds of `(x, N)` exactly when `x = BB N + 1`. -/
lemma succBB_iff (x N : ℕ) : succBB.Evalb (M := ℕ) ![x, N] ↔ x = BB N + 1 := by
  rw [eval_succBB]
  obtain ⟨e₀, he₀, hv₀⟩ := BB_mem N
  constructor
  · rintro ⟨hub, hreach⟩
    have h1 : BB N < x := hub e₀ he₀ _ hv₀
    by_contra hne
    obtain ⟨e, he, v, hv, hle⟩ := hreach (BB N + 1) (by omega)
    have := le_BB he hv
    omega
  · rintro rfl
    refine ⟨fun e he v hv => Nat.lt_succ_of_le (le_BB he hv), fun w hw => ?_⟩
    exact ⟨e₀, he₀, BB N, hv₀, by omega⟩

/-- **The next rung.** One constant `C` with `BB N < TruthBig 𝚺 2 (C + 6·log₂ N)`:
a `Σ₂` formula of that size names `BB N + 1` by truth. -/
theorem BB_lt_TruthBig_sigma2 :
    ∃ C, ∀ N, BB N < TruthBig 𝚺 2 (C + 6 * Nat.log2 N) := by
  refine ⟨fSize succBB + 5, fun N => ?_⟩
  have hname : TruthNames (binWrap succBB N) (BB N + 1) := fun x => by
    rw [eval_binWrap, succBB_iff]
  exact Nat.lt_of_succ_le
    (le_TruthBig (binWrap_sigma succBB_sigma2 N) (fSize_binWrap_le succBB N) hname)

/-- **Claim B of `THE-LADDER.md`, concretely.** `R` is `Σ₁` truth naming and
`R⁺` is `Σ₂` truth naming. The record of `R` at budget `n` is beaten by an
`R⁺` formula of size `C + 6·log₂ (h n)`. -/
theorem sigma2_record_gt_sigma1 :
    ∃ (C : ℕ) (h : ℕ → ℕ), ∀ n, TruthBig 𝚺 1 n < TruthBig 𝚺 2 (C + 6 * Nat.log2 (h n)) := by
  obtain ⟨h, hh⟩ := TruthBig_sigma1_le_BB
  obtain ⟨C, hC⟩ := BB_lt_TruthBig_sigma2
  exact ⟨C, h, fun n => lt_of_le_of_lt (hh n) (hC (h n))⟩

end Sigma2

end RayoBoolos

#print axioms RayoBoolos.TruthBig_pi_le_sigma_succ
#print axioms RayoBoolos.BB_le_TruthBig_sigma1
#print axioms RayoBoolos.TruthBig_sigma1_le_BB
#print axioms RayoBoolos.BB_lt_TruthBig_sigma2
#print axioms RayoBoolos.sigma2_record_gt_sigma1
