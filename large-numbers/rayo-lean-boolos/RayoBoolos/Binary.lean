/-
`RayoBoolos.Binary` — the logarithmic naming bound: for every computable `f`
there is a constant `C` with `f n ≤ BoolosBig_PA (C + 6·log₂ n)` for all `n`
(`BoolosBig_PA_log_bound`). This is the first claim of Theorem 1 in
`large-numbers/BOOLOS-IS-BUSY-BEAVER-CLASS.md`.

`Minimization.lean` substitutes the unary numeral for `n` into the naming
formula, which costs `O(n)` symbols. Here the input enters once, as a binary
numeral `bin n` built from `0`, `1`, `+`, `·` (`tSize_bin_le`: at most
`6·log₂ n + 1` symbols), bound to a variable: `logName θ n (y) :≡ ∃x (x =
bin n ∧ minGraph θ (y, x))`. In every model of `𝗣𝗔⁻` the term `bin n`
denotes `n` (`val_bin`), so `logName θ n` is equivalent there to the
unary-numeral formula and names the same number (`logName_names`).
-/

module

public import RayoBoolos.Minimization

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Size of sums, products and constants -/

theorem tSize_add {k : ℕ} (t u : Semiterm ℒₒᵣ Empty k) :
    tSize (‘!!t + !!u’ : Semiterm ℒₒᵣ Empty k) = 1 + tSize t + tSize u := by
  have : (‘!!t + !!u’ : Semiterm ℒₒᵣ Empty k) = Semiterm.func Language.ORing.Func.add ![t, u] := by
    simp only [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func]
    congr 1
  rw [this]; simp [tSize, Fin.sum_univ_succ]; omega

theorem tSize_mul {k : ℕ} (t u : Semiterm ℒₒᵣ Empty k) :
    tSize (‘!!t * !!u’ : Semiterm ℒₒᵣ Empty k) = 1 + tSize t + tSize u := by
  have : (‘!!t * !!u’ : Semiterm ℒₒᵣ Empty k) = Semiterm.func Language.ORing.Func.mul ![t, u] := by
    simp only [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq, Rew.func]
    congr 1
  rw [this]; simp [tSize, Fin.sum_univ_succ]; omega

theorem tSize_zero (k : ℕ) : tSize (‘0’ : Semiterm ℒₒᵣ Empty k) = 1 := by
  simpa using tSize_numeral_zero k

theorem tSize_one (k : ℕ) : tSize (‘1’ : Semiterm ℒₒᵣ Empty k) = 1 := by
  simpa using tSize_numeral_one k

/-! ### Binary numerals -/

/-- The binary numeral for `n`: `0`, `1`, `(1+1)·t` or `(1+1)·t + 1`. -/
def bin (k : ℕ) (n : ℕ) : Semiterm ℒₒᵣ Empty k :=
  if n = 0 then ‘0’
  else if n = 1 then ‘1’
  else if n % 2 = 0 then ‘(1 + 1) * !!(bin k (n / 2))’
  else ‘(1 + 1) * !!(bin k (n / 2)) + 1’
termination_by n
decreasing_by all_goals omega

/-- A binary numeral has logarithmic size. -/
theorem tSize_bin_le (k n : ℕ) : tSize (bin k n) ≤ 6 * Nat.log2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [bin]
    by_cases h0 : n = 0
    · simp [h0, tSize_zero]
    by_cases h1 : n = 1
    · simp [h1, tSize_one]
    have hlog : Nat.log2 n = Nat.log2 (n / 2) + 1 := by
      rw [Nat.log2_def]; simp [show 2 ≤ n by omega]
    have ih' := ih (n / 2) (by omega)
    by_cases h2 : n % 2 = 0
    · simp only [h0, h1, h2, ↓reduceIte, tSize_mul, tSize_add, tSize_one]
      omega
    · simp only [h0, h1, h2, ↓reduceIte, tSize_mul, tSize_add, tSize_one]
      omega

/-- A binary numeral denotes its number, in every model of `𝗣𝗔⁻`. -/
theorem val_bin {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (k n : ℕ) (b : Fin k → M) :
    (bin k n).val b Empty.elim = (n : M) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [bin]
    by_cases h0 : n = 0
    · simp [h0]
    by_cases h1 : n = 1
    · simp [h1]
    have ih' := ih (n / 2) (by omega)
    by_cases h2 : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      simp only [h0, h1, h2, ↓reduceIte]
      simp [ih']
      conv_rhs => rw [hn]
      push_cast; ring
    · have hn : n = 2 * (n / 2) + 1 := by omega
      simp only [h0, h1, h2, ↓reduceIte]
      simp [ih']
      conv_rhs => rw [hn]
      push_cast; ring

/-! ### Naming `f n` in `O(1) + O(log n)` symbols -/

/-- `logName θ n (y)`: `∃ x, x = bin(n) ∧ minGraph θ (y, x)`. The input `n`
enters through a single binary numeral. -/
noncomputable def logName (θ : ArithmeticSemisentence 2) (n : ℕ) : ArithmeticSemisentence 1 :=
  “y. ∃ x, x = !!(bin 2 n) ∧ !(minGraph θ) y x”

lemma eval_logName {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (θ : ArithmeticSemisentence 2) (n : ℕ) (y : M) :
    (logName θ n).Evalb (M := M) ![y] ↔ (minGraph θ).Evalb (M := M) ![y, ORingStructure.numeral n] := by
  simp [logName, val_bin, numeral_eq_natCast]

theorem logName_names {θ : ArithmeticSemisentence 2} (hθ : Hierarchy 𝚺 1 θ) {f : ℕ → ℕ}
    (hf : ∀ y x : ℕ, θ.Evalb (M := ℕ) ![y, x] ↔ y = f x) (n : ℕ) :
    TNamesMeta (logName θ n) (f n) := by
  have hN : TNamesMeta (minGraph θ ⇜ ![#0, Semiterm.numeral n]) (f n) := minGraph_names hθ hf n
  unfold TNamesMeta namesSentence at hN ⊢
  apply Arithmetic.complete.{0} (𝗣𝗔 : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory hM
  have hw := models_of_provable hM hN
  simp [models_iff] at hw
  simp [models_iff]
  intro x
  rw [eval_logName]
  exact hw x

theorem fSize_logName_le (θ : ArithmeticSemisentence 2) (n : ℕ) :
    fSize (logName θ n) ≤ fSize (minGraph θ) + 5 + 6 * Nat.log2 n := by
  have hb : ∀ i : Fin 2, tSize ((Rew.subst (![#1, #0] : Fin 2 → Semiterm ℒₒᵣ Empty 2)) (Semiterm.bvar i)) ≤ 1 := by
    intro i; cases i using Fin.cases with
    | zero => simp [tSize]
    | succ j => cases j using Fin.cases with
      | zero => simp [tSize]
      | succ k => exact k.elim0
  have h1 : fSize (minGraph θ ⇜ (![#1, #0] : Fin 2 → Semiterm ℒₒᵣ Empty 2)) ≤ fSize (minGraph θ) * 1 :=
    fSize_rew_le (minGraph θ) (Rew.subst ![#1, #0]) 1 (le_refl 1) hb
  have h2 : fSize (“#0 = !!(bin 2 n)” : ArithmeticSemisentence 2) = 1 + (1 + tSize (bin 2 n)) := by
    simp [Semiformula.Operator.eq_def, fSize, Fin.sum_univ_succ, tSize]
  have h3 := tSize_bin_le 2 n
  have final : 1 + (1 + fSize (“#0 = !!(bin 2 n)” : ArithmeticSemisentence 2) +
      fSize (minGraph θ ⇜ (![#1, #0] : Fin 2 → Semiterm ℒₒᵣ Empty 2))) ≤
        fSize (minGraph θ) + 5 + 6 * Nat.log2 n := by omega
  unfold logName
  simp only [fSize]
  exact final

/-- **The logarithmic bound.** For every computable `f` there is a constant
`C` such that `f n` is `𝗣𝗔`-nameable within budget `C + 6·log₂ n`, for every
`n`. -/
theorem BoolosBig_PA_log_bound {f : ℕ → ℕ} (hf : Computable f) :
    ∃ C, ∀ n, f n ≤ BoolosBig_PA (C + 6 * Nat.log2 n) := by
  obtain ⟨θ, hθ, hθf⟩ := computable_graph hf
  refine ⟨fSize (minGraph θ) + 5, fun n => ?_⟩
  exact namedValues_le_BoolosBig_PA ⟨logName θ n, fSize_logName_le θ n, logName_names hθ hθf n⟩

end RayoBoolos

#print axioms RayoBoolos.logName_names
#print axioms RayoBoolos.BoolosBig_PA_log_bound
