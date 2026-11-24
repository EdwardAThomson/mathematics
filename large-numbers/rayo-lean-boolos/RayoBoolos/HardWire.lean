/-
`RayoBoolos.HardWire`: building an input into a program, with a short code
number, and the Busy Beaver upper bound with an explicit `n log n` rescaling
(`PROVABLE-NAMING-REPORT.md` Theorem 6(b)).

`CompactCode.lean` proves the upper bound in the form "one fixed program,
run on an input of `O(n log n)` bits". To compare with `BB` of
`BusyBeaver.lean`, which runs programs on input `0`, the input has to be
built into the program. Mathlib's `Code.const m` writes `m` in unary as `m`
nested compositions, and every nesting roughly squares the code number, so
`Code.const m` has a code number of about `2^(2^m)`: useless here.

This file writes `m` instead as a balanced binary tree of its bits.

* `binCode j m`: a program (on any input) outputting `binTree j m`, a tree of
  the `2^j` low bits of `m` built with `Nat.pair`.
* `binDecode j t`: unfolds the tree `t` `j` times and reads off the bits;
  primitive recursive (`primrec_binDecode`), and
  `binDecode j (binTree j m) = m % 2^(2^j)` (`binDecode_binTree`).
* `encode_binCode_le`: `binCode j m` has a code number below `2^(8·2^j)`, so
  `O(2^j)` bits: a balanced tree of depth `j` doubles the bit length of its
  leaves `j` times, and there are `2^j` leaves.
* `hardwire c j m = comp c (pair (const j) (binCode j m))` runs `c` on
  `⟪j, binTree j m⟫`.
* `exists_hardwire`: for every partial recursive `f` there is `A` such that
  for every input `m` of fewer than `L` bits some program number `e` with
  `e < 2^(A·L)` (so fewer than `A·L` bits) computes `f m` on input `0`.
* `BoolosBigIn_le_BB_nlogn'`: for a consistent, computably axiomatized
  `T ⊇ 𝗣𝗔⁻`, `BoolosBigIn T n ≤ BB (2^(C·(n+1)·(log₂(n+1)+6)))`.
* `busy_beaver_sandwich`: both halves in the same units (bits of program):
  `BB (2^s) ≤ BoolosBigIn T (C + 6·s)` and
  `BoolosBigIn T n ≤ BB (2^(C·(n+1)·(log₂(n+1)+6)))`.
* `TruthBig_sigma1_le_BB_nlogn`: the same upper bound for `Σ₁` truth naming.
-/

module

public import RayoBoolos.CompactCode
public import RayoBoolos.TruthCompact

@[expose] public section

namespace RayoBoolos

open LO LO.FirstOrder LO.FirstOrder.Arithmetic Encodable
open Nat.Partrec (Code)

/-! ### Constants as balanced binary trees of bits -/

/-- The `2^j` low bits of `m` as a balanced tree: a leaf is a bit, a node is
`Nat.pair (high half) (low half)`. -/
def binTree : ℕ → ℕ → ℕ
  | 0, m => m % 2
  | j + 1, m => Nat.pair (binTree j (m / 2 ^ 2 ^ j)) (binTree j (m % 2 ^ 2 ^ j))

/-- A program outputting `binTree j m` on every input. -/
def binCode : ℕ → ℕ → Code
  | 0, m => Code.const (m % 2)
  | j + 1, m => Code.pair (binCode j (m / 2 ^ 2 ^ j)) (binCode j (m % 2 ^ 2 ^ j))

lemma eval_binCode : ∀ j m x, (binCode j m).eval x = Part.some (binTree j m)
  | 0, m, x => by simp [binCode, binTree, Code.eval_const]
  | j + 1, m, x => by
    simp [binCode, binTree, Code.eval, eval_binCode j, Seq.seq]

/-- One unfolding step: replace every number by the two halves of its pair. -/
def expand (l : List ℕ) : List ℕ := l.flatMap fun x => [x.unpair.1, x.unpair.2]

/-- A list of bits, most significant first, read as a number. -/
def digVal (l : List ℕ) : ℕ := l.foldl (fun a d => 2 * a + d) 0

/-- The decoder: unfold `j` times, then read the bits. -/
def binDecode (j t : ℕ) : ℕ := digVal (expand^[j] [t])

lemma expand_append (a b : List ℕ) : expand (a ++ b) = expand a ++ expand b := by
  simp [expand, List.flatMap_append]

lemma iterate_expand_append (j : ℕ) :
    ∀ a b : List ℕ, expand^[j] (a ++ b) = expand^[j] a ++ expand^[j] b := by
  induction j with
  | zero => intro a b; rfl
  | succ j ih =>
    intro a b
    simp only [Function.iterate_succ_apply]
    rw [expand_append, ih]

lemma foldl_bits (B : List ℕ) :
    ∀ c, B.foldl (fun a d => 2 * a + d) c = c * 2 ^ B.length + digVal B := by
  induction B with
  | nil => intro c; simp [digVal]
  | cons d B ih =>
    intro c
    simp only [List.foldl_cons, digVal]
    rw [ih, ih (2 * 0 + d)]
    simp [pow_succ]
    ring

lemma digVal_append (A B : List ℕ) : digVal (A ++ B) = digVal A * 2 ^ B.length + digVal B := by
  rw [digVal, List.foldl_append, foldl_bits]
  rfl

lemma binTree_spec : ∀ j m, (expand^[j] [binTree j m]).length = 2 ^ j ∧
    digVal (expand^[j] [binTree j m]) = m % 2 ^ 2 ^ j
  | 0, m => by simp [binTree, digVal]
  | j + 1, m => by
    have e : expand^[j + 1] [binTree (j + 1) m] =
        expand^[j] [binTree j (m / 2 ^ 2 ^ j)] ++ expand^[j] [binTree j (m % 2 ^ 2 ^ j)] := by
      rw [Function.iterate_succ_apply, ← iterate_expand_append]
      simp [binTree, expand]
    obtain ⟨h1, h2⟩ := binTree_spec j (m / 2 ^ 2 ^ j)
    obtain ⟨h3, h4⟩ := binTree_spec j (m % 2 ^ 2 ^ j)
    rw [e, List.length_append, digVal_append, h1, h2, h3, h4, Nat.mod_mod]
    constructor
    · rw [pow_succ]; ring
    · have hsq : (2 : ℕ) ^ 2 ^ (j + 1) = 2 ^ 2 ^ j * 2 ^ 2 ^ j := by
        rw [pow_succ, pow_mul, sq]
      rw [hsq, Nat.mod_mul]
      ring

theorem binDecode_binTree (j m : ℕ) : binDecode j (binTree j m) = m % 2 ^ 2 ^ j :=
  (binTree_spec j m).2

theorem primrec_binDecode : Primrec₂ binDecode := by
  have hexp : Primrec expand := by
    unfold expand
    refine Primrec.list_flatMap Primrec.id ?_
    exact (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
        (Primrec.const []))).to₂
  have hdig : Primrec digVal := by
    unfold digVal
    exact Primrec.list_foldl Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  have hit : Primrec fun p : ℕ × ℕ => expand^[p.1] [p.2] :=
    Primrec.nat_iterate Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (hexp.comp Primrec.snd).to₂
  exact (hdig.comp hit).to₂

/-! ### Code-number bounds -/

lemma pair_bound {X Y Q : ℕ} (hX : 8 * (X + 1) ≤ Q) (hY : 8 * (Y + 1) ≤ Q) :
    8 * (4 * Nat.pair X Y + 7) ≤ Q ^ 2 := by
  have hp := Nat.pair_lt_max_add_one_sq X Y
  have hM : 8 * (max X Y + 1) ≤ Q := by
    rcases le_total X Y with h | h
    · rw [max_eq_right h]; exact hY
    · rw [max_eq_left h]; exact hX
  have hsq : (8 * (max X Y + 1)) ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left hM 2
  have h1 : 1 ≤ max X Y + 1 := by omega
  nlinarith

lemma encode_pair (a b : Code) : encode (Code.pair a b) = 4 * Nat.pair (encode a) (encode b) + 4 := by
  simp only [Code.encodeCode_eq, Code.encodeCode]; ring

lemma encode_comp (a b : Code) : encode (Code.comp a b) = 4 * Nat.pair (encode a) (encode b) + 6 := by
  simp only [Code.encodeCode_eq, Code.encodeCode]; ring

lemma pow_8_mul_two_pow (A j : ℕ) : ((2 : ℕ) ^ (A * 2 ^ j)) ^ 2 = 2 ^ (A * 2 ^ (j + 1)) := by
  rw [← pow_mul, pow_succ]; ring_nf

lemma encode_binCode_le (A : ℕ) (hA : 8 ≤ A) :
    ∀ j m, 8 * (encode (binCode j m) + 1) ≤ 2 ^ (A * 2 ^ j)
  | 0, m => by
    have h256 : (256 : ℕ) ≤ 2 ^ A := by
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;>
      simp [binCode, h, Code.const, Code.encodeCode_eq, Code.encodeCode, Nat.pair] <;> omega
  | j + 1, m => by
    rw [binCode, encode_pair, ← pow_8_mul_two_pow]
    have := pair_bound (encode_binCode_le A hA j (m / 2 ^ 2 ^ j))
      (encode_binCode_le A hA j (m % 2 ^ 2 ^ j))
    omega

lemma encode_const_le (A : ℕ) (hA : 8 ≤ A) :
    ∀ j, 8 * (encode (Code.const j) + 1) ≤ 2 ^ (A * 2 ^ j)
  | 0 => by
    have h256 : (256 : ℕ) ≤ 2 ^ A := by
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA
    simp [Code.const, Code.encodeCode_eq, Code.encodeCode]; omega
  | j + 1 => by
    rw [Code.const, encode_comp, ← pow_8_mul_two_pow]
    have hj := encode_const_le A hA j
    have hsucc : 8 * (encode Code.succ + 1) ≤ 2 ^ (A * 2 ^ j) := by
      have : (256 : ℕ) ≤ 2 ^ (A * 2 ^ j) := by
        calc (256 : ℕ) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ (A * 2 ^ j) := Nat.pow_le_pow_right (by norm_num)
              (le_trans hA (Nat.le_mul_of_pos_right _ (by positivity)))
      simp [Code.encodeCode_eq, Code.encodeCode]; omega
    have := pair_bound hsucc hj
    omega

/-! ### Building the input into the program -/

/-- Run `c` on `⟪j, binTree j m⟫`, on any input. -/
def hardwire (c : Code) (j m : ℕ) : Code := Code.comp c (Code.pair (Code.const j) (binCode j m))

lemma eval_hardwire (c : Code) (j m x : ℕ) :
    (hardwire c j m).eval x = c.eval (Nat.pair j (binTree j m)) := by
  simp [hardwire, Code.eval, Code.eval_const, eval_binCode, Seq.seq]

lemma encode_hardwire_lt (c : Code) (j m : ℕ) :
    encode (hardwire c j m) < 2 ^ (8 * (encode c + 1) * 2 ^ (j + 2)) := by
  set A := 8 * (encode c + 1) with hAdef
  have hA : 8 ≤ A := by omega
  have hc : 8 * (encode c + 1) ≤ 2 ^ (A * 2 ^ (j + 1)) := by
    calc 8 * (encode c + 1) = A := rfl
      _ ≤ 2 ^ A := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (A * 2 ^ (j + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by positivity))
  have hin : 8 * (encode (Code.pair (Code.const j) (binCode j m)) + 1) ≤ 2 ^ (A * 2 ^ (j + 1)) := by
    rw [encode_pair, ← pow_8_mul_two_pow]
    have := pair_bound (encode_const_le A hA j) (encode_binCode_le A hA j m)
    omega
  have hout := pair_bound hc hin
  rw [pow_8_mul_two_pow] at hout
  have e2 : (2 : ℕ) ^ (A * 2 ^ (j + 1 + 1)) = 2 ^ (A * 2 ^ (j + 2)) := rfl
  rw [e2] at hout
  rw [hardwire, encode_comp]
  omega

/-- **Hard-wiring an input.** For every partial recursive `f` there is a
constant `A` such that, for every input `m` of fewer than `L` bits, some
program with code number below `2^(A·L)` outputs `f m` on input `0`. -/
theorem exists_hardwire {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ A, ∀ L m, Nat.log2 m < L → ∃ e, e < 2 ^ (A * L) ∧ progOut e = f m := by
  have hF : Partrec fun p : ℕ => f (binDecode p.unpair.1 p.unpair.2) :=
    hf.comp (primrec_binDecode.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hF)
  refine ⟨8 * (8 * (encode c + 1)), fun L m hm => ?_⟩
  have hL : L ≠ 0 := by omega
  set j := Nat.log2 L + 1 with hj
  have hLj : L < 2 ^ j := Nat.lt_log2_self
  have hjL : 2 ^ j ≤ 2 * L := by
    rw [hj, pow_succ]; have := Nat.log2_self_le hL; omega
  have hmj : m < 2 ^ 2 ^ j := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; positivity
    · have h1 : m < 2 ^ L := (Nat.log2_lt (by omega)).mp hm
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hLj.le)
  refine ⟨encode (hardwire c j m), ?_, ?_⟩
  · refine lt_of_lt_of_le (encode_hardwire_lt c j m) (Nat.pow_le_pow_right (by norm_num) ?_)
    have : 2 ^ (j + 2) ≤ 8 * L := by rw [pow_add]; omega
    calc 8 * (encode c + 1) * 2 ^ (j + 2) ≤ 8 * (encode c + 1) * (8 * L) :=
          Nat.mul_le_mul_left _ this
      _ = _ := by ring
  · unfold progOut
    rw [Denumerable.ofNat_encode, eval_hardwire, hc]
    simp [binDecode_binTree, Nat.mod_eq_of_lt hmj]

/-! ### The Busy Beaver upper bound with explicit rescaling -/

lemma BB_mono {N N' : ℕ} (h : N ≤ N') : BB N ≤ BB N' := by
  apply Finset.sup_mono
  intro v hv
  obtain ⟨e, he, hve⟩ := (Set.Finite.mem_toFinset _).mp hv
  exact (Set.Finite.mem_toFinset _).mpr ⟨e, le_trans he h, hve⟩

/-- **Theorem 6(b).** For a consistent, computably axiomatized `T ⊇ 𝗣𝗔⁻`
there is `C` with `BoolosBigIn T n ≤ BB (2^(C · nlogBound n))`: every number
`T` names in size `n` is the output of a program of `O(n log n)` bits. -/
theorem BoolosBigIn_le_BB_nlogn (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ∃ C, ∀ n, BoolosBigIn T n ≤ BB (2 ^ (C * nlogBound n)) := by
  obtain ⟨g, hg, hsearch⟩ := exists_compact_search T
  obtain ⟨A, hA⟩ := exists_hardwire hg
  refine ⟨A, fun n => BoolosBigIn_le fun k hk => ?_⟩
  obtain ⟨m, hm, hkm⟩ := hsearch n k hk
  obtain ⟨e, he, hprog⟩ := hA (nlogBound n) m hm
  exact le_BB he.le (hprog ▸ hkm)

/-- Theorem 6(b) with round constants:
`BoolosBigIn T n ≤ BB (2^(C·(n+1)·(log₂(n+1)+6)))`. -/
theorem BoolosBigIn_le_BB_nlogn' (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ∃ C, ∀ n, BoolosBigIn T n ≤ BB (2 ^ (C * (n + 1) * (Nat.log2 (n + 1) + 6))) := by
  obtain ⟨C, hC⟩ := BoolosBigIn_le_BB_nlogn T
  refine ⟨40 * C, fun n => le_trans (hC n) (BB_mono (Nat.pow_le_pow_right (by norm_num) ?_))⟩
  calc C * nlogBound n ≤ C * (40 * (n + 1) * (Nat.log2 (n + 1) + 6)) :=
        Nat.mul_le_mul_left _ (nlogBound_le n)
    _ = _ := by ring

/-- **The Busy Beaver sandwich, both halves in bits of program.** For a
consistent, computably axiomatized `T ⊇ 𝗣𝗔⁻` there is one constant `C` with,
for all `n` and `s`,

* `BB (2^s) ≤ BoolosBigIn T (C + 6·s)` (programs of `s` bits are beaten by
  naming formulas of size `C + 6s`), and
* `BoolosBigIn T n ≤ BB (2^(C·(n+1)·(log₂(n+1)+6)))` (formulas of size `n`
  are beaten by programs of `O(n log n)` bits). -/
theorem busy_beaver_sandwich (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ∃ C, ∀ n s, BB (2 ^ s) ≤ BoolosBigIn T (C + 6 * s) ∧
      BoolosBigIn T n ≤ BB (2 ^ (C * (n + 1) * (Nat.log2 (n + 1) + 6))) := by
  obtain ⟨C₁, h₁⟩ := BB_le_BoolosBigIn
  obtain ⟨C₂, h₂⟩ := BoolosBigIn_le_BB_nlogn' T
  refine ⟨max C₁ C₂, fun n s => ⟨?_, ?_⟩⟩
  · refine le_trans (h₁ T (2 ^ s)) (BoolosBigIn_mono ?_)
    rw [Nat.log2_two_pow]; omega
  · exact le_trans (h₂ n) (BB_mono (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_max_right _ _)))))

/-- For `T = 𝗣𝗔`. -/
theorem BoolosBig_PA_le_BB_nlogn :
    ∃ C, ∀ n, BoolosBig_PA n ≤ BB (2 ^ (C * (n + 1) * (Nat.log2 (n + 1) + 6))) := by
  obtain ⟨C, hC⟩ := BoolosBigIn_le_BB_nlogn' 𝗣𝗔
  exact ⟨C, fun n => by rw [← BoolosBigIn_PA]; exact hC n⟩

/-- **`Σ₁` truth naming, upper bound with explicit rescaling.**
`TruthBig 𝚺 1 n ≤ BB (2^(C·(n+1)·(log₂(n+16)+1)))`. -/
theorem TruthBig_sigma1_le_BB_nlogn :
    ∃ C, ∀ n, TruthBig 𝚺 1 n ≤ BB (2 ^ (C * (n + 1) * (Nat.log2 (n + 16) + 1))) := by
  obtain ⟨g, hg, hs⟩ := TruthBig_sigma1_compact
  obtain ⟨A, hA⟩ := exists_hardwire hg
  refine ⟨4 * A, fun n => Finset.sup_le fun m hm => ?_⟩
  obtain ⟨x, hx, hmx⟩ := hs n m ((Set.Finite.mem_toFinset _).mp hm)
  obtain ⟨e, he, hprog⟩ := hA _ x hx
  refine le_BB (le_trans he.le (Nat.pow_le_pow_right (by norm_num) ?_)) (hprog ▸ hmx)
  calc A * (4 * n * (Nat.log2 (n + 16) + 1)) ≤ A * (4 * (n + 1) * (Nat.log2 (n + 16) + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by ring

end RayoBoolos

#print axioms RayoBoolos.primrec_binDecode
#print axioms RayoBoolos.binDecode_binTree
#print axioms RayoBoolos.exists_hardwire
#print axioms RayoBoolos.BoolosBigIn_le_BB_nlogn
#print axioms RayoBoolos.BoolosBigIn_le_BB_nlogn'
#print axioms RayoBoolos.busy_beaver_sandwich
#print axioms RayoBoolos.BoolosBig_PA_le_BB_nlogn
#print axioms RayoBoolos.TruthBig_sigma1_le_BB_nlogn
