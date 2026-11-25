/-
`RayoBoolos.CompactCode`: an `O(n log n)`-bit code for formulas, with a
primitive recursive decoder into `Foundation`'s Gödel numbering, and the
explicit `n log n` rescaling in the upper half of the Busy Beaver sandwich
(`PROVABLE-NAMING-REPORT.md` Theorem 6(b), Corollary 7(b)).

* `ftoks φ`: `φ` in Polish notation, one token per symbol (`fSize φ` tokens,
  each below `cbase φ = 14 + arity + fSize φ`).
* `compactCode φ = ⟪b, ⟪length, tokens as base-b digits⟫⟫`;
  `log2_compactCode_lt`: it has fewer than `4·|φ|·(log₂(b+1)+1)` bits.
* `compactDecode`: a stack machine from compact codes to `Encodable.encode`,
  primitive recursive (`primrec_compactDecode`) and correct
  (`compactDecode_compactCode`).
* `exists_compact_search`: one partial recursive function outputs every
  number `T` names in size `≤ n` on an input of `< nlogBound n` bits.
* `BoolosBigIn_le_any_nlogn'`:
  `BoolosBigIn T n ≤ BoolosBigIn U (C + 240·(n+1)·(log₂(n+1)+6))`.
-/

module

public import RayoBoolos.UpperBound

@[expose] public section

namespace RayoBoolos

open LO LO.FirstOrder LO.FirstOrder.Arithmetic Encodable

/-! ### Tokens (Polish notation) -/

/-- Polish-notation tokens of a term. `0, 1` constants, `2, 3` for `+, ×`,
`14 + i` for the bound variable `#i`. -/
def ttoks {k : ℕ} : Semiterm ℒₒᵣ Empty k → List ℕ
  | .bvar i => [14 + (i : ℕ)]
  | .fvar x => x.elim
  | .func Language.ORing.Func.zero _ => [0]
  | .func Language.ORing.Func.one _ => [1]
  | .func Language.ORing.Func.add v => 2 :: (ttoks (v 0) ++ ttoks (v 1))
  | .func Language.ORing.Func.mul v => 3 :: (ttoks (v 0) ++ ttoks (v 1))

/-- Polish-notation tokens of a formula. -/
def ftoks {k : ℕ} : Semiformula ℒₒᵣ Empty k → List ℕ
  | .verum => [8]
  | .falsum => [9]
  | .rel Language.ORing.Rel.eq v => 4 :: (ttoks (v 0) ++ ttoks (v 1))
  | .rel Language.ORing.Rel.lt v => 5 :: (ttoks (v 0) ++ ttoks (v 1))
  | .nrel Language.ORing.Rel.eq v => 6 :: (ttoks (v 0) ++ ttoks (v 1))
  | .nrel Language.ORing.Rel.lt v => 7 :: (ttoks (v 0) ++ ttoks (v 1))
  | .and φ ψ => 10 :: (ftoks φ ++ ftoks ψ)
  | .or φ ψ => 11 :: (ftoks φ ++ ftoks ψ)
  | .all φ => 12 :: ftoks φ
  | .exs φ => 13 :: ftoks φ

/-! ### The decoder: a stack machine run on the reversed token list -/

def vec2 (a b : ℕ) : ℕ := Nat.pair a (Nat.pair b 0 + 1) + 1

def dstep (s : List ℕ) (t : ℕ) : List ℕ :=
  if t < 2 then (Nat.pair 2 (Nat.pair 0 (Nat.pair t 0)) + 1) :: s
  else if t < 8 then
    (Nat.pair (if t < 4 then 2 else if t < 6 then 0 else 1)
      (Nat.pair 2 (Nat.pair (t % 2) (vec2 s.headI s.tail.headI))) + 1) :: s.tail.tail
  else if t < 10 then (Nat.pair (t - 6) 0 + 1) :: s
  else if t < 12 then (Nat.pair (t - 6) (Nat.pair s.headI s.tail.headI) + 1) :: s.tail.tail
  else if t < 14 then (Nat.pair (t - 6) s.headI + 1) :: s.tail
  else (Nat.pair 0 (t - 14) + 1) :: s

lemma ttoks_run {k : ℕ} (t : Semiterm ℒₒᵣ Empty k) :
    ∀ s, (ttoks t).reverse.foldl dstep s = encode t :: s := by
  induction t with
  | bvar i =>
    intro s; simp [ttoks, dstep, Semiterm.encode_eq_toNat, Semiterm.toNat]
    repeat rw [if_neg (by omega)]
  | fvar x => exact x.elim
  | func f v ih =>
    intro s
    cases f with
    | zero => simp [ttoks, dstep, Semiterm.encode_eq_toNat, Semiterm.toNat]; rfl
    | one => simp [ttoks, dstep, Semiterm.encode_eq_toNat, Semiterm.toNat]; rfl
    | add =>
      simp [ttoks, List.foldl_append, ih, dstep, vec2, Semiterm.encode_eq_toNat, Semiterm.toNat,
        Matrix.vecToNat]
      exact ⟨rfl, rfl, rfl⟩
    | mul =>
      simp [ttoks, List.foldl_append, ih, dstep, vec2, Semiterm.encode_eq_toNat, Semiterm.toNat,
        Matrix.vecToNat]
      exact ⟨rfl, rfl, rfl⟩

lemma ftoks_run {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) :
    ∀ s, (ftoks φ).reverse.foldl dstep s = encode φ :: s := by
  induction φ with
  | verum => intro s; simp [ftoks, dstep]; rfl
  | falsum => intro s; simp [ftoks, dstep]; rfl
  | rel r v =>
    intro s
    cases r <;>
    · simp only [ftoks, List.reverse_cons, List.reverse_append, List.foldl_append, List.foldl_cons, List.foldl_nil, ttoks_run]
      simp [dstep, vec2, Semiformula.encode_rel, Matrix.vecToNat]
      exact ⟨rfl, rfl, rfl⟩
  | nrel r v =>
    intro s
    cases r <;>
    · simp only [ftoks, List.reverse_cons, List.reverse_append, List.foldl_append, List.foldl_cons, List.foldl_nil, ttoks_run]
      simp [dstep, vec2, Semiformula.encode_nrel, Matrix.vecToNat]
      exact ⟨rfl, rfl, rfl⟩
  | and φ ψ ihφ ihψ =>
    intro s; simp [ftoks, List.foldl_append, ihφ, ihψ, dstep]; rfl
  | or φ ψ ihφ ihψ =>
    intro s; simp [ftoks, List.foldl_append, ihφ, ihψ, dstep]; rfl
  | all φ ih => intro s; simp [ftoks, List.foldl_append, ih, dstep]; rfl
  | exs φ ih => intro s; simp [ftoks, List.foldl_append, ih, dstep]; rfl


/-! ### Packing a token list into one number (base `b` digits) -/

def pack (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: l => d + b * pack b l

lemma pack_lt {b : ℕ} : ∀ l : List ℕ, (∀ d ∈ l, d < b) → pack b l < b ^ l.length
  | [], _ => by simp [pack]
  | d :: l, h => by
    have hd := h d (by simp)
    have ih := pack_lt l (fun x hx => h x (by simp [hx]))
    simp only [pack, List.length_cons, pow_succ]
    nlinarith

lemma pack_digit {b : ℕ} (hb : 0 < b) : ∀ (l : List ℕ), (∀ d ∈ l, d < b) →
    ∀ j (hj : j < l.length), pack b l / b ^ j % b = l[j]
  | [], _, j, hj => by simp at hj
  | d :: l, h, 0, _ => by
    simp [pack, Nat.mod_eq_of_lt (h d (by simp))]
  | d :: l, h, j + 1, hj => by
    have e : pack b (d :: l) / b ^ (j + 1) = pack b l / b ^ j := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      simp only [pack]
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (h d (by simp)), zero_add]
    rw [e]
    simpa using pack_digit hb l (fun x hx => h x (by simp [hx])) j (by simpa using hj)

def unpackToks (m : ℕ) : List ℕ :=
  (List.range m.unpair.2.unpair.1).map fun j => m.unpair.2.unpair.2 / m.unpair.1 ^ j % m.unpair.1

lemma unpackToks_pack {b : ℕ} (hb : 0 < b) (l : List ℕ) (h : ∀ d ∈ l, d < b) :
    unpackToks (Nat.pair b (Nat.pair l.length (pack b l))) = l := by
  apply List.ext_getElem
  · simp [unpackToks]
  · intro j h1 h2
    simp [unpackToks, pack_digit hb l h j h2]

/-! ### Length and size of the token list -/

lemma ttoks_length {k : ℕ} (t : Semiterm ℒₒᵣ Empty k) : (ttoks t).length = tSize t := by
  induction t with
  | bvar i => simp [ttoks, tSize]
  | fvar x => exact x.elim
  | func f v ih =>
    cases f <;> simp [ttoks, tSize, Fin.sum_univ_succ, ih] <;> omega

lemma ftoks_length {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) : (ftoks φ).length = fSize φ := by
  induction φ with
  | verum => simp [ftoks, fSize]
  | falsum => simp [ftoks, fSize]
  | rel r v => cases r <;> simp [ftoks, fSize, Fin.sum_univ_succ, ttoks_length] <;> omega
  | nrel r v => cases r <;> simp [ftoks, fSize, Fin.sum_univ_succ, ttoks_length] <;> omega
  | and φ ψ ihφ ihψ => simp [ftoks, fSize, ihφ, ihψ]; omega
  | or φ ψ ihφ ihψ => simp [ftoks, fSize, ihφ, ihψ]; omega
  | all φ ih => simp [ftoks, fSize, ih]; omega
  | exs φ ih => simp [ftoks, fSize, ih]; omega

lemma ttoks_lt {k : ℕ} (t : Semiterm ℒₒᵣ Empty k) : ∀ x ∈ ttoks t, x < 14 + k := by
  induction t with
  | bvar i => simp [ttoks]
  | fvar x => exact x.elim
  | func f v ih =>
    intro x hx
    cases f <;> simp only [ttoks, List.mem_cons, List.mem_append, List.not_mem_nil] at hx <;>
      rcases hx with rfl | hx | hx <;> first | omega | exact ih _ x hx

lemma ftoks_lt {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) : ∀ x ∈ ftoks φ, x < 14 + k + fSize φ := by
  induction φ with
  | verum => simp [ftoks, fSize]; omega
  | falsum => simp [ftoks, fSize]; omega
  | rel r v =>
    cases r <;> simp only [ftoks, List.mem_cons, List.mem_append] <;>
      rintro x (rfl | hx | hx) <;>
      first | omega | (have := ttoks_lt _ x hx; omega)
  | nrel r v =>
    cases r <;> simp only [ftoks, List.mem_cons, List.mem_append] <;>
      rintro x (rfl | hx | hx) <;>
      first | omega | (have := ttoks_lt _ x hx; omega)
  | and φ ψ ihφ ihψ =>
    simp only [ftoks, fSize, List.mem_cons, List.mem_append]
    rintro x (rfl | hx | hx)
    · omega
    · have := ihφ x hx; omega
    · have := ihψ x hx; omega
  | or φ ψ ihφ ihψ =>
    simp only [ftoks, fSize, List.mem_cons, List.mem_append]
    rintro x (rfl | hx | hx)
    · omega
    · have := ihφ x hx; omega
    · have := ihψ x hx; omega
  | all φ ih =>
    simp only [ftoks, fSize, List.mem_cons]
    rintro x (rfl | hx)
    · omega
    · have := ih x hx; omega
  | exs φ ih =>
    simp only [ftoks, fSize, List.mem_cons]
    rintro x (rfl | hx)
    · omega
    · have := ih x hx; omega

/-! ### The compact code -/

/-- The digit base used for `φ`: larger than every token of `φ`. -/
def cbase {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) : ℕ := 14 + k + fSize φ

/-- The compact code of `φ`: base, length, and the token list as base-`b` digits. -/
def compactCode {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) : ℕ :=
  Nat.pair (cbase φ) (Nat.pair (ftoks φ).length (pack (cbase φ) (ftoks φ)))

/-- The decoder: compact code to `Foundation`'s Gödel number. -/
def compactDecode (m : ℕ) : ℕ := ((unpackToks m).reverse.foldl dstep []).headI

theorem compactDecode_compactCode {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) :
    compactDecode (compactCode φ) = encode φ := by
  have hb : 0 < cbase φ := by unfold cbase; omega
  rw [compactDecode, compactCode, unpackToks_pack hb _ (ftoks_lt φ), ftoks_run]; rfl

/-! ### The decoder is primitive recursive -/

lemma primrec_dstep : Primrec₂ dstep := by
  have hs : Primrec (fun p : List ℕ × ℕ => p.1) := Primrec.fst
  have ht : Primrec (fun p : List ℕ × ℕ => p.2) := Primrec.snd
  have hh : Primrec (fun p : List ℕ × ℕ => p.1.headI) := Primrec.list_headI.comp hs
  have hh2 : Primrec (fun p : List ℕ × ℕ => p.1.tail.headI) :=
    Primrec.list_headI.comp (Primrec.list_tail.comp hs)
  have htl : Primrec (fun p : List ℕ × ℕ => p.1.tail) := Primrec.list_tail.comp hs
  have htl2 : Primrec (fun p : List ℕ × ℕ => p.1.tail.tail) :=
    Primrec.list_tail.comp htl
  have lt : ∀ c : ℕ, PrimrecPred (fun p : List ℕ × ℕ => p.2 < c) := fun c =>
    Primrec.nat_lt.comp ht (Primrec.const c)
  have pr : ∀ {f g : List ℕ × ℕ → ℕ}, Primrec f → Primrec g →
      Primrec (fun p => Nat.pair (f p) (g p) + 1) := fun hf hg =>
    Primrec.nat_add.comp (Primrec₂.natPair.comp hf hg) (Primrec.const 1)
  have pr0 : ∀ {f g : List ℕ × ℕ → ℕ}, Primrec f → Primrec g →
      Primrec (fun p => Nat.pair (f p) (g p)) := fun hf hg => Primrec₂.natPair.comp hf hg
  have hsub : ∀ c : ℕ, Primrec (fun p : List ℕ × ℕ => p.2 - c) := fun c =>
    Primrec.nat_sub.comp ht (Primrec.const c)
  have cons : ∀ {f : List ℕ × ℕ → ℕ} {g : List ℕ × ℕ → List ℕ}, Primrec f → Primrec g →
      Primrec (fun p => f p :: g p) := fun hf hg => Primrec.list_cons.comp hf hg
  have hv2 : Primrec (fun p : List ℕ × ℕ => vec2 p.1.headI p.1.tail.headI) :=
    pr hh (pr hh2 (Primrec.const 0))
  have hkind : Primrec (fun p : List ℕ × ℕ =>
      if p.2 < 4 then 2 else if p.2 < 6 then 0 else 1) :=
    Primrec.ite (lt 4) (Primrec.const 2) (Primrec.ite (lt 6) (Primrec.const 0) (Primrec.const 1))
  have hmod : Primrec (fun p : List ℕ × ℕ => p.2 % 2) := Primrec.nat_mod.comp ht (Primrec.const 2)
  exact Primrec.ite (lt 2)
    (cons (pr (Primrec.const 2) (pr0 (Primrec.const 0) (pr0 ht (Primrec.const 0)))) hs)
    (Primrec.ite (lt 8)
      (cons (pr hkind (pr0 (Primrec.const 2) (pr0 hmod hv2))) htl2)
      (Primrec.ite (lt 10)
        (cons (pr (hsub 6) (Primrec.const 0)) hs)
        (Primrec.ite (lt 12)
          (cons (pr (hsub 6) (pr0 hh hh2)) htl2)
          (Primrec.ite (lt 14)
            (cons (pr (hsub 6) hh) htl)
            (cons (pr (Primrec.const 0) (hsub 14)) hs)))))

lemma primrec_unpackToks : Primrec unpackToks := by
  have hb : Primrec (fun m : ℕ => m.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hl : Primrec (fun m : ℕ => m.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hn : Primrec (fun m : ℕ => m.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  unfold unpackToks
  refine Primrec.list_map (Primrec.list_range.comp hl) ?_
  exact Primrec.nat_mod.comp
    (Primrec.nat_div.comp (hn.comp Primrec.fst) (hpow.comp (hb.comp Primrec.fst) Primrec.snd))
    (hb.comp Primrec.fst)

theorem primrec_compactDecode : Primrec compactDecode := by
  unfold compactDecode
  exact Primrec.list_headI.comp
    (Primrec.list_foldl (Primrec.list_reverse.comp primrec_unpackToks) (Primrec.const [])
      (primrec_dstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

/-! ### Size of the compact code -/

theorem compactCode_lt {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) :
    compactCode φ < (cbase φ + 1) ^ (4 * fSize φ) := by
  have hS : 1 ≤ fSize φ := fSize_pos φ
  have hX : 2 ≤ cbase φ + 1 := by unfold cbase; omega
  have hpack : pack (cbase φ) (ftoks φ) < (cbase φ + 1) ^ fSize φ := by
    have := pack_lt (b := cbase φ) (ftoks φ) (ftoks_lt φ)
    rw [ftoks_length] at this
    exact lt_of_lt_of_le this (Nat.pow_le_pow_left (by omega) _)
  have hlen : (ftoks φ).length < (cbase φ + 1) ^ fSize φ := by
    rw [ftoks_length]
    exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hX _)
  have hinner : Nat.pair (ftoks φ).length (pack (cbase φ) (ftoks φ)) <
      (cbase φ + 1) ^ (2 * fSize φ) := by
    calc _ < (max (ftoks φ).length (pack (cbase φ) (ftoks φ)) + 1) ^ 2 :=
          Nat.pair_lt_max_add_one_sq _ _
      _ ≤ ((cbase φ + 1) ^ fSize φ) ^ 2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  have hb : cbase φ < (cbase φ + 1) ^ (2 * fSize φ) := by
    have : (cbase φ + 1) ^ 1 ≤ (cbase φ + 1) ^ (2 * fSize φ) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simp at this; omega
  unfold compactCode
  calc _ < (max (cbase φ) (Nat.pair (ftoks φ).length (pack (cbase φ) (ftoks φ))) + 1) ^ 2 :=
        Nat.pair_lt_max_add_one_sq _ _
    _ ≤ ((cbase φ + 1) ^ (2 * fSize φ)) ^ 2 := Nat.pow_le_pow_left (by omega) _
    _ = _ := by ring

/-- The compact code of `φ` has `O(|φ| log |φ|)` bits. -/
theorem log2_compactCode_lt {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) :
    Nat.log2 (compactCode φ) < 4 * fSize φ * (Nat.log2 (cbase φ + 1) + 1) := by
  have hS : 1 ≤ fSize φ := fSize_pos φ
  by_cases h0 : compactCode φ = 0
  · rw [h0]; simp [Nat.log2_zero]; positivity
  rw [Nat.log2_lt h0]
  calc compactCode φ < (cbase φ + 1) ^ (4 * fSize φ) := compactCode_lt φ
    _ ≤ (2 ^ (Nat.log2 (cbase φ + 1) + 1)) ^ (4 * fSize φ) :=
        Nat.pow_le_pow_left (Nat.lt_log2_self).le _
    _ = _ := by rw [← pow_mul, mul_comm]

lemma fSize_neg {k : ℕ} (φ : Semiformula ℒₒᵣ Empty k) : fSize (Semiformula.neg φ) = fSize φ := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v => rfl
  | nrel r v => rfl
  | and φ ψ ihφ ihψ => show 1 + fSize (Semiformula.neg φ) + fSize (Semiformula.neg ψ) = _; rw [ihφ, ihψ]; rfl
  | or φ ψ ihφ ihψ => show 1 + fSize (Semiformula.neg φ) + fSize (Semiformula.neg ψ) = _; rw [ihφ, ihψ]; rfl
  | all φ ih => show 1 + fSize (Semiformula.neg φ) = _; rw [ih]; rfl
  | exs φ ih => show 1 + fSize (Semiformula.neg φ) = _; rw [ih]; rfl

/-- The naming template `∀x (φ(x) ↔ x = y)` has size at most `2|φ| + 10`. -/
theorem fSize_nameTemplate_le (φ : ArithmeticSemisentence 1) :
    fSize (nameTemplate φ) ≤ 2 * fSize φ + 10 := by
  have h1 : fSize ((φ/[#0] : Semiformula ℒₒᵣ Empty 2)) ≤ fSize φ := by
    have := fSize_rew_le φ (Rew.subst ![(#0 : Semiterm ℒₒᵣ Empty 2)]) 1 le_rfl
      (by intro i; fin_cases i; simp [tSize])
    simpa using this
  have h2 : fSize (“#0 = #1” : Semiformula ℒₒᵣ Empty 2) = 3 := by
    simp [Semiformula.Operator.eq_def, fSize, tSize, Fin.sum_univ_succ]
  have h3 : fSize (Semiformula.neg (“#0 = #1” : Semiformula ℒₒᵣ Empty 2)) = 3 := by
    rw [fSize_neg, h2]
  simp [nameTemplate, fSize, fSize_neg]
  omega

/-! ### The explicit `n log n` rescaling -/

/-- The explicit rescaling: `4·(2n+10)·(log₂(2n+26)+1)`, which is `O(n log n)`. -/
def nlogBound (n : ℕ) : ℕ := 4 * (2 * n + 10) * (Nat.log2 (2 * n + 26) + 1)

lemma log2_compact_template_lt {n : ℕ} (φ : ArithmeticSemisentence 1) (hφ : fSize φ ≤ n) :
    Nat.log2 (compactCode (nameTemplate φ)) < nlogBound n := by
  have hS := fSize_nameTemplate_le φ
  have h := log2_compactCode_lt (nameTemplate φ)
  have hb : cbase (nameTemplate φ) + 1 ≤ 2 * n + 26 := by unfold cbase; omega
  have hl := log2_mono hb
  unfold nlogBound
  calc _ < _ := h
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

/-- **Theorem 6(b), program-with-input form.** For a consistent, computably
axiomatized `T ⊇ 𝗣𝗔⁻` there is one partial recursive function `g` such that
every number `T` names with a formula of size at most `n` is an output of `g`
on some input of fewer than `nlogBound n = O(n log n)` bits. -/
theorem exists_compact_search (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ∃ g : ℕ →. ℕ, Partrec g ∧ ∀ n k, k ∈ namedValuesIn T n →
      ∃ m, Nat.log2 m < nlogBound n ∧ k ∈ g m := by
  obtain ⟨g, hg, hs⟩ := exists_search T
  refine ⟨fun m => g (compactDecode m), hg.comp primrec_compactDecode.to_comp, ?_⟩
  rintro n k ⟨φ, hφ, hk⟩
  refine ⟨compactCode (nameTemplate φ), log2_compact_template_lt φ hφ, ?_⟩
  simpa [compactDecode_compactCode] using hs φ k hk

/-- **Corollary 7(b): the axioms do not matter, with an explicit `n log n`
rescaling.** For consistent, computably axiomatized `T ⊇ 𝗣𝗔⁻` there is `C`
such that for every consistent `U ⊇ 𝗣𝗔⁻` (not necessarily computably
axiomatized) and every `n`,
`BoolosBigIn T n ≤ BoolosBigIn U (C + 6 · nlogBound n)`. -/
theorem BoolosBigIn_le_any_nlogn (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ∃ C, ∀ (U : ArithmeticTheory) [𝗣𝗔⁻ ⪯ U] [Entailment.Consistent U],
      ∀ n, BoolosBigIn T n ≤ BoolosBigIn U (C + 6 * nlogBound n) := by
  obtain ⟨g, hg, hsearch⟩ := exists_compact_search T
  obtain ⟨C, hC⟩ := BoolosBigIn_partrec_bound hg
  refine ⟨C, fun U _ _ n => ?_⟩
  apply BoolosBigIn_le
  intro k hk
  obtain ⟨m, hm, hkm⟩ := hsearch n k hk
  exact le_trans (hC U m k hkm)
    (BoolosBigIn_mono (show C + 6 * Nat.log2 m ≤ C + 6 * nlogBound n by omega))

lemma log2_mul_32_lt (x : ℕ) (hx : x ≠ 0) : Nat.log2 (32 * x) < Nat.log2 x + 6 := by
  rw [Nat.log2_lt (by omega)]
  have h := @Nat.lt_log2_self x
  have e : 2 ^ (Nat.log2 x + 6) = 32 * 2 ^ (Nat.log2 x + 1) := by
    rw [show Nat.log2 x + 6 = (Nat.log2 x + 1) + 5 by omega, pow_add]; ring
  omega

lemma nlogBound_le (n : ℕ) : nlogBound n ≤ 40 * (n + 1) * (Nat.log2 (n + 1) + 6) := by
  unfold nlogBound
  have h1 : Nat.log2 (2 * n + 26) ≤ Nat.log2 (32 * (n + 1)) := log2_mono (by omega)
  have h2 := log2_mul_32_lt (n + 1) (by omega)
  calc 4 * (2 * n + 10) * (Nat.log2 (2 * n + 26) + 1)
      ≤ 4 * (10 * (n + 1)) * (Nat.log2 (n + 1) + 6) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ = 40 * (n + 1) * (Nat.log2 (n + 1) + 6) := by ring

/-- Corollary 7(b) with round constants:
`BoolosBigIn T n ≤ BoolosBigIn U (C + 240·(n+1)·(log₂(n+1) + 6))`. -/
theorem BoolosBigIn_le_any_nlogn' (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    ∃ C, ∀ (U : ArithmeticTheory) [𝗣𝗔⁻ ⪯ U] [Entailment.Consistent U],
      ∀ n, BoolosBigIn T n ≤ BoolosBigIn U (C + 240 * (n + 1) * (Nat.log2 (n + 1) + 6)) := by
  obtain ⟨C, hC⟩ := BoolosBigIn_le_any_nlogn T
  refine ⟨C, fun U _ _ n => le_trans (hC U n) (BoolosBigIn_mono ?_)⟩
  have h6 : 6 * nlogBound n ≤ 240 * (n + 1) * (Nat.log2 (n + 1) + 6) :=
    calc 6 * nlogBound n ≤ 6 * (40 * (n + 1) * (Nat.log2 (n + 1) + 6)) :=
          Nat.mul_le_mul_left _ (nlogBound_le n)
      _ = _ := by ring
  omega

/-- For `T = 𝗣𝗔`. -/
theorem BoolosBig_PA_le_any_nlogn :
    ∃ C, ∀ (U : ArithmeticTheory) [𝗣𝗔⁻ ⪯ U] [Entailment.Consistent U],
      ∀ n, BoolosBig_PA n ≤ BoolosBigIn U (C + 240 * (n + 1) * (Nat.log2 (n + 1) + 6)) := by
  obtain ⟨C, hC⟩ := BoolosBigIn_le_any_nlogn' 𝗣𝗔
  exact ⟨C, fun U _ _ n => by rw [← BoolosBigIn_PA]; exact hC U n⟩

end RayoBoolos

#print axioms RayoBoolos.compactDecode_compactCode
#print axioms RayoBoolos.primrec_compactDecode
#print axioms RayoBoolos.log2_compactCode_lt
#print axioms RayoBoolos.exists_compact_search
#print axioms RayoBoolos.BoolosBigIn_le_any_nlogn
#print axioms RayoBoolos.BoolosBigIn_le_any_nlogn'
#print axioms RayoBoolos.BoolosBig_PA_le_any_nlogn
