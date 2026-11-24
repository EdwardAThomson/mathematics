/-
`Rayo.NoTop` — the "no rulebook is final" argument of `THE-LADDER.md` §3,
machine-checked in the abstract setting. Lean 4 core only, no Mathlib,
matching the rest of this self-contained `rayo-lean` project.

A *naming scheme* is a type of formulas with a size and a functional
"names" relation. `IsBN R n m` says `m` is the record of `R` at budget `n`:
the largest number named by a formula of size `≤ n` (or `0` if none is).

* **Existence and uniqueness of the record** (`exists_isBN_of_finite`,
  `IsBN.unique`): whenever the formulas of size `≤ n` fit in a finite list.
* **Claim A** (`size_gt_of_names_succ_record`, `no_short_self_record`): a
  formula of `R` that names "one more than `R`'s record at budget `n`" must
  itself be larger than `n`. In particular no family of formulas of size
  `≤ c + 6·log₂(n+2)` can do it for every `n`. This is Berry's paradox as a
  theorem; it uses nothing about what the formulas are.
* **Claim B** (`Extends.record_le`, `record_lt_of_names_succ_record`): if a
  scheme `S` extends `R` and contains formulas `β n` naming one more than
  `R`'s record, then `S`'s record at budget `size (β n)` strictly exceeds
  `R`'s record at budget `n`.
* **Non-vacuity** (`unary`, `unaryPlus`, `unaryPlus_beats_unary`): a toy
  pair of schemes satisfying every hypothesis of Claim B, with `β n` of
  size `log₂ n + 1`, so the hypotheses are jointly satisfiable and the
  logarithmic budget is attained.

What is *not* here: any particular rung of the ladder. That a given
extension (a truth predicate, a halting oracle) really supplies the family
`β` at logarithmic size is a fact about that language and is argued on paper
in `THE-LADDER.md` and `BOOLOS-IS-BUSY-BEAVER-CLASS.md`.
-/

namespace Rayo

/-- A naming scheme: formulas, a size, and a "names" relation under which a
formula names at most one number. -/
structure Scheme where
  Form : Type
  size : Form → Nat
  names : Form → Nat → Prop
  names_unique : ∀ φ k₁ k₂, names φ k₁ → names φ k₂ → k₁ = k₂

namespace Scheme

/-- `m` bounds every number named within budget `n`. -/
def Bounds (R : Scheme) (n m : Nat) : Prop :=
  ∀ φ k, R.size φ ≤ n → R.names φ k → k ≤ m

/-- `m` is the record of `R` at budget `n`: an upper bound on everything
named by a formula of size `≤ n`, which is itself so named, or is `0`. -/
def IsBN (R : Scheme) (n m : Nat) : Prop :=
  R.Bounds n m ∧ (m = 0 ∨ ∃ φ, R.size φ ≤ n ∧ R.names φ m)

/-- The record at a given budget is unique. -/
theorem IsBN.unique {R : Scheme} {n m₁ m₂ : Nat}
    (h₁ : R.IsBN n m₁) (h₂ : R.IsBN n m₂) : m₁ = m₂ := by
  have key : ∀ {a b : Nat}, R.IsBN n a → R.IsBN n b → a ≤ b := by
    intro a b ha hb
    rcases ha.2 with h0 | ⟨φ, hsz, hn⟩
    · omega
    · exact hb.1 φ a hsz hn
  have := key h₁ h₂
  have := key h₂ h₁
  omega

/-- The record is non-decreasing in the budget. -/
theorem IsBN.mono {R : Scheme} {n n' m m' : Nat}
    (h : R.IsBN n m) (h' : R.IsBN n' m') (hn : n ≤ n') : m ≤ m' := by
  rcases h.2 with h0 | ⟨φ, hsz, hnm⟩
  · omega
  · exact h'.1 φ m (Nat.le_trans hsz hn) hnm

private theorem exists_record_on_list (R : Scheme) (n : Nat) (l : List R.Form) :
    ∃ m, (∀ φ ∈ l, ∀ k, R.size φ ≤ n → R.names φ k → k ≤ m) ∧
      (m = 0 ∨ ∃ φ, R.size φ ≤ n ∧ R.names φ m) := by
  induction l with
  | nil => exact ⟨0, (fun φ hφ => by cases hφ), Or.inl rfl⟩
  | cons a l ih =>
    obtain ⟨m, hb, hw⟩ := ih
    by_cases ha : R.size a ≤ n ∧ ∃ k, R.names a k
    · obtain ⟨hsz, k, hk⟩ := ha
      by_cases hkm : k ≤ m
      · refine ⟨m, ?_, hw⟩
        intro φ hφ k' hs hn
        rcases List.mem_cons.mp hφ with rfl | hφ'
        · have := R.names_unique _ _ _ hn hk
          omega
        · exact hb φ hφ' k' hs hn
      · refine ⟨k, ?_, Or.inr ⟨a, hsz, hk⟩⟩
        intro φ hφ k' hs hn
        rcases List.mem_cons.mp hφ with rfl | hφ'
        · have := R.names_unique _ _ _ hn hk
          omega
        · have := hb φ hφ' k' hs hn
          omega
    · refine ⟨m, ?_, hw⟩
      intro φ hφ k' hs hn
      rcases List.mem_cons.mp hφ with rfl | hφ'
      · exact absurd ⟨hs, k', hn⟩ ha
      · exact hb φ hφ' k' hs hn

/-- **The record exists** whenever the formulas of size `≤ n` all lie in
some finite list. -/
theorem exists_isBN_of_finite (R : Scheme) (n : Nat) (upTo : List R.Form)
    (hfin : ∀ φ, R.size φ ≤ n → φ ∈ upTo) : ∃ m, R.IsBN n m := by
  obtain ⟨m, hb, hw⟩ := exists_record_on_list R n upTo
  exact ⟨m, fun φ k hs hn => hb φ (hfin φ hs) k hs hn, hw⟩

/-! ### Claim A: a scheme cannot name its own record cheaply -/

/-- **Claim A.** A formula of `R` naming one more than `R`'s record at
budget `n` has size greater than `n`. -/
theorem size_gt_of_names_succ_record {R : Scheme} {n m : Nat} {β : R.Form}
    (hm : R.IsBN n m) (hβ : R.names β (m + 1)) : n < R.size β := by
  apply Nat.lt_of_not_le
  intro hle
  have := hm.1 β (m + 1) hle hβ
  omega

/-- Arithmetic: a budget of `c + 6·log₂(n+2)` is eventually within `n`. -/
theorem exists_log_budget_le (c : Nat) : ∃ n, c + 6 * Nat.log2 (n + 2) ≤ n := by
  refine ⟨2 ^ (c + 8) - 2, ?_⟩
  have hc : c < 2 ^ c := Nat.lt_two_pow_self
  have hpow : 2 ^ (c + 8) = 2 ^ c * 256 := by rw [Nat.pow_add]
  have hbig : 2 ≤ 2 ^ (c + 8) := by omega
  have hadd : 2 ^ (c + 8) - 2 + 2 = 2 ^ (c + 8) := by omega
  rw [hadd, Nat.log2_two_pow]
  omega

/-- **Claim A, logarithmic form.** No family of `R`-formulas of size
`≤ c + 6·log₂(n+2)` names one more than `R`'s record at every budget `n`
(assuming the records exist). -/
theorem no_short_self_record (R : Scheme) (hex : ∀ n, ∃ m, R.IsBN n m)
    (c : Nat) (β : Nat → R.Form)
    (hsize : ∀ n, R.size (β n) ≤ c + 6 * Nat.log2 (n + 2)) :
    ¬ ∀ n m, R.IsBN n m → R.names (β n) (m + 1) := by
  intro hβ
  obtain ⟨n, hn⟩ := exists_log_budget_le c
  obtain ⟨m, hm⟩ := hex n
  have hgt := size_gt_of_names_succ_record hm (hβ n m hm)
  have := hsize n
  omega

/-! ### Claim B: the next scheme can -/

/-- `S` extends `R`: every `R`-formula has a counterpart in `S`, no larger,
naming the same number. -/
structure Extends (R S : Scheme) where
  emb : R.Form → S.Form
  size_le : ∀ φ, S.size (emb φ) ≤ R.size φ
  names_emb : ∀ φ k, R.names φ k → S.names (emb φ) k

/-- An extension never has a smaller record. -/
theorem Extends.record_le {R S : Scheme} (e : Extends R S) {n m m' : Nat}
    (hR : R.IsBN n m) (hS : S.IsBN n m') : m ≤ m' := by
  rcases hR.2 with h0 | ⟨φ, hsz, hn⟩
  · omega
  · exact hS.1 (e.emb φ) m (Nat.le_trans (e.size_le φ) hsz) (e.names_emb φ m hn)

/-- **Claim B.** If `S` contains a formula `β` naming one more than `R`'s
record at budget `n`, then `S`'s record at budget `size β` strictly exceeds
`R`'s record at budget `n`. (The hypothesis `_hR` is not used by the proof:
it is kept so the statement reads as it does on paper. All that matters is
that `β` names `m + 1`.) -/
theorem record_lt_of_names_succ_record {R S : Scheme} {n m m' : Nat} {β : S.Form}
    (_hR : R.IsBN n m) (hβ : S.names β (m + 1)) (hS : S.IsBN (S.size β) m') :
    m < m' := by
  have := hS.1 β (m + 1) (Nat.le_refl _) hβ
  omega

/-- **Claim B, logarithmic form.** If `S` has formulas `β n` of size
`≤ c + 6·log₂(n+2)` naming one more than `R`'s record at budget `n`, then
`S`'s record at budget `c + 6·log₂(n+2)` strictly exceeds `R`'s at `n`. -/
theorem record_lt_at_log_budget {R S : Scheme} (c : Nat) (β : Nat → S.Form)
    (hsize : ∀ n, S.size (β n) ≤ c + 6 * Nat.log2 (n + 2))
    (hβ : ∀ n m, R.IsBN n m → S.names (β n) (m + 1))
    {n m m' : Nat} (hR : R.IsBN n m) (hS : S.IsBN (c + 6 * Nat.log2 (n + 2)) m') :
    m < m' := by
  have := hS.1 (β n) (m + 1) (hsize n) (hβ n m hR)
  omega

end Scheme

/-! ### Non-vacuity: a toy pair of schemes satisfying Claim B's hypotheses -/

/-- Unary numerals: the formula `a` has size `a` and names `a`. -/
def unary : Scheme where
  Form := Nat
  size := id
  names := fun a k => k = a
  names_unique := by intro φ k₁ k₂ h₁ h₂; omega

/-- The record of `unary` at budget `n` is `n`. -/
theorem unary_isBN (n : Nat) : unary.IsBN n n := by
  refine ⟨?_, Or.inr ⟨n, Nat.le_refl n, rfl⟩⟩
  intro φ k hs hn
  have h1 : @LE.le Nat _ φ n := hs
  have h2 : @Eq Nat k φ := hn
  exact Nat.le_trans (Nat.le_of_eq h2) h1

/-- `unary` plus a second kind of formula: `inr a`, of size `log₂ a + 1`,
naming `a + 1`. Since the record of `unary` at budget `a` is `a`, `inr a`
plays the role of "one more than the old record at budget `a`". -/
def unaryPlus : Scheme where
  Form := Sum Nat Nat
  size := fun φ => match φ with
    | .inl a => a
    | .inr a => Nat.log2 a + 1
  names := fun φ k => match φ with
    | .inl a => k = a
    | .inr a => k = a + 1
  names_unique := by
    intro φ k₁ k₂ h₁ h₂
    cases φ <;> simp only at h₁ h₂ <;> omega

/-- `unaryPlus` extends `unary`. -/
def unaryPlusExtends : Scheme.Extends unary unaryPlus where
  emb := Sum.inl
  size_le := fun _ => Nat.le_refl _
  names_emb := fun _ _ h => h

/-- The toy instance of Claim B: at budget `log₂ n + 1` the extended scheme
already beats the record `n` that `unary` needs budget `n` to reach. -/
theorem unaryPlus_beats_unary {n m' : Nat}
    (hS : unaryPlus.IsBN (Nat.log2 n + 1) m') : n < m' :=
  Scheme.record_lt_of_names_succ_record (R := unary) (S := unaryPlus)
    (β := Sum.inr n) (unary_isBN n) rfl hS

end Rayo

#print axioms Rayo.Scheme.IsBN.unique
#print axioms Rayo.Scheme.IsBN.mono
#print axioms Rayo.Scheme.exists_isBN_of_finite
#print axioms Rayo.Scheme.size_gt_of_names_succ_record
#print axioms Rayo.Scheme.no_short_self_record
#print axioms Rayo.Scheme.Extends.record_le
#print axioms Rayo.Scheme.record_lt_of_names_succ_record
#print axioms Rayo.Scheme.record_lt_at_log_budget
#print axioms Rayo.unaryPlus_beats_unary
