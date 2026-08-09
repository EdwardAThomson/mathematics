/-
`RayoBoolos.RayoBig` — the growth-rate half of the Rayo fork, mechanized in
Lean under the honest RELATIVE scope `RAYO-GROWTH-RATE.md` already uses.

**What this file is.** `RAYO-GROWTH-RATE.md` §6 makes one structural point
sharply: the Boolos fork and the Rayo fork run the *same* naming machine —
direct naming, `O(k)` input cost, pre-inflation to `f(k²)` to absorb the
linear factor — and differ *only* in the strength of the naming predicate
(first-order provability-in-PA for Boolos, truth-in-`V` for Rayo). "Same
machine, different fuel." This file cashes that out formally: it takes the
pre-inflation domination argument already mechanized (gap-free, no proof
holes) for `BoolosBig_PA` (`RayoBoolos.BoolosBig.BoolosBig_PA_dominates`) and re-runs it
against an *abstract* satisfaction interface standing in for truth-in-`V`,
proving the identical domination theorem `rayoBig_dominates`.

**Why the satisfaction predicate is axiomatized, and why that is the honest
ceiling — not a shortcut.** For the Boolos fork the naming predicate is
first-order *provability*, which `Foundation` supplies as an honest
object-language formula (`RayoBoolos.TNames`), so `BoolosBig.lean` builds it
outright with no axiom. For the Rayo fork the naming predicate is
*truth-in-`V`*, and by **Tarski's undefinability theorem that satisfaction
relation is not first-order definable** — it is exactly the MK /
impredicative-truth commitment `RAYO-R0-WELLDEFINEDNESS.md` isolated, and
`RAYO-GROWTH-RATE.md` §4 names it as the very thing that makes Rayo transcend
where Boolos cannot. So there is no honest way to *construct* a Rayo `Sat`
inside first-order Lean the way `TNames` is constructed; the faithful move is
to **assume it as an interface** and prove the growth theorem *relative* to
it. That is precisely the "everything below is conditional on R0's
well-definedness commitment" framing the note opens with, now made into a
Lean hypothesis rather than left in prose.

**What is axiomatized vs. mechanized — the exact split.**
  - *Axiomatized* (the `SatInterface` structure fields, i.e. hypotheses — NOT
    Lean `axiom` declarations and NOT constructed objects): a carrier `Fml` of
    coded one-free-variable FOST formulas with a symbol-count `size`; that
    only finitely many formulas have `size ≤ b` (true of any reasonable
    coding); and the satisfaction predicate `Sat : Fml → ℕ → Prop`, the
    truth-in-`V` readout of a coded formula at the von Neumann numeral of a
    natural. The naming predicate `Names φ k` is then *defined* as the Tarski
    naming biconditional `∀ j, Sat φ j ↔ j = k` (this is `∀x(φ(x) ↔ x = k̄)`,
    the R0/B0 "names" condition verbatim), from which the uniqueness-naming
    readout `Names_unique` is *derived*, not assumed. The definability class's
    closure under `n ↦ n²` pre-inflation with constant size overhead — the
    abstract analogue of `graphSq` — is likewise taken as a hypothesis `sq`
    of the theorem, because constructing it requires the FOST formula algebra
    we are deliberately not rebuilding here.
  - *Mechanized* (gap-free, this file): everything the growth argument does
    *with* that interface. The finite-sup `RayoBig` construction and its
    monotonicity; that a formula names at most one value; and the full
    pre-inflation √-bookkeeping of `BoolosBig_PA_dominates`, transported
    verbatim. No step of the combinatorial argument is assumed.

So `#print axioms rayoBig_dominates` reports only Lean/Mathlib's own
`propext, Classical.choice, Quot.sound` (from `Set.Finite`/`Finset.sup`): the
`Sat` interface contributes *zero* Lean axioms, exactly because it rides in as
structure fields / hypotheses. The mathematical dependence on truth-in-`V`
lives, honestly and visibly, in the `SatInterface` argument the theorem
quantifies over — you cannot invoke `rayoBig_dominates` without producing one.

Extends the project without touching `K*.lean`, `BoolosBig.lean`, or
`TNames.lean`; it `import`s `BoolosBig` only to reuse its already-built
Mathlib finiteness API and to make the "same machine" reuse literal.
-/

module

public import RayoBoolos.BoolosBig

@[expose] public section

/-! ### The abstract satisfaction interface (the axiomatized truth-in-`V` readout) -/

/-- An **abstract FOST satisfaction interface**: the honest Lean stand-in for
truth-in-`V`, packaged as structure fields (hypotheses), never as `axiom`
declarations or constructed objects.

Faithfulness of each field to `RAYO-GROWTH-RATE.md`:
  - `Fml` — the type of (codes of) one-free-variable first-order set-theory
    formulas `φ(x)`. Opaque on purpose: any concrete coding would just be one
    inhabitant of this interface.
  - `size φ` — the symbol/code length of `φ`, the quantity `Rayo(n)` budgets
    over (`|φ| ≤ n` in the note's `Rayo(n) = 1 + sup{ m : |φ| ≤ n names m }`).
  - `size_pos` — every formula costs at least one symbol.
  - `finite` — only finitely many formulas fit in any fixed budget. For real
    FOST this is immediate from the coding (finitely many symbols, bounded
    length); here it is the abstract fact `RayoBig`'s sup needs.
  - `Sat φ k` — **the truth-in-`V` satisfaction readout**: `φ` holds of the
    von Neumann numeral of `k`. This one field is the whole Tarskian
    commitment: constructing it for genuine FOST is exactly the
    non-first-order-definable MK truth predicate of R0 §4, which is why it is
    assumed rather than built (see the module docstring).

The naming predicate and its uniqueness readout are *derived* from `Sat`
below, not added as fields — so nothing about "names at most one value" is
smuggled in as an assumption. -/
structure SatInterface where
  Fml : Type
  size : Fml → ℕ
  size_pos : ∀ φ : Fml, 1 ≤ size φ
  finite : ∀ b : ℕ, {φ : Fml | size φ ≤ b}.Finite
  Sat : Fml → ℕ → Prop

namespace SatInterface

variable (I : SatInterface)

/-- **The naming predicate, as the Tarski naming biconditional.** `Names φ k`
says `φ` satisfies exactly `k`: `∀ j, Sat φ j ↔ j = k`. This is
`∀x(φ(x) ↔ x = k̄)`, the "`φ` names `k`" condition of
`RAYO-R0-WELLDEFINEDNESS.md` / `BOOLOS-B0-WELLDEFINEDNESS.md`, verbatim — the
Tarski clause for the readout, phrased in `Sat`. -/
def Names (φ : I.Fml) (k : ℕ) : Prop := ∀ j : ℕ, I.Sat φ j ↔ j = k

variable {I}

/-- **The uniqueness-naming readout, derived (not assumed).** A formula names
at most one value: if `φ` names both `k1` and `k2` then `k1 = k2`. Immediate
from the naming biconditional — `Sat φ k1` holds (take `j = k1`), and `φ`
naming `k2` turns that into `k1 = k2`. This is `BOOLOS-B0-WELLDEFINEDNESS.md`
Lemma 1 for the Rayo interface, and it is what makes `namedValues` finite. -/
theorem Names_unique {φ : I.Fml} {k1 k2 : ℕ}
    (h1 : I.Names φ k1) (h2 : I.Names φ k2) : k1 = k2 := by
  unfold Names at h1 h2
  have hsat : I.Sat φ k1 := (h1 k1).mpr rfl
  exact (h2 k1).mp hsat

/-! ### `RayoBig`, relative to the interface

Mirrors `BoolosBig.lean`'s `namedValues` / `BoolosBig_PA` architecture exactly,
with `Sat`-naming in place of PA-`TNamesMeta` and the abstract `finite` field
in place of the concrete `formsUpTo_finite`. -/

/-- The values nameable within budget `n`: `RAYO-R0-WELLDEFINEDNESS.md`'s
`{ m : some φ with |φ| ≤ n names m }`. -/
def namedValues (I : SatInterface) (n : ℕ) : Set ℕ :=
  {k | ∃ φ : I.Fml, I.size φ ≤ n ∧ I.Names φ k}

theorem namedValues_finite (I : SatInterface) (n : ℕ) : (I.namedValues n).Finite := by
  have hcover : I.namedValues n ⊆ ⋃ φ ∈ {φ : I.Fml | I.size φ ≤ n}, {k | I.Names φ k} := by
    rintro k ⟨φ, hφ, hk⟩
    exact Set.mem_biUnion hφ hk
  apply Set.Finite.subset _ hcover
  apply Set.Finite.biUnion (I.finite n)
  intro φ _
  rcases Set.eq_empty_or_nonempty {k | I.Names φ k} with he | ⟨k0, hk0⟩
  · rw [he]; exact Set.finite_empty
  · have : {k | I.Names φ k} = {k0} := by
      ext k; constructor
      · intro hk; exact Names_unique hk hk0
      · rintro rfl; exact hk0
    rw [this]; exact Set.finite_singleton _

theorem namedValues_mono {I : SatInterface} {n m : ℕ} (h : n ≤ m) :
    I.namedValues n ⊆ I.namedValues m := by
  rintro k ⟨φ, hφ, hk⟩
  exact ⟨φ, hφ.trans h, hk⟩

end SatInterface

/-- **`RayoBig`, concretely, relative to a satisfaction interface `I`**: the
largest value nameable by a formula of `size ≤ n` (or `0` if none), the
`Rayo(n) = 1 + sup{…}` construction of `RAYO-R0-WELLDEFINEDNESS.md` with the
`+1` dropped (immaterial to growth rate; the sup is what dominates). Built via
`Finset.sup id` over the finite `namedValues`, exactly as `BoolosBig_PA` is —
`Finset.sup ∅ id = 0` handles the empty budget for free, and `Finset.le_sup`
(`namedValues_le_RayoBig`) is the only property the domination argument uses. -/
noncomputable def RayoBig (I : SatInterface) (n : ℕ) : ℕ :=
  (I.namedValues_finite n).toFinset.sup id

theorem namedValues_le_RayoBig {I : SatInterface} {n k : ℕ}
    (hk : k ∈ I.namedValues n) : k ≤ RayoBig I n := by
  apply Finset.le_sup (f := id)
  exact (Set.Finite.mem_toFinset _).mpr hk

/-- `RayoBig` is monotone: a larger budget names at least as much. -/
theorem RayoBig_mono {I : SatInterface} {n m : ℕ} (h : n ≤ m) :
    RayoBig I n ≤ RayoBig I m := by
  apply Finset.sup_mono
  intro k hk
  exact (Set.Finite.mem_toFinset _).mpr
    (SatInterface.namedValues_mono h ((Set.Finite.mem_toFinset _).mp hk))

/-! ### The definability / naming-cost interface for the dominated class -/

/-- **`Definable I f`**: `f : ℕ → ℕ` is nameable in the interface `I` with the
FOST direct-naming cost profile of `RAYO-GROWTH-RATE.md` §2. For each input
`n`, a formula `nameOf n` names `f n`, and its `size` is at most
`cost * (2*n + 1)` — *linear in the input*, matching the note's successor-chain
`O(k)` input cost (and the mechanized `BoolosBig.fSize_graphAt_le`, whose bound
is `fSize graph * (2n+1)`; `cost` plays the role of `fSize graph`, a constant
independent of `n`).

This is the abstract analogue of `RayoBoolos.ProvablyTotal` + the size lemmas.
Whether such a `Definable` witness exists for a given `f` is a fact about FOST
truth-in-`V` naming, not about this file — the file proves what *follows* from
having one, for the whole class at once. -/
structure Definable (I : SatInterface) (f : ℕ → ℕ) where
  nameOf : ℕ → I.Fml
  names : ∀ n : ℕ, I.Names (nameOf n) (f n)
  cost : ℕ
  size_le : ∀ n : ℕ, I.size (nameOf n) ≤ cost * (2 * n + 1)

/-- **The domination theorem for the Rayo fork.** `RayoBig` (relative to any
satisfaction interface `I`) eventually dominates every `f` that is monotone and
`Definable` in `I`, provided the definability class is closed under the `n ↦ n²`
pre-inflation with *constant* size overhead (`sq` — the abstract analogue of
`RayoBoolos.ProvablyTotal.sq`, built there from `graphSq`; here a hypothesis,
since constructing it needs the FOST formula algebra this file abstracts away).

`RAYO-GROWTH-RATE.md` §2 in Lean. The proof is `BoolosBig_PA_dominates`
transported verbatim: naming `f` directly costs `O(n)` (the `size_le` bound is
linear, not constant), so the naive `RayoBig(n + c) ≥ f(n)` fails; instead name
the pre-inflated `F(n) = f(n²)` — whose graph needs no numeral, hence only a
*constant* size overhead over `f`'s — and compose with `n² ≥ m` at `n ≈ √m` to
recover genuine domination. This is exactly the §3 "same machine" claim: the
√-bookkeeping below is character-for-character `BoolosBig`'s; only the naming
predicate underneath (`Sat` vs. PA-provability) has changed. -/
theorem rayoBig_dominates
    (I : SatInterface)
    (sq : ∀ {g : ℕ → ℕ}, Definable I g → Definable I (fun n => g (n * n)))
    (f : ℕ → ℕ) (hf_mono : Monotone f) (D : Definable I f) :
    ∃ N, ∀ m > N, RayoBig I m ≥ f m := by
  -- Pre-inflate: `F(n) = f(n²)` is definable at a constant cost `c`.
  have Dsq : Definable I (fun n => f (n * n)) := sq D
  set c := Dsq.cost + 1 with hc_def
  have hc : 1 ≤ c := by omega
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
  -- `f (n*n)` is named within budget `c * (2n+1)`, hence `≤ RayoBig` there.
  have hmem : f (n * n) ∈ I.namedValues (c * (2 * n + 1)) := by
    refine ⟨Dsq.nameOf n, ?_, ?_⟩
    · calc I.size (Dsq.nameOf n) ≤ Dsq.cost * (2 * n + 1) := Dsq.size_le n
        _ ≤ c * (2 * n + 1) := Nat.mul_le_mul_right _ (by omega)
    · exact Dsq.names n
  have hle : f (n * n) ≤ RayoBig I (c * (2 * n + 1)) := namedValues_le_RayoBig hmem
  show f m ≤ RayoBig I m
  calc f m ≤ f (n * n) := hf_mono hn_sq_ge_m
    _ ≤ RayoBig I (c * (2 * n + 1)) := hle
    _ ≤ RayoBig I m := RayoBig_mono hc_bound

#print axioms RayoBig
#print axioms rayoBig_dominates
