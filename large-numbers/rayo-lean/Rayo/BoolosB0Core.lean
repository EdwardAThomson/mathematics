/-
`Rayo.BoolosB0Core` — the combinatorial core of the Boolos-fork well-definedness
gate, `BOOLOS-B0-WELLDEFINEDNESS.md` §3 (Lemma 1, Lemma 2, and the Combination),
abstracted away from Peano Arithmetic and proof theory so it needs nothing
beyond Lean 4 core — no Mathlib, matching the rest of this self-contained
`rayo-lean` project (`lake-manifest.json` lists no packages).

`BOOLOS-B0-WELLDEFINEDNESS.md` §7, option (3), states this precisely as the
thing to verify: given a finite list `Φ` of candidate formulas (the length-≤n
representatives) and a partial "names" map (Lemma 1: each candidate names at
most one value, since a consistent theory can't prove two different unique
denotations for the same formula), the set of named values is finite and, if
nonempty, has a maximum — which is exactly `BoolosBig_T(n) = sup Ψₙ = max Ψₙ`
in that note's §3. This file proves that abstract fact, generically over any
carrier type `α` for "candidate formula" and any partial map `α → Option Nat`
for "the value this candidate names, if any" — the PA/provability-specific
content (why the map is well-defined, why the candidate list is finite) lives
in the note itself and is not re-derived here; only the combinatorial payoff
is checked.
-/

namespace Rayo

/-- The maximum of a list of naturals, or `none` if the list is empty. -/
def natListMax : List Nat → Option Nat
  | [] => none
  | x :: xs =>
    match natListMax xs with
    | none => some x
    | some m => some (max x m)

@[simp] theorem natListMax_nil : natListMax ([] : List Nat) = none := rfl

theorem natListMax_eq_none_iff (l : List Nat) : natListMax l = none ↔ l = [] := by
  cases l with
  | nil => simp [natListMax]
  | cons x xs =>
    simp only [natListMax]
    cases natListMax xs <;> simp

/-- Every member of a list is `≤` the list's `natListMax`, whenever that is
`some`. -/
theorem le_of_mem_natListMax {l : List Nat} {x m : Nat}
    (hx : x ∈ l) (hm : natListMax l = some m) : x ≤ m := by
  induction l generalizing m with
  | nil => cases hx
  | cons y ys ih =>
    simp only [natListMax] at hm
    rcases List.mem_cons.mp hx with rfl | hx'
    · cases hys : natListMax ys with
      | none => rw [hys] at hm; simp only [Option.some.injEq] at hm; omega
      | some m' => rw [hys] at hm; simp only [Option.some.injEq] at hm; omega
    · cases hys : natListMax ys with
      | none =>
        exfalso
        have hnil : ys = [] := (natListMax_eq_none_iff ys).mp hys
        rw [hnil] at hx'
        simp at hx'
      | some m' =>
        rw [hys] at hm
        simp only [Option.some.injEq] at hm
        have hxm' := ih hx' hys
        omega

/-- `natListMax` of a nonempty list is itself a member of the list. -/
theorem mem_of_natListMax_eq_some {l : List Nat} {m : Nat} (hm : natListMax l = some m) :
    m ∈ l := by
  induction l generalizing m with
  | nil => simp [natListMax] at hm
  | cons y ys ih =>
    simp only [natListMax] at hm
    cases hys : natListMax ys with
    | none =>
      rw [hys] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      simp
    | some m' =>
      rw [hys] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rcases Nat.le_total y m' with h | h
      · rw [Nat.max_eq_right h]
        have hmem : m' ∈ ys := ih hys
        simp [hmem]
      · rw [Nat.max_eq_left h]
        simp

/-- **The B0 core theorem.** For any finite list of candidates `Φ` and any
partial naming map `name`, the set of values named by some candidate in `Φ`
is finite (it is literally a `List`, by construction) and, if any candidate
names anything, there is a value `m` that is itself named by some candidate
and that bounds every named value — i.e. a genuine maximum, not merely an
upper bound. This is `BoolosBig_T(n) = sup Ψₙ = max Ψₙ`
(`BOOLOS-B0-WELLDEFINEDNESS.md` §3, "Combination") with nothing PA-specific
left in it. -/
theorem exists_max_of_finite_naming {α : Type u} (Φ : List α) (name : α → Option Nat) :
    (Φ.filterMap name = []) ∨
      ∃ m, (∃ φ ∈ Φ, name φ = some m) ∧ ∀ φ ∈ Φ, ∀ v, name φ = some v → v ≤ m := by
  cases hcase : natListMax (Φ.filterMap name) with
  | none =>
    left
    exact (natListMax_eq_none_iff (Φ.filterMap name)).mp hcase
  | some m =>
    right
    refine ⟨m, ?_, ?_⟩
    · have hmem : m ∈ Φ.filterMap name := mem_of_natListMax_eq_some hcase
      rw [List.mem_filterMap] at hmem
      obtain ⟨φ, hφ, hname⟩ := hmem
      exact ⟨φ, hφ, hname⟩
    · intro φ hφ v hv
      have hv' : v ∈ Φ.filterMap name := by
        rw [List.mem_filterMap]
        exact ⟨φ, hφ, hv⟩
      exact le_of_mem_natListMax hv' hcase

end Rayo
