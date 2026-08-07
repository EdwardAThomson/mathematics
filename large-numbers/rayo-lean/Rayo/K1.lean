/-
`Rayo.K1` — the k = 1 naming-cost item.

We name the von-Neumann natural `1 = {∅} = {{}}` with a first-order formula
over `∈` (and `=`), count its symbols under the frozen convention
(`notes/convention-notes.md`), and prove mechanically that it has a unique
solution equal to `1`.

## The formula (convention form, `x = v₀`)

    φ₁(x)  :=  ( (∃ y (y ∈ x))  ∧  (∀ z (∀ w (¬ ((z ∈ x) ∧ (w ∈ z))))) )

"x is nonempty, and no member of x has a member" — i.e. x is nonempty and
every member of x is empty. Under extensionality the empty set is unique, so
the members of x are exactly {∅}, hence x = {∅} = 1.

## Symbol count n₁ = 30

Counted under `notes/convention-notes.md` §2/§4 with the same fully-
parenthesized discipline as the §5 illustration for φ₀ (quantifier body wrapped
in one paren pair, `¬` argument wrapped, each `∧`-node wrapped; atoms bare;
`∃`/`∀` are primitive, one symbol each; each variable occurrence is one).

    ( ( ∃ y ( y ∈ x ) ) ∧ ( ∀ z ( ∀ w ( ¬ ( ( z ∈ x ) ∧ ( w ∈ z ) ) ) ) ) )

    A = ∃ y ( y ∈ x )                                = 7
    C = ( z ∈ x ∧ w ∈ z )                            = 9
    ¬(C)                                             = 12
    ∀ w ( ¬(C) )                                     = 16
    B = ∀ z ( ∀ w ( ¬(C) ) )                          = 20
    φ₁ = ( A ∧ B )                                   = 1+7+1+20+1 = 30

`∃ y (y ∈ x)` uses the primitive `∃` (convention §2). In the `Formula` datatype
`∃` is not a constructor, so it is represented by the standard expansion
`¬ ∀ y ¬ (y ∈ x)`; this is a representation choice for the mechanization only
and does not change the convention symbol count (which is taken on the
`∃`-primitive alphabet).

## Extensionality

The HF model of `Rayo.Satisfaction` is non-extensional (a set is a *list* of
elements), so `{∅}` and `{∅, ∅}` are distinct terms though the same set. No
first-order formula over `∈`/`=` can separate them, so uniqueness holds only
*up to extensional equality*. We state that precisely: any solution has exactly
the same members as `1` (`SameMembers`). Because every member is forced to be
the (structurally unique) empty set, `SameMembers` here is genuine extensional
equality, discharging the extensionality obligation the k=0 spike deferred.

The proof has no proof holes.
-/

import Rayo.K0

namespace Rayo

/-- The von-Neumann `1 = {∅}`, as an HF term. -/
def one : HF := HF.mk [HF.empty]

/-- The k = 1 naming formula.
`φ₁(v₀) ≔ (∃ v₁ (v₁ ∈ v₀)) ∧ (∀ v₂ ∀ v₃ ¬((v₂ ∈ v₀) ∧ (v₃ ∈ v₂)))`,
with `∃` expanded as `¬∀¬` for the datatype. -/
def phi1 : Formula :=
  .conj
    (.neg (.all 1 (.neg (.mem 1 0))))
    (.all 2 (.all 3 (.neg (.conj (.mem 2 0) (.mem 3 2)))))

/-- Two HF sets have the same members: extensional equality at the top level. -/
def SameMembers (a b : HF) : Prop := ∀ z, z ∈ a.elems ↔ z ∈ b.elems

/-- Assignment-lookup rewrites for the variables of `φ₁`. -/
private theorem upd_1_0 (e : Env) (v : HF) : Env.update e 1 v 0 = e 0 :=
  Env.update_other e 1 0 v (by decide)

private theorem upd_23_2 (e : Env) (z w : HF) :
    Env.update (Env.update e 2 z) 3 w 2 = z := by
  rw [Env.update_other _ 3 2 w (by decide), Env.update_same]

private theorem upd_23_0 (e : Env) (z w : HF) :
    Env.update (Env.update e 2 z) 3 w 0 = e 0 := by
  rw [Env.update_other _ 3 0 w (by decide), Env.update_other _ 2 0 z (by decide)]

private theorem upd_23_3 (e : Env) (z w : HF) :
    Env.update (Env.update e 2 z) 3 w 3 = w :=
  Env.update_same _ 3 w

/-- The `∃`-conjunct of `φ₁` says exactly that `v₀` is nonempty. -/
theorem satA_iff (e : Env) :
    Sat e (.neg (.all 1 (.neg (.mem 1 0)))) ↔ (e 0).elems ≠ [] := by
  have h : Sat e (.neg (.all 1 (.neg (.mem 1 0))))
      ↔ ¬ ∀ v : HF, ¬ (v ∈ (e 0).elems) := by
    simp only [Sat, HF.Mem, Env.update_same, upd_1_0]
  rw [h]
  constructor
  · intro hne hnil
    exact hne (fun v hv => by rw [hnil] at hv; simp at hv)
  · intro hne hall
    cases hx : (e 0).elems with
    | nil => exact hne hx
    | cons b rest => exact hall b (by rw [hx]; simp)

/-- The `∀`-conjunct of `φ₁` says exactly that every member of `v₀` is empty. -/
theorem satB_iff (e : Env) :
    Sat e (.all 2 (.all 3 (.neg (.conj (.mem 2 0) (.mem 3 2)))))
      ↔ ∀ z, z ∈ (e 0).elems → z = HF.empty := by
  simp only [Sat, HF.Mem, upd_23_2, upd_23_0, upd_23_3]
  constructor
  · intro hB z hz
    rw [← no_mem_iff_empty z]
    intro w hw
    exact hB z w ⟨hz, hw⟩
  · intro hE z w hzw
    have hz : z = HF.empty := hE z hzw.1
    have hw := hzw.2
    rw [hz] at hw
    simp [HF.empty, HF.elems] at hw

/-- `φ₁` holds of `v₀` exactly when `v₀` is nonempty and all its members are empty. -/
theorem phi1_iff (e : Env) :
    Sat e phi1 ↔ ((e 0).elems ≠ [] ∧ ∀ z, z ∈ (e 0).elems → z = HF.empty) := by
  have hsplit : Sat e phi1
      ↔ Sat e (.neg (.all 1 (.neg (.mem 1 0))))
        ∧ Sat e (.all 2 (.all 3 (.neg (.conj (.mem 2 0) (.mem 3 2))))) := Iff.rfl
  rw [hsplit, satA_iff, satB_iff]

/-- Existence: the canonical `1 = {∅}` satisfies `φ₁`. -/
theorem phi1_holds_of_one : Sat (fun _ => one) phi1 := by
  rw [phi1_iff]
  refine ⟨?_, ?_⟩
  · simp [one, HF.elems]
  · intro z hz
    simp only [one, HF.elems, List.mem_singleton] at hz
    exact hz

/-- Uniqueness (naming): any solution has exactly the same members as `1`,
i.e. is extensionally equal to `1 = {∅}`. -/
theorem phi1_names_one (e : Env) (h : Sat e phi1) : SameMembers (e 0) one := by
  rw [phi1_iff] at h
  obtain ⟨hne, hemp⟩ := h
  intro z
  constructor
  · intro hz
    have hze : z = HF.empty := hemp z hz
    simp [one, HF.elems, hze]
  · intro hz
    simp only [one, HF.elems, List.mem_singleton] at hz
    subst hz
    cases hx : (e 0).elems with
    | nil => exact absurd hx hne
    | cons b rest =>
      have hbe : b = HF.empty := hemp b (by rw [hx]; simp)
      rw [← hbe]; simp

/-- Any two solutions of `φ₁` are extensionally equal (same members). -/
theorem phi1_unique (e e' : Env) (h : Sat e phi1) (h' : Sat e' phi1) :
    SameMembers (e 0) (e' 0) := by
  intro z
  rw [phi1_names_one e h z, phi1_names_one e' h' z]

end Rayo
