/-
`Rayo.K2` — the k = 2 naming-cost item.

We name the von-Neumann natural `2 = {0, 1} = {∅, {∅}}` with a first-order
formula over `∈` (and `=`), count its symbols under the frozen convention
(`notes/convention-notes.md`), and prove mechanically that its solutions are,
up to extensional equality, exactly `2`.

## The formula (convention form, `x = v₀`)

φ₂ is built *recursively* from φ₀ ("is 0", `zF`) and φ₁ ("is 1", `oneF`):

    φ₂(x) := (∃ a ((a ∈ x) ∧ φ₀(a)))          -- x has a member that is 0
           ∧ (∃ b ((b ∈ x) ∧ φ₁(b)))          -- x has a member that is 1
           ∧ (∀ c ¬((c ∈ x) ∧ (¬φ₀(c) ∧ ¬φ₁(c))))   -- every member of x is 0 or 1

with, as sub-predicates on a variable `t`,

    φ₀(t) := ∀ u ¬(u ∈ t)                                            -- "t is empty"
    φ₁(t) := (∃ u (u ∈ t)) ∧ (∀ u ∀ w ¬((u ∈ t) ∧ (w ∈ u)))         -- "t is {∅}"

The "0 or 1" clause is written directly in the primitive alphabet as a De
Morgan negation ("no member is neither 0 nor 1"), so no `or`/`implies`
abbreviation expansion is needed. `∃` is a convention primitive (one symbol);
in the `Formula` datatype it has no constructor and is represented by the
standard `¬∀¬` expansion (a mechanization-only choice that does not change the
convention count, exactly as in `Rayo.K1`).

## Symbol count n₂ = 128

Counted under `notes/convention-notes.md` §2/§4 with the same fully-
parenthesized discipline as φ₀ (10) and φ₁ (30): atom = 3; `¬φ = |φ|+3`;
`(φ ∧ ψ) = |φ|+|ψ|+3`; `Q v (φ) = |φ|+4` (`∃`/`∀` primitive, one symbol each;
each variable occurrence one).

    φ₀(t)                                            = 10   (as in K0)
    φ₁(t)                                            = 30   (as in K1)
    E0 = ∃a ((a∈x) ∧ φ₀(a))       body 3+10+3=16     = 20
    E1 = ∃b ((b∈x) ∧ φ₁(b))       body 3+30+3=36     = 40
    U  = ∀c ¬((c∈x) ∧ (¬φ₀(c) ∧ ¬φ₁(c)))
         ¬φ₀=13, ¬φ₁=33, (¬φ₀∧¬φ₁)=49, (c∈x ∧ ·)=55, ¬·=58   = 62
    φ₂ = (E0 ∧ (E1 ∧ U))          20 + (40+62+3) + 3 = 128

n₂ = 128. This is the cost of *this* recursive construction; it is an upper
bound on the true minimum, not a claim of minimality (a transitivity-based
characterisation might be cheaper). Flagged per `METHODOLOGY.md` C1.

## Extensionality (the k=2 subtlety)

The HF model of `Rayo.Satisfaction` is non-extensional (a set is a *list*).
For k=1 every member of a solution was forced to be *structurally* the empty
set, so `SameMembers` was genuine. For k=2 a solution may contain a member that
is `{∅, ∅}` — extensionally `1` but not structurally `Rayo.one`. So strict
structural `SameMembers` with `two = {∅, one}` is *false*, and uniqueness holds
only *up to extensional equality*. We state it precisely with `ClassEq` (same
0/1 extensional class): `phi2_unique` shows any two solutions have exactly the
same members up to `ClassEq`, and `not_isZero_and_isOne` shows the two classes
are disjoint, so a solution is extensionally `{0, 1} = 2` and nothing else.

The proofs have no proof holes.
-/

import Rayo.K1

namespace Rayo

/-- von-Neumann `2 = {0, 1} = {∅, {∅}}`, as an HF term. -/
def two : HF := HF.mk [HF.empty, one]

/-- Extensional predicate "is `0`" (the empty set). -/
def IsZero (a : HF) : Prop := a = HF.empty

/-- Extensional predicate "is (extensionally) `1 = {∅}`": nonempty, every
member empty. This is exactly `Rayo.K1`'s characterisation of `φ₁`. -/
def IsOne (a : HF) : Prop := a.elems ≠ [] ∧ ∀ w, w ∈ a.elems → w = HF.empty

/-- The 0-class and the 1-class are disjoint: nothing is both. -/
theorem not_isZero_and_isOne (a : HF) : ¬ (IsZero a ∧ IsOne a) := by
  rintro ⟨h0, h1, _⟩
  rw [h0] at h1
  exact h1 rfl

/-! ### The "is 0" sub-formula `φ₀(t)` on an arbitrary variable `t`. -/

/-- `zF t inner := ∀ v_inner ¬(v_inner ∈ v_t)` — "`v_t` is empty". -/
def zF (t inner : Nat) : Formula := .all inner (.neg (.mem inner t))

theorem zF_iff (e : Env) (t inner : Nat) (h : t ≠ inner) :
    Sat e (zF t inner) ↔ IsZero (e t) := by
  have hlk : ∀ w : HF, Env.update e inner w t = e t := fun w =>
    Env.update_other e inner t w h
  have hshape : Sat e (zF t inner) ↔ ∀ w : HF, ¬ (w ∈ (e t).elems) := by
    simp only [zF, Sat, HF.Mem, Env.update_same, hlk]
  rw [hshape, IsZero]
  exact no_mem_iff_empty (e t)

/-! ### The "is 1" sub-formula `φ₁(t)` on an arbitrary variable `t`. -/

/-- `oneF t u v := (∃ v_u (v_u ∈ v_t)) ∧ (∀ v_u ∀ v_v ¬((v_u ∈ v_t) ∧ (v_v ∈ v_u)))`,
"`v_t` is nonempty and all its members are empty", with `∃` as `¬∀¬`. -/
def oneF (t u v : Nat) : Formula :=
  .conj
    (.neg (.all u (.neg (.mem u t))))
    (.all u (.all v (.neg (.conj (.mem u t) (.mem v u)))))

theorem oneF_iff (e : Env) (t u v : Nat)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v) :
    Sat e (oneF t u v) ↔ IsOne (e t) := by
  have hA : Sat e (.neg (.all u (.neg (.mem u t)))) ↔ (e t).elems ≠ [] := by
    have hlk : ∀ w : HF, Env.update e u w t = e t := fun w =>
      Env.update_other e u t w htu
    have h : Sat e (.neg (.all u (.neg (.mem u t))))
        ↔ ¬ ∀ w : HF, ¬ (w ∈ (e t).elems) := by
      simp only [Sat, HF.Mem, Env.update_same, hlk]
    rw [h]
    constructor
    · intro hne hnil
      exact hne (fun w hw => by rw [hnil] at hw; simp at hw)
    · intro hne hall
      cases hx : (e t).elems with
      | nil => exact hne hx
      | cons b rest => exact hall b (by rw [hx]; simp)
  have hB : Sat e (.all u (.all v (.neg (.conj (.mem u t) (.mem v u)))))
      ↔ ∀ z, z ∈ (e t).elems → z = HF.empty := by
    have hlk_t : ∀ (z w : HF), Env.update (Env.update e u z) v w t = e t := by
      intro z w
      rw [Env.update_other _ v t w htv, Env.update_other _ u t z htu]
    have hlk_u : ∀ (z w : HF), Env.update (Env.update e u z) v w u = z := by
      intro z w
      rw [Env.update_other _ v u w huv, Env.update_same]
    have hlk_v : ∀ (z w : HF), Env.update (Env.update e u z) v w v = w := by
      intro z w
      exact Env.update_same _ v w
    simp only [Sat, HF.Mem, hlk_t, hlk_u, hlk_v]
    constructor
    · intro hbb z hz
      rw [← no_mem_iff_empty z]
      intro w hw
      exact hbb z w ⟨hz, hw⟩
    · intro hE z w hzw
      have hz : z = HF.empty := hE z hzw.1
      have hw := hzw.2
      rw [hz] at hw
      simp [HF.empty, HF.elems] at hw
  have hsplit : Sat e (oneF t u v)
      ↔ Sat e (.neg (.all u (.neg (.mem u t))))
        ∧ Sat e (.all u (.all v (.neg (.conj (.mem u t) (.mem v u))))) := Iff.rfl
  rw [hsplit, hA, hB, IsOne]

/-! ### The k = 2 formula and its characterisation. -/

/-- The k = 2 naming formula (see the file header for the convention form).
`x = v₀`; witnesses `a = v₁`, `b = v₂`, member-quantifier `c = v₃`; each
sub-predicate uses its own fresh bound variables (`4`; `5,6`; `7`; `8,9`). -/
def phi2 : Formula :=
  .conj
    (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 4)))))
    (.conj
      (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 5 6)))))
      (.all 3 (.neg (.conj (.mem 3 0)
        (.conj (.neg (zF 3 7)) (.neg (oneF 3 8 9)))))))

/-- The `∃`-0 conjunct says `x` has a member that is 0. -/
theorem satE0_iff (e : Env) :
    Sat e (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 4)))))
      ↔ ∃ a, a ∈ (e 0).elems ∧ IsZero a := by
  have hbody : ∀ a : HF, Sat (Env.update e 1 a) (.conj (.mem 1 0) (zF 1 4))
      ↔ (a ∈ (e 0).elems ∧ IsZero a) := by
    intro a
    have h1 : (Env.update e 1 a) 1 = a := Env.update_same e 1 a
    have h0 : (Env.update e 1 a) 0 = e 0 := Env.update_other e 1 0 a (by decide)
    have hz : Sat (Env.update e 1 a) (zF 1 4) ↔ IsZero a := by
      have hz0 := zF_iff (Env.update e 1 a) 1 4 (by decide)
      rw [h1] at hz0
      exact hz0
    show ((Env.update e 1 a) 1 ∈ ((Env.update e 1 a) 0).elems)
          ∧ Sat (Env.update e 1 a) (zF 1 4) ↔ (a ∈ (e 0).elems ∧ IsZero a)
    simp only [h1, h0, hz]
  rw [show Sat e (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 4)))))
        ↔ ¬ ∀ a : HF, ¬ Sat (Env.update e 1 a) (.conj (.mem 1 0) (zF 1 4)) from Iff.rfl]
  constructor
  · intro h
    rcases Classical.em (∃ a, a ∈ (e 0).elems ∧ IsZero a) with hex | hex
    · exact hex
    · exact absurd (fun a hp => hex ⟨a, (hbody a).mp hp⟩) h
  · rintro ⟨a, ha⟩ h
    exact h a ((hbody a).mpr ha)

/-- The `∃`-1 conjunct says `x` has a member that is 1. -/
theorem satE1_iff (e : Env) :
    Sat e (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 5 6)))))
      ↔ ∃ b, b ∈ (e 0).elems ∧ IsOne b := by
  have hbody : ∀ b : HF, Sat (Env.update e 2 b) (.conj (.mem 2 0) (oneF 2 5 6))
      ↔ (b ∈ (e 0).elems ∧ IsOne b) := by
    intro b
    have h2 : (Env.update e 2 b) 2 = b := Env.update_same e 2 b
    have h0 : (Env.update e 2 b) 0 = e 0 := Env.update_other e 2 0 b (by decide)
    have ho : Sat (Env.update e 2 b) (oneF 2 5 6) ↔ IsOne b := by
      have ho0 := oneF_iff (Env.update e 2 b) 2 5 6 (by decide) (by decide) (by decide)
      rw [h2] at ho0
      exact ho0
    show ((Env.update e 2 b) 2 ∈ ((Env.update e 2 b) 0).elems)
          ∧ Sat (Env.update e 2 b) (oneF 2 5 6) ↔ (b ∈ (e 0).elems ∧ IsOne b)
    simp only [h2, h0, ho]
  rw [show Sat e (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 5 6)))))
        ↔ ¬ ∀ b : HF, ¬ Sat (Env.update e 2 b) (.conj (.mem 2 0) (oneF 2 5 6)) from Iff.rfl]
  constructor
  · intro h
    rcases Classical.em (∃ b, b ∈ (e 0).elems ∧ IsOne b) with hex | hex
    · exact hex
    · exact absurd (fun b hp => hex ⟨b, (hbody b).mp hp⟩) h
  · rintro ⟨b, hb⟩ h
    exact h b ((hbody b).mpr hb)

/-- The `∀` conjunct says every member of `x` is 0 or 1. -/
theorem satU_iff (e : Env) :
    Sat e (.all 3 (.neg (.conj (.mem 3 0)
        (.conj (.neg (zF 3 7)) (.neg (oneF 3 8 9))))))
      ↔ ∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c) := by
  have hbody : ∀ c : HF,
      Sat (Env.update e 3 c) (.neg (.conj (.mem 3 0)
        (.conj (.neg (zF 3 7)) (.neg (oneF 3 8 9)))))
      ↔ (c ∈ (e 0).elems → (IsZero c ∨ IsOne c)) := by
    intro c
    have h3 : (Env.update e 3 c) 3 = c := Env.update_same e 3 c
    have h0 : (Env.update e 3 c) 0 = e 0 := Env.update_other e 3 0 c (by decide)
    have hz : Sat (Env.update e 3 c) (zF 3 7) ↔ IsZero c := by
      have hz0 := zF_iff (Env.update e 3 c) 3 7 (by decide)
      rw [h3] at hz0
      exact hz0
    have ho : Sat (Env.update e 3 c) (oneF 3 8 9) ↔ IsOne c := by
      have ho0 := oneF_iff (Env.update e 3 c) 3 8 9 (by decide) (by decide) (by decide)
      rw [h3] at ho0
      exact ho0
    show ¬ (((Env.update e 3 c) 3 ∈ ((Env.update e 3 c) 0).elems)
          ∧ (¬ Sat (Env.update e 3 c) (zF 3 7) ∧ ¬ Sat (Env.update e 3 c) (oneF 3 8 9)))
        ↔ (c ∈ (e 0).elems → (IsZero c ∨ IsOne c))
    simp only [h3, h0, hz, ho]
    constructor
    · intro hnand hc
      rcases Classical.em (IsZero c) with hz2 | hz2
      · exact Or.inl hz2
      · rcases Classical.em (IsOne c) with ho2 | ho2
        · exact Or.inr ho2
        · exact absurd ⟨hc, hz2, ho2⟩ hnand
    · intro himp hand
      rcases himp hand.1 with h | h
      · exact hand.2.1 h
      · exact hand.2.2 h
  constructor
  · intro h c hc
    exact (hbody c).mp (h c) hc
  · intro h c
    exact (hbody c).mpr (h c)

/-- `φ₂` holds of `x` exactly when `x` has a 0-member, a 1-member, and every
member is 0 or 1 — i.e. `x` is extensionally `{0, 1} = 2`. -/
theorem phi2_iff (e : Env) :
    Sat e phi2 ↔
      ( (∃ a, a ∈ (e 0).elems ∧ IsZero a)
        ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
        ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c)) ) := by
  have hsplit : Sat e phi2 ↔
      Sat e (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 4)))))
      ∧ (Sat e (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 5 6)))))
         ∧ Sat e (.all 3 (.neg (.conj (.mem 3 0)
             (.conj (.neg (zF 3 7)) (.neg (oneF 3 8 9))))))) := Iff.rfl
  rw [hsplit, satE0_iff, satE1_iff, satU_iff]

/-- Existence: the canonical `2 = {∅, {∅}}` satisfies `φ₂`. -/
theorem phi2_holds_of_two : Sat (fun _ => two) phi2 := by
  rw [phi2_iff]
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, ?_, ?_⟩, ?_⟩
  · simp [two, HF.elems]
  · simp [two, HF.elems]
  · simp [one, HF.elems]
  · intro w hw
    simp only [one, HF.elems, List.mem_singleton] at hw
    exact hw
  · intro c hc
    simp only [two, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h
    · exact Or.inl h
    · subst h
      refine Or.inr ⟨?_, ?_⟩
      · simp [one, HF.elems]
      · intro w hw
        simp only [one, HF.elems, List.mem_singleton] at hw
        exact hw

/-- Naming: any solution has exactly the member-classification of `2` — a
0-member, a 1-member, and no other kind of member. -/
theorem phi2_names_two (e : Env) (h : Sat e phi2) :
    (∃ a, a ∈ (e 0).elems ∧ IsZero a)
    ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
    ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c)) :=
  (phi2_iff e).mp h

/-- Two HF members are extensionally equal *within the 0/1 universe* iff they
share a class. On φ₂-solutions (whose members are only 0s and 1s) this is
genuine extensional equality. -/
def ClassEq (z m : HF) : Prop := (IsZero z ∧ IsZero m) ∨ (IsOne z ∧ IsOne m)

/-- Uniqueness up to extensional equality: any two solutions of `φ₂` have
exactly the same members up to `ClassEq`. With `not_isZero_and_isOne` this
pins every solution to the extensional set `{0, 1} = 2`. -/
theorem phi2_unique (e e' : Env) (h : Sat e phi2) (h' : Sat e' phi2) :
    ∀ z, (∃ m, m ∈ (e 0).elems ∧ ClassEq z m)
        ↔ (∃ m, m ∈ (e' 0).elems ∧ ClassEq z m) := by
  obtain ⟨⟨a, ha, haz⟩, ⟨b, hb, hbo⟩, _⟩ := (phi2_iff e).mp h
  obtain ⟨⟨a', ha', haz'⟩, ⟨b', hb', hbo'⟩, _⟩ := (phi2_iff e').mp h'
  intro z
  constructor
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩
    · exact ⟨a', ha', Or.inl ⟨hzz, haz'⟩⟩
    · exact ⟨b', hb', Or.inr ⟨hzo, hbo'⟩⟩
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩
    · exact ⟨a, ha, Or.inl ⟨hzz, haz⟩⟩
    · exact ⟨b, hb, Or.inr ⟨hzo, hbo⟩⟩

end Rayo
