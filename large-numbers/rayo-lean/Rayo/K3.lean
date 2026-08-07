/-
`Rayo.K3` — the k = 3 naming-cost item.

We name the von-Neumann natural `3 = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}` with a
first-order formula over `∈` (and `=`), count its symbols under the frozen
convention (`notes/convention-notes.md`), and prove mechanically that its
solutions are, up to extensional equality, exactly `3`.

## The formula (convention form, `x = v₀`)

φ₃ is built *recursively* from φ₀ ("is 0"), φ₁ ("is 1") and φ₂ ("is 2"):

    φ₃(x) := (∃ a ((a ∈ x) ∧ φ₀(a)))                         -- x has a 0-member
           ∧ (∃ b ((b ∈ x) ∧ φ₁(b)))                         -- x has a 1-member
           ∧ (∃ d ((d ∈ x) ∧ φ₂(d)))                         -- x has a 2-member
           ∧ (∀ c ¬((c ∈ x) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ ¬φ₂(c))))) -- every member is 0, 1 or 2

with sub-predicates on a variable `t` (`φ₀`, `φ₁` reused from `Rayo.K0/K1`
via `zF`/`oneF`; `φ₂` the extensional "is 2" predicate `twoF` below):

    φ₀(t) := ∀ u ¬(u ∈ t)                                     -- "t is empty"
    φ₁(t) := (∃ u (u ∈ t)) ∧ (∀ u ∀ w ¬((u ∈ t) ∧ (w ∈ u)))  -- "t is {∅}"
    φ₂(t) := (∃ a ((a ∈ t) ∧ φ₀(a)))                          -- t has a 0-member
           ∧ (∃ b ((b ∈ t) ∧ φ₁(b)))                          -- t has a 1-member
           ∧ (∀ c ¬((c ∈ t) ∧ (¬φ₀(c) ∧ ¬φ₁(c))))            -- every member is 0 or 1

The "0/1/2" clause is written directly in the primitive alphabet as a De Morgan
negation ("no member is none-of-0/1/2"), so no `or`/`implies` abbreviation
expansion is needed. `∃` is a convention primitive (one symbol); in the
`Formula` datatype it has no constructor and is represented by the standard
`¬∀¬` expansion (a mechanization-only choice that does not change the convention
count, exactly as in `Rayo.K1`/`Rayo.K2`).

## Symbol count n₃ = 403

Counted under `notes/convention-notes.md` §2/§4 with the same fully-parenthesized
discipline as φ₀ (10), φ₁ (30) and φ₂ (128): atom = 3; `¬φ = |φ|+3`;
`(φ ∧ ψ) = |φ|+|ψ|+3`; `Q v (φ) = |φ|+4` (`∃`/`∀` primitive, one symbol each;
each variable occurrence one).

    φ₀(t)                                            = 10   (as in K0)
    φ₁(t)                                            = 30   (as in K1)
    φ₂(t)                                            = 128  (as in K2)
    E0 = ∃a ((a∈x) ∧ φ₀(a))       body 3+10+3=16     = 20
    E1 = ∃b ((b∈x) ∧ φ₁(b))       body 3+30+3=36     = 40
    E2 = ∃d ((d∈x) ∧ φ₂(d))       body 3+128+3=134   = 138
    U  = ∀c ¬((c∈x) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ ¬φ₂(c))))
         ¬φ₀=13, ¬φ₁=33, ¬φ₂=131,
         (¬φ₁∧¬φ₂)=33+131+3=167, (¬φ₀∧·)=13+167+3=183,
         (c∈x ∧ ·)=3+183+3=189, ¬·=192                = 196
    φ₃ = (E0 ∧ (E1 ∧ (E2 ∧ U)))   20+40+138+196 + 3·3 = 403

n₃ = 403. This is the cost of *this* recursive construction; it is an upper
bound on the true minimum, not a claim of minimality. Flagged per
`METHODOLOGY.md` C1.

## Extensionality (the k≥2 subtlety)

The HF model of `Rayo.Satisfaction` is non-extensional (a set is a *list*). As
for k=2, a member of a solution may be structurally different from the canonical
`0`/`1`/`2` yet extensionally equal, so strict structural uniqueness is false and
uniqueness holds only *up to extensional equality*. We state it with `ClassEq3`
(same 0/1/2 extensional class): `phi3_unique` shows any two solutions have the
same members up to `ClassEq3`, and the three `not_is…_and_is…` lemmas show the
classes are pairwise disjoint, so a solution is extensionally `{0, 1, 2} = 3`.

## Finding (recorded here, per this item)

- k = 3
- formula: `phi3` below (convention form in the header)
- symbol count n₃ = 403 (derivation above)
- Lean proof reference: `phi3_iff` (characterisation), `phi3_holds_of_three`
  (existence), `phi3_names_three` (member classification) and `phi3_unique`
  (uniqueness up to `ClassEq3`) in this file. The proofs have no proof holes.
-/

import Rayo.K2

namespace Rayo

/-- von-Neumann `3 = {0, 1, 2} = {∅, {∅}, {∅, {∅}}}`, as an HF term. -/
def three : HF := HF.mk [HF.empty, one, two]

/-- Extensional predicate "is (extensionally) `2 = {0, 1}`": has a 0-member, a
1-member, and every member is 0 or 1. This is exactly `Rayo.K2`'s φ₂
characterisation, lifted to a standalone predicate. -/
def IsTwo (a : HF) : Prop :=
  (∃ z, z ∈ a.elems ∧ IsZero z)
  ∧ (∃ o, o ∈ a.elems ∧ IsOne o)
  ∧ (∀ w, w ∈ a.elems → IsZero w ∨ IsOne w)

/-! ### Generic building blocks

`exists_member_iff` and `forall_member_not_bad` factor the "container has a
member satisfying P" and "every member of the container is not-bad" shapes,
reused for both the top-level φ₃ conjuncts and the `twoF` sub-predicate. -/

/-- "The container `cv` has a member for which `P` holds", where `P` (read on the
witness variable `w`) means the extensional predicate `Pp`. -/
theorem exists_member_iff (e : Env) (cv w : Nat) (P : Formula) (Pp : HF → Prop)
    (hcw : cv ≠ w)
    (hP : ∀ val, Sat (Env.update e w val) P ↔ Pp val) :
    Sat e (.neg (.all w (.neg (.conj (.mem w cv) P))))
      ↔ ∃ m, m ∈ (e cv).elems ∧ Pp m := by
  have hbody : ∀ m : HF, Sat (Env.update e w m) (.conj (.mem w cv) P)
      ↔ (m ∈ (e cv).elems ∧ Pp m) := by
    intro m
    have hw : Env.update e w m w = m := Env.update_same e w m
    have hc : Env.update e w m cv = e cv := Env.update_other e w cv m hcw
    simp only [Sat, HF.Mem, hw, hc, hP m]
  rw [show Sat e (.neg (.all w (.neg (.conj (.mem w cv) P))))
        ↔ ¬ ∀ m : HF, ¬ Sat (Env.update e w m) (.conj (.mem w cv) P) from Iff.rfl]
  constructor
  · intro h
    rcases Classical.em (∃ m, m ∈ (e cv).elems ∧ Pp m) with hex | hex
    · exact hex
    · exact absurd (fun m hp => hex ⟨m, (hbody m).mp hp⟩) h
  · rintro ⟨m, hm⟩ h
    exact h m ((hbody m).mpr hm)

/-- "Every member of the container `cv` fails the bad predicate `Bp`", where the
formula `B` (read on the quantifier variable `w`) means `Bp`. -/
theorem forall_member_not_bad (e : Env) (cv w : Nat) (B : Formula) (Bp : HF → Prop)
    (hcw : cv ≠ w)
    (hB : ∀ val, Sat (Env.update e w val) B ↔ Bp val) :
    Sat e (.all w (.neg (.conj (.mem w cv) B)))
      ↔ ∀ m, m ∈ (e cv).elems → ¬ Bp m := by
  have hbody : ∀ m : HF, Sat (Env.update e w m) (.neg (.conj (.mem w cv) B))
      ↔ ¬ (m ∈ (e cv).elems ∧ Bp m) := by
    intro m
    have hw : Env.update e w m w = m := Env.update_same e w m
    have hc : Env.update e w m cv = e cv := Env.update_other e w cv m hcw
    simp only [Sat, HF.Mem, hw, hc, hB m]
  have hall : Sat e (.all w (.neg (.conj (.mem w cv) B)))
      ↔ ∀ m, ¬ (m ∈ (e cv).elems ∧ Bp m) := by
    rw [show Sat e (.all w (.neg (.conj (.mem w cv) B)))
          ↔ ∀ m : HF, Sat (Env.update e w m) (.neg (.conj (.mem w cv) B)) from Iff.rfl]
    exact forall_congr' (fun m => hbody m)
  rw [hall]
  constructor
  · intro h m hm hb
    exact h m ⟨hm, hb⟩
  · intro h m hmb
    exact h m hmb.1 hmb.2

/-! ### The "is 2" sub-formula `φ₂(t)` on an arbitrary variable `t`. -/

/-- `twoF t a b c z1 o1 o2 cz co1 co2` — "`v_t` is extensionally `2 = {0, 1}`":
has a 0-member (`a`), a 1-member (`b`), and every member (`c`) is 0 or 1. -/
def twoF (t a b c z1 o1 o2 cz co1 co2 : Nat) : Formula :=
  .conj
    (.neg (.all a (.neg (.conj (.mem a t) (zF a z1)))))
    (.conj
      (.neg (.all b (.neg (.conj (.mem b t) (oneF b o1 o2)))))
      (.all c (.neg (.conj (.mem c t)
        (.conj (.neg (zF c cz)) (.neg (oneF c co1 co2)))))))

theorem twoF_iff (e : Env) (t a b c z1 o1 o2 cz co1 co2 : Nat)
    (hat : a ≠ t) (haz : a ≠ z1)
    (hbt : b ≠ t) (hbo1 : b ≠ o1) (hbo2 : b ≠ o2) (ho12 : o1 ≠ o2)
    (hct : c ≠ t) (hcz : c ≠ cz) (hco1 : c ≠ co1) (hco2 : c ≠ co2) (hco12 : co1 ≠ co2) :
    Sat e (twoF t a b c z1 o1 o2 cz co1 co2) ↔ IsTwo (e t) := by
  have hz : ∀ val, Sat (Env.update e a val) (zF a z1) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e a val) a z1 haz
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e b val) (oneF b o1 o2) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e b val) b o1 o2 hbo1 hbo2 ho12
    rwa [Env.update_same] at h
  have hE0 := exists_member_iff e t a (zF a z1) IsZero hat.symm hz
  have hE1 := exists_member_iff e t b (oneF b o1 o2) IsOne hbt.symm hoo
  have hB : ∀ val, Sat (Env.update e c val)
      (.conj (.neg (zF c cz)) (.neg (oneF c co1 co2)))
      ↔ (¬ IsZero val ∧ ¬ IsOne val) := by
    intro val
    have hzc : Sat (Env.update e c val) (zF c cz) ↔ IsZero val := by
      have h := zF_iff (Env.update e c val) c cz hcz
      rwa [Env.update_same] at h
    have hoc : Sat (Env.update e c val) (oneF c co1 co2) ↔ IsOne val := by
      have h := oneF_iff (Env.update e c val) c co1 co2 hco1 hco2 hco12
      rwa [Env.update_same] at h
    simp only [Sat, hzc, hoc]
  have hU := forall_member_not_bad e t c
    (.conj (.neg (zF c cz)) (.neg (oneF c co1 co2)))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val) hct.symm hB
  have hsplit : Sat e (twoF t a b c z1 o1 o2 cz co1 co2)
      ↔ Sat e (.neg (.all a (.neg (.conj (.mem a t) (zF a z1)))))
        ∧ (Sat e (.neg (.all b (.neg (.conj (.mem b t) (oneF b o1 o2)))))
           ∧ Sat e (.all c (.neg (.conj (.mem c t)
               (.conj (.neg (zF c cz)) (.neg (oneF c co1 co2))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hU]
  unfold IsTwo
  constructor
  · rintro ⟨h0, h1, hu⟩
    refine ⟨h0, h1, ?_⟩
    intro m hm
    rcases Classical.em (IsZero m) with hzm | hzm
    · exact Or.inl hzm
    · rcases Classical.em (IsOne m) with hom | hom
      · exact Or.inr hom
      · exact absurd ⟨hzm, hom⟩ (hu m hm)
  · rintro ⟨h0, h1, hu⟩
    refine ⟨h0, h1, ?_⟩
    intro m hm
    rintro ⟨hnz, hno⟩
    rcases hu m hm with hzm | hom
    · exact hnz hzm
    · exact hno hom

/-! ### The k = 3 formula and its characterisation. -/

/-- The k = 3 naming formula (see the file header for the convention form).
`x = v₀`; witnesses `a = v₁` (0-member), `b = v₂` (1-member), `d = v₃`
(2-member), member-quantifier `c = v₄`; each sub-predicate uses its own fresh
bound variables. -/
def phi3 : Formula :=
  .conj
    (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 5)))))
    (.conj
      (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 6 7)))))
      (.conj
        (.neg (.all 3 (.neg (.conj (.mem 3 0) (twoF 3 8 9 10 11 12 13 14 15 16)))))
        (.all 4 (.neg (.conj (.mem 4 0)
          (.conj (.neg (zF 4 17))
            (.conj (.neg (oneF 4 18 19))
              (.neg (twoF 4 20 21 22 23 24 25 26 27 28)))))))))

/-- `φ₃` holds of `x` exactly when `x` has a 0-member, a 1-member, a 2-member,
and every member is 0, 1 or 2 — i.e. `x` is extensionally `{0, 1, 2} = 3`. -/
theorem phi3_iff (e : Env) :
    Sat e phi3 ↔
      ( (∃ a, a ∈ (e 0).elems ∧ IsZero a)
        ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
        ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
        ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c ∨ IsTwo c)) ) := by
  have hz : ∀ val, Sat (Env.update e 1 val) (zF 1 5) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e 1 val) 1 5 (by decide)
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e 2 val) (oneF 2 6 7) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e 2 val) 2 6 7 (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have ht : ∀ val, Sat (Env.update e 3 val) (twoF 3 8 9 10 11 12 13 14 15 16) ↔ IsTwo val :=
    fun val => by
      have h := twoF_iff (Env.update e 3 val) 3 8 9 10 11 12 13 14 15 16
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
  have hE0 := exists_member_iff e 0 1 (zF 1 5) IsZero (by decide) hz
  have hE1 := exists_member_iff e 0 2 (oneF 2 6 7) IsOne (by decide) hoo
  have hE2 := exists_member_iff e 0 3 (twoF 3 8 9 10 11 12 13 14 15 16) IsTwo (by decide) ht
  have hB : ∀ val, Sat (Env.update e 4 val)
      (.conj (.neg (zF 4 17))
        (.conj (.neg (oneF 4 18 19)) (.neg (twoF 4 20 21 22 23 24 25 26 27 28))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) := by
    intro val
    have hz4 : Sat (Env.update e 4 val) (zF 4 17) ↔ IsZero val := by
      have h := zF_iff (Env.update e 4 val) 4 17 (by decide)
      rwa [Env.update_same] at h
    have ho4 : Sat (Env.update e 4 val) (oneF 4 18 19) ↔ IsOne val := by
      have h := oneF_iff (Env.update e 4 val) 4 18 19 (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht4 : Sat (Env.update e 4 val) (twoF 4 20 21 22 23 24 25 26 27 28) ↔ IsTwo val := by
      have h := twoF_iff (Env.update e 4 val) 4 20 21 22 23 24 25 26 27 28
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz4, ho4, ht4]
  have hU := forall_member_not_bad e 0 4
    (.conj (.neg (zF 4 17))
      (.conj (.neg (oneF 4 18 19)) (.neg (twoF 4 20 21 22 23 24 25 26 27 28))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) (by decide) hB
  have hsplit : Sat e phi3
      ↔ Sat e (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 5)))))
        ∧ (Sat e (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 6 7)))))
           ∧ (Sat e (.neg (.all 3 (.neg (.conj (.mem 3 0)
               (twoF 3 8 9 10 11 12 13 14 15 16)))))
              ∧ Sat e (.all 4 (.neg (.conj (.mem 4 0)
                  (.conj (.neg (zF 4 17))
                    (.conj (.neg (oneF 4 18 19))
                      (.neg (twoF 4 20 21 22 23 24 25 26 27 28))))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hU]
  constructor
  · rintro ⟨h0, h1, h2, hu⟩
    refine ⟨h0, h1, h2, ?_⟩
    intro m hm
    rcases Classical.em (IsZero m) with hzm | hzm
    · exact Or.inl hzm
    · rcases Classical.em (IsOne m) with hom | hom
      · exact Or.inr (Or.inl hom)
      · rcases Classical.em (IsTwo m) with htm | htm
        · exact Or.inr (Or.inr htm)
        · exact absurd ⟨hzm, hom, htm⟩ (hu m hm)
  · rintro ⟨h0, h1, h2, hu⟩
    refine ⟨h0, h1, h2, ?_⟩
    intro m hm
    rintro ⟨hnz, hno, hnt⟩
    rcases hu m hm with hzm | hom | htm
    · exact hnz hzm
    · exact hno hom
    · exact hnt htm

/-! ### Existence and uniqueness. -/

/-- The canonical `1 = {∅}` is (extensionally) `1`. -/
theorem isOne_one : IsOne one :=
  ⟨by simp [one, HF.elems], by
    intro w hw
    simp only [one, HF.elems, List.mem_singleton] at hw
    exact hw⟩

/-- The canonical `2 = {∅, {∅}}` is (extensionally) `2`. -/
theorem isTwo_two : IsTwo two := by
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ?_⟩
  · simp [two, HF.elems]
  · simp [two, HF.elems]
  · intro w hw
    simp only [two, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · exact Or.inl h
    · subst h; exact Or.inr isOne_one

/-- Existence: the canonical `3 = {∅, {∅}, {∅, {∅}}}` satisfies `φ₃`. -/
theorem phi3_holds_of_three : Sat (fun _ => three) phi3 := by
  rw [phi3_iff]
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ⟨two, ?_, isTwo_two⟩, ?_⟩
  · simp [three, HF.elems]
  · simp [three, HF.elems]
  · simp [three, HF.elems]
  · intro m hm
    simp only [three, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl isOne_one)
    · subst h; exact Or.inr (Or.inr isTwo_two)

/-- Naming: any solution has exactly the member-classification of `3` — a
0-member, a 1-member, a 2-member, and no other kind of member. -/
theorem phi3_names_three (e : Env) (h : Sat e phi3) :
    (∃ a, a ∈ (e 0).elems ∧ IsZero a)
    ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
    ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
    ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c ∨ IsTwo c)) :=
  (phi3_iff e).mp h

/-- The 0-class and the 2-class are disjoint: nothing is both. -/
theorem not_isZero_and_isTwo (a : HF) : ¬ (IsZero a ∧ IsTwo a) := by
  rintro ⟨h0, htwo⟩
  have h0' : a = HF.empty := h0
  obtain ⟨⟨z, hz, _⟩, _, _⟩ := htwo
  rw [h0'] at hz
  simp [HF.empty, HF.elems] at hz

/-- The 1-class and the 2-class are disjoint: nothing is both. A member of a
1-set is empty, but a 2-set has a nonempty (1-)member. -/
theorem not_isOne_and_isTwo (a : HF) : ¬ (IsOne a ∧ IsTwo a) := by
  rintro ⟨hone, htwo⟩
  obtain ⟨_, hallempty⟩ := hone
  obtain ⟨_, ⟨o, ho, hoOne⟩, _⟩ := htwo
  have heq : o = HF.empty := hallempty o ho
  rw [heq] at hoOne
  obtain ⟨hne, _⟩ := hoOne
  exact hne rfl

/-- Same 0/1/2 extensional class. On φ₃-solutions (whose members are only 0s,
1s and 2s) this is genuine extensional equality. -/
def ClassEq3 (z m : HF) : Prop :=
  (IsZero z ∧ IsZero m) ∨ (IsOne z ∧ IsOne m) ∨ (IsTwo z ∧ IsTwo m)

/-- Uniqueness up to extensional equality: any two solutions of `φ₃` have exactly
the same members up to `ClassEq3`. With the three disjointness lemmas
(`not_isZero_and_isOne`, `not_isZero_and_isTwo`, `not_isOne_and_isTwo`) this pins
every solution to the extensional set `{0, 1, 2} = 3`. -/
theorem phi3_unique (e e' : Env) (h : Sat e phi3) (h' : Sat e' phi3) :
    ∀ z, (∃ m, m ∈ (e 0).elems ∧ ClassEq3 z m)
        ↔ (∃ m, m ∈ (e' 0).elems ∧ ClassEq3 z m) := by
  obtain ⟨⟨a, ha, haz⟩, ⟨b, hb, hbo⟩, ⟨d, hd, hdt⟩, _⟩ := (phi3_iff e).mp h
  obtain ⟨⟨a', ha', haz'⟩, ⟨b', hb', hbo'⟩, ⟨d', hd', hdt'⟩, _⟩ := (phi3_iff e').mp h'
  intro z
  constructor
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩
    · exact ⟨a', ha', Or.inl ⟨hzz, haz'⟩⟩
    · exact ⟨b', hb', Or.inr (Or.inl ⟨hzo, hbo'⟩)⟩
    · exact ⟨d', hd', Or.inr (Or.inr ⟨hzt, hdt'⟩)⟩
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩
    · exact ⟨a, ha, Or.inl ⟨hzz, haz⟩⟩
    · exact ⟨b, hb, Or.inr (Or.inl ⟨hzo, hbo⟩)⟩
    · exact ⟨d, hd, Or.inr (Or.inr ⟨hzt, hdt⟩)⟩

end Rayo
