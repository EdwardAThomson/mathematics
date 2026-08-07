/-
`Rayo.K4` — the k = 4 naming-cost item.

We name the von-Neumann natural `4 = {0, 1, 2, 3}` with a first-order formula
over `∈` (and `=`), count its symbols under the frozen convention
(`notes/convention-notes.md`), and prove mechanically that its solutions are,
up to extensional equality, exactly `4`.

## The formula (convention form, `x = v₀`)

φ₄ is built *recursively* from φ₀ ("is 0"), φ₁ ("is 1"), φ₂ ("is 2") and
φ₃ ("is 3"):

    φ₄(x) := (∃ a ((a ∈ x) ∧ φ₀(a)))                              -- x has a 0-member
           ∧ (∃ b ((b ∈ x) ∧ φ₁(b)))                              -- x has a 1-member
           ∧ (∃ d ((d ∈ x) ∧ φ₂(d)))                              -- x has a 2-member
           ∧ (∃ g ((g ∈ x) ∧ φ₃(g)))                              -- x has a 3-member
           ∧ (∀ c ¬((c ∈ x) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ (¬φ₂(c) ∧ ¬φ₃(c)))))) -- members are 0,1,2 or 3

with sub-predicates on a variable `t` (`φ₀`, `φ₁`, `φ₂` reused from
`Rayo.K0/K1/K2` via `zF`/`oneF`/`twoF`; `φ₃` the extensional "is 3" predicate
`threeF` below, which is exactly `Rayo.K3`'s φ₃ characterisation lifted to a
standalone predicate):

    φ₀(t) := ∀ u ¬(u ∈ t)
    φ₁(t) := (∃ u (u ∈ t)) ∧ (∀ u ∀ w ¬((u ∈ t) ∧ (w ∈ u)))
    φ₂(t) := (∃ a ((a ∈ t) ∧ φ₀(a))) ∧ (∃ b ((b ∈ t) ∧ φ₁(b)))
           ∧ (∀ c ¬((c ∈ t) ∧ (¬φ₀(c) ∧ ¬φ₁(c))))
    φ₃(t) := (∃ a ((a ∈ t) ∧ φ₀(a))) ∧ (∃ b ((b ∈ t) ∧ φ₁(b)))
           ∧ (∃ d ((d ∈ t) ∧ φ₂(d)))
           ∧ (∀ c ¬((c ∈ t) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ ¬φ₂(c)))))

The "0/1/2/3" clause is written directly in the primitive alphabet as a De
Morgan negation ("no member is none-of-0/1/2/3"), so no `or`/`implies`
abbreviation expansion is needed. `∃` is a convention primitive (one symbol); in
the `Formula` datatype it has no constructor and is represented by the standard
`¬∀¬` expansion (a mechanization-only choice that does not change the convention
count, exactly as in `Rayo.K1`/`Rayo.K2`/`Rayo.K3`).

## Symbol count n₄ = 1228

Counted under `notes/convention-notes.md` §2/§4 with the same fully-parenthesized
discipline as φ₀ (10), φ₁ (30), φ₂ (128) and φ₃ (403): atom = 3; `¬φ = |φ|+3`;
`(φ ∧ ψ) = |φ|+|ψ|+3`; `Q v (φ) = |φ|+4` (`∃`/`∀` primitive, one symbol each;
each variable occurrence one). Each `E_i = ∃v ((v∈x) ∧ φ_i(v)) = |φ_i|+10`.

    φ₀(t)                                            = 10   (as in K0)
    φ₁(t)                                            = 30   (as in K1)
    φ₂(t)                                            = 128  (as in K2)
    φ₃(t)                                            = 403  (as in K3)
    E0 = ∃a ((a∈x) ∧ φ₀(a))       10+10              = 20
    E1 = ∃b ((b∈x) ∧ φ₁(b))       30+10              = 40
    E2 = ∃d ((d∈x) ∧ φ₂(d))       128+10             = 138
    E3 = ∃g ((g∈x) ∧ φ₃(g))       403+10             = 413
    U  = ∀c ¬((c∈x) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ (¬φ₂(c) ∧ ¬φ₃(c)))))
         ¬φ₀=13, ¬φ₁=33, ¬φ₂=131, ¬φ₃=406,
         (¬φ₂∧¬φ₃)=131+406+3=540, (¬φ₁∧·)=33+540+3=576,
         (¬φ₀∧·)=13+576+3=592, (c∈x ∧ ·)=3+592+3=598, ¬·=601   = 605
    φ₄ = (E0 ∧ (E1 ∧ (E2 ∧ (E3 ∧ U))))   20+40+138+413+605 + 4·3 = 1228

n₄ = 1228. This is the cost of *this* recursive construction; it is an upper
bound on the true minimum, not a claim of minimality. Flagged per
`METHODOLOGY.md` C1.

## Extensionality (the k≥2 subtlety)

The HF model of `Rayo.Satisfaction` is non-extensional (a set is a *list*). As
for k=2,3, a member of a solution may be structurally different from the
canonical `0`/`1`/`2`/`3` yet extensionally equal, so strict structural
uniqueness is false and uniqueness holds only *up to extensional equality*. We
state it with `ClassEq4` (same 0/1/2/3 extensional class): `phi4_unique` shows
any two solutions have the same members up to `ClassEq4`, and the six
`not_is…_and_is…` lemmas (three reused from `Rayo.K3`, three new here) show the
classes are pairwise disjoint, so a solution is extensionally `{0,1,2,3} = 4`.

## Finding (recorded here, per this item)

- k = 4
- formula: `phi4` below (convention form in the header)
- symbol count n₄ = 1228 (derivation above)
- Lean proof reference: `phi4_iff` (characterisation), `phi4_holds_of_four`
  (existence), `phi4_names_four` (member classification) and `phi4_unique`
  (uniqueness up to `ClassEq4`) in this file. The proofs have no proof holes.
-/

import Rayo.K3

namespace Rayo

/-- von-Neumann `4 = {0, 1, 2, 3}`, as an HF term. -/
def four : HF := HF.mk [HF.empty, one, two, three]

/-- Extensional predicate "is (extensionally) `3 = {0, 1, 2}`": has a 0-member, a
1-member, a 2-member, and every member is 0, 1 or 2. This is exactly `Rayo.K3`'s
φ₃ characterisation, lifted to a standalone predicate. -/
def IsThree (a : HF) : Prop :=
  (∃ z, z ∈ a.elems ∧ IsZero z)
  ∧ (∃ o, o ∈ a.elems ∧ IsOne o)
  ∧ (∃ w, w ∈ a.elems ∧ IsTwo w)
  ∧ (∀ w, w ∈ a.elems → IsZero w ∨ IsOne w ∨ IsTwo w)

/-! ### The "is 3" sub-formula `φ₃(t)` on an arbitrary variable `t`.

Unlike `Rayo.K3`'s `twoF`, which was parameterised over all of its fresh bound
variables, `threeF` uses a *fixed* block of bound variables `6..33` and takes
only its container `t`. Because `threeF` is only ever applied to a container
index `< 6` (in this file, to variables `4` and `5`), and its fixed block avoids
`0..5`, no variable-capture arises; the single hypothesis `t < 6` discharges
every "container ≠ bound variable" side condition. Choosing fixed bound-variable
indices is a mechanization-only convenience and does not affect the convention
symbol count (variable identity is free, `notes/convention-notes.md` §4). -/

/-- `threeF t` — "`v_t` is extensionally `3 = {0, 1, 2}`": has a 0-member, a
1-member, a 2-member, and every member is 0, 1 or 2. Bound variables are the
fixed block `6..33`. -/
def threeF (t : Nat) : Formula :=
  .conj
    (.neg (.all 6 (.neg (.conj (.mem 6 t) (zF 6 10)))))
    (.conj
      (.neg (.all 7 (.neg (.conj (.mem 7 t) (oneF 7 11 12)))))
      (.conj
        (.neg (.all 8 (.neg (.conj (.mem 8 t) (twoF 8 13 14 15 16 17 18 19 20 21)))))
        (.all 9 (.neg (.conj (.mem 9 t)
          (.conj (.neg (zF 9 22))
            (.conj (.neg (oneF 9 23 24))
              (.neg (twoF 9 25 26 27 28 29 30 31 32 33)))))))))

theorem threeF_iff (e : Env) (t : Nat) (ht : t < 6) :
    Sat e (threeF t) ↔ IsThree (e t) := by
  have hz : ∀ val, Sat (Env.update e 6 val) (zF 6 10) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e 6 val) 6 10 (by decide)
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e 7 val) (oneF 7 11 12) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e 7 val) 7 11 12 (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have htt : ∀ val, Sat (Env.update e 8 val) (twoF 8 13 14 15 16 17 18 19 20 21) ↔ IsTwo val :=
    fun val => by
      have h := twoF_iff (Env.update e 8 val) 8 13 14 15 16 17 18 19 20 21
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
  have hE0 := exists_member_iff e t 6 (zF 6 10) IsZero (by omega) hz
  have hE1 := exists_member_iff e t 7 (oneF 7 11 12) IsOne (by omega) hoo
  have hE2 := exists_member_iff e t 8 (twoF 8 13 14 15 16 17 18 19 20 21) IsTwo (by omega) htt
  have hB : ∀ val, Sat (Env.update e 9 val)
      (.conj (.neg (zF 9 22))
        (.conj (.neg (oneF 9 23 24)) (.neg (twoF 9 25 26 27 28 29 30 31 32 33))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) := by
    intro val
    have hz9 : Sat (Env.update e 9 val) (zF 9 22) ↔ IsZero val := by
      have h := zF_iff (Env.update e 9 val) 9 22 (by decide)
      rwa [Env.update_same] at h
    have ho9 : Sat (Env.update e 9 val) (oneF 9 23 24) ↔ IsOne val := by
      have h := oneF_iff (Env.update e 9 val) 9 23 24 (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht9 : Sat (Env.update e 9 val) (twoF 9 25 26 27 28 29 30 31 32 33) ↔ IsTwo val := by
      have h := twoF_iff (Env.update e 9 val) 9 25 26 27 28 29 30 31 32 33
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz9, ho9, ht9]
  have hU := forall_member_not_bad e t 9
    (.conj (.neg (zF 9 22))
      (.conj (.neg (oneF 9 23 24)) (.neg (twoF 9 25 26 27 28 29 30 31 32 33))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) (by omega) hB
  have hsplit : Sat e (threeF t)
      ↔ Sat e (.neg (.all 6 (.neg (.conj (.mem 6 t) (zF 6 10)))))
        ∧ (Sat e (.neg (.all 7 (.neg (.conj (.mem 7 t) (oneF 7 11 12)))))
           ∧ (Sat e (.neg (.all 8 (.neg (.conj (.mem 8 t)
               (twoF 8 13 14 15 16 17 18 19 20 21)))))
              ∧ Sat e (.all 9 (.neg (.conj (.mem 9 t)
                  (.conj (.neg (zF 9 22))
                    (.conj (.neg (oneF 9 23 24))
                      (.neg (twoF 9 25 26 27 28 29 30 31 32 33))))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hU]
  unfold IsThree
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

/-- The canonical `3 = {∅, {∅}, {∅, {∅}}}` is (extensionally) `3`. -/
theorem isThree_three : IsThree three := by
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ⟨two, ?_, isTwo_two⟩, ?_⟩
  · simp [three, HF.elems]
  · simp [three, HF.elems]
  · simp [three, HF.elems]
  · intro w hw
    simp only [three, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl isOne_one)
    · subst h; exact Or.inr (Or.inr isTwo_two)

/-! ### The k = 4 formula and its characterisation. -/

/-- The k = 4 naming formula (see the file header for the convention form).
`x = v₀`; witnesses `a = v₁` (0-member), `b = v₂` (1-member), `d = v₃`
(2-member), `g = v₄` (3-member), member-quantifier `c = v₅`; the `zF`/`oneF`/
`twoF` sub-predicates use fresh bound variables `34..57`, and each `threeF` uses
its own fixed block `6..33`. -/
def phi4 : Formula :=
  .conj
    (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 34)))))
    (.conj
      (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 35 36)))))
      (.conj
        (.neg (.all 3 (.neg (.conj (.mem 3 0) (twoF 3 37 38 39 40 41 42 43 44 45)))))
        (.conj
          (.neg (.all 4 (.neg (.conj (.mem 4 0) (threeF 4)))))
          (.all 5 (.neg (.conj (.mem 5 0)
            (.conj (.neg (zF 5 46))
              (.conj (.neg (oneF 5 47 48))
                (.conj (.neg (twoF 5 49 50 51 52 53 54 55 56 57))
                  (.neg (threeF 5)))))))))))

/-- `φ₄` holds of `x` exactly when `x` has a 0-member, a 1-member, a 2-member, a
3-member, and every member is 0, 1, 2 or 3 — i.e. `x` is extensionally
`{0, 1, 2, 3} = 4`. -/
theorem phi4_iff (e : Env) :
    Sat e phi4 ↔
      ( (∃ a, a ∈ (e 0).elems ∧ IsZero a)
        ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
        ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
        ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
        ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c)) ) := by
  have hz : ∀ val, Sat (Env.update e 1 val) (zF 1 34) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e 1 val) 1 34 (by decide)
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e 2 val) (oneF 2 35 36) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e 2 val) 2 35 36 (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have ht2 : ∀ val, Sat (Env.update e 3 val) (twoF 3 37 38 39 40 41 42 43 44 45) ↔ IsTwo val :=
    fun val => by
      have h := twoF_iff (Env.update e 3 val) 3 37 38 39 40 41 42 43 44 45
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
  have ht3 : ∀ val, Sat (Env.update e 4 val) (threeF 4) ↔ IsThree val := fun val => by
    have h := threeF_iff (Env.update e 4 val) 4 (by decide)
    rwa [Env.update_same] at h
  have hE0 := exists_member_iff e 0 1 (zF 1 34) IsZero (by decide) hz
  have hE1 := exists_member_iff e 0 2 (oneF 2 35 36) IsOne (by decide) hoo
  have hE2 := exists_member_iff e 0 3 (twoF 3 37 38 39 40 41 42 43 44 45) IsTwo (by decide) ht2
  have hE3 := exists_member_iff e 0 4 (threeF 4) IsThree (by decide) ht3
  have hB : ∀ val, Sat (Env.update e 5 val)
      (.conj (.neg (zF 5 46))
        (.conj (.neg (oneF 5 47 48))
          (.conj (.neg (twoF 5 49 50 51 52 53 54 55 56 57)) (.neg (threeF 5)))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val) := by
    intro val
    have hz5 : Sat (Env.update e 5 val) (zF 5 46) ↔ IsZero val := by
      have h := zF_iff (Env.update e 5 val) 5 46 (by decide)
      rwa [Env.update_same] at h
    have ho5 : Sat (Env.update e 5 val) (oneF 5 47 48) ↔ IsOne val := by
      have h := oneF_iff (Env.update e 5 val) 5 47 48 (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht5 : Sat (Env.update e 5 val) (twoF 5 49 50 51 52 53 54 55 56 57) ↔ IsTwo val := by
      have h := twoF_iff (Env.update e 5 val) 5 49 50 51 52 53 54 55 56 57
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht35 : Sat (Env.update e 5 val) (threeF 5) ↔ IsThree val := by
      have h := threeF_iff (Env.update e 5 val) 5 (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz5, ho5, ht5, ht35]
  have hU := forall_member_not_bad e 0 5
    (.conj (.neg (zF 5 46))
      (.conj (.neg (oneF 5 47 48))
        (.conj (.neg (twoF 5 49 50 51 52 53 54 55 56 57)) (.neg (threeF 5)))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val) (by decide) hB
  have hsplit : Sat e phi4
      ↔ Sat e (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 34)))))
        ∧ (Sat e (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 35 36)))))
           ∧ (Sat e (.neg (.all 3 (.neg (.conj (.mem 3 0)
               (twoF 3 37 38 39 40 41 42 43 44 45)))))
              ∧ (Sat e (.neg (.all 4 (.neg (.conj (.mem 4 0) (threeF 4)))))
                 ∧ Sat e (.all 5 (.neg (.conj (.mem 5 0)
                     (.conj (.neg (zF 5 46))
                       (.conj (.neg (oneF 5 47 48))
                         (.conj (.neg (twoF 5 49 50 51 52 53 54 55 56 57))
                           (.neg (threeF 5))))))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hE3, hU]
  constructor
  · rintro ⟨h0, h1, h2, h3, hu⟩
    refine ⟨h0, h1, h2, h3, ?_⟩
    intro m hm
    rcases Classical.em (IsZero m) with hzm | hzm
    · exact Or.inl hzm
    · rcases Classical.em (IsOne m) with hom | hom
      · exact Or.inr (Or.inl hom)
      · rcases Classical.em (IsTwo m) with htm | htm
        · exact Or.inr (Or.inr (Or.inl htm))
        · rcases Classical.em (IsThree m) with h3m | h3m
          · exact Or.inr (Or.inr (Or.inr h3m))
          · exact absurd ⟨hzm, hom, htm, h3m⟩ (hu m hm)
  · rintro ⟨h0, h1, h2, h3, hu⟩
    refine ⟨h0, h1, h2, h3, ?_⟩
    intro m hm
    rintro ⟨hnz, hno, hnt, hn3⟩
    rcases hu m hm with hzm | hom | htm | h3m
    · exact hnz hzm
    · exact hno hom
    · exact hnt htm
    · exact hn3 h3m

/-- Existence: the canonical `4 = {∅, {∅}, {∅,{∅}}, {∅,{∅},{∅,{∅}}}}` satisfies `φ₄`. -/
theorem phi4_holds_of_four : Sat (fun _ => four) phi4 := by
  rw [phi4_iff]
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ⟨two, ?_, isTwo_two⟩,
    ⟨three, ?_, isThree_three⟩, ?_⟩
  · simp [four, HF.elems]
  · simp [four, HF.elems]
  · simp [four, HF.elems]
  · simp [four, HF.elems]
  · intro m hm
    simp only [four, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl isOne_one)
    · subst h; exact Or.inr (Or.inr (Or.inl isTwo_two))
    · subst h; exact Or.inr (Or.inr (Or.inr isThree_three))

/-- Naming: any solution has exactly the member-classification of `4` — a
0-member, a 1-member, a 2-member, a 3-member, and no other kind of member. -/
theorem phi4_names_four (e : Env) (h : Sat e phi4) :
    (∃ a, a ∈ (e 0).elems ∧ IsZero a)
    ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
    ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
    ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
    ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c)) :=
  (phi4_iff e).mp h

/-! ### Class disjointness (the new k = 4 cases). -/

/-- The 0-class and the 3-class are disjoint: nothing is both. A 3-set has a
member, but `0 = ∅` has none. -/
theorem not_isZero_and_isThree (a : HF) : ¬ (IsZero a ∧ IsThree a) := by
  rintro ⟨h0, hthree⟩
  have h0' : a = HF.empty := h0
  obtain ⟨⟨z, hz, _⟩, _, _, _⟩ := hthree
  rw [h0'] at hz
  simp [HF.empty, HF.elems] at hz

/-- The 1-class and the 3-class are disjoint: nothing is both. A member of a
1-set is empty, but a 3-set has a (nonempty) 2-member. -/
theorem not_isOne_and_isThree (a : HF) : ¬ (IsOne a ∧ IsThree a) := by
  rintro ⟨hone, hthree⟩
  obtain ⟨_, hallempty⟩ := hone
  obtain ⟨_, _, ⟨w, hw, hwTwo⟩, _⟩ := hthree
  have heq : w = HF.empty := hallempty w hw
  rw [heq] at hwTwo
  obtain ⟨⟨z, hz, _⟩, _, _⟩ := hwTwo
  simp [HF.empty, HF.elems] at hz

/-- The 2-class and the 3-class are disjoint: nothing is both. A 2-set's members
are only 0s and 1s, but a 3-set has a 2-member, and `2` is neither 0 nor 1. -/
theorem not_isTwo_and_isThree (a : HF) : ¬ (IsTwo a ∧ IsThree a) := by
  rintro ⟨htwo, hthree⟩
  obtain ⟨_, _, htwoAll⟩ := htwo
  obtain ⟨_, _, ⟨w, hw, hwTwo⟩, _⟩ := hthree
  rcases htwoAll w hw with hzw | how
  · exact not_isZero_and_isTwo w ⟨hzw, hwTwo⟩
  · exact not_isOne_and_isTwo w ⟨how, hwTwo⟩

/-- Same 0/1/2/3 extensional class. On φ₄-solutions (whose members are only 0s,
1s, 2s and 3s) this is genuine extensional equality. -/
def ClassEq4 (z m : HF) : Prop :=
  (IsZero z ∧ IsZero m) ∨ (IsOne z ∧ IsOne m) ∨ (IsTwo z ∧ IsTwo m) ∨ (IsThree z ∧ IsThree m)

/-- Uniqueness up to extensional equality: any two solutions of `φ₄` have exactly
the same members up to `ClassEq4`. With the six disjointness lemmas
(`not_isZero_and_isOne`, `not_isZero_and_isTwo`, `not_isOne_and_isTwo`,
`not_isZero_and_isThree`, `not_isOne_and_isThree`, `not_isTwo_and_isThree`) this
pins every solution to the extensional set `{0, 1, 2, 3} = 4`. -/
theorem phi4_unique (e e' : Env) (h : Sat e phi4) (h' : Sat e' phi4) :
    ∀ z, (∃ m, m ∈ (e 0).elems ∧ ClassEq4 z m)
        ↔ (∃ m, m ∈ (e' 0).elems ∧ ClassEq4 z m) := by
  obtain ⟨⟨a, ha, haz⟩, ⟨b, hb, hbo⟩, ⟨d, hd, hdt⟩, ⟨g, hg, hg3⟩, _⟩ := (phi4_iff e).mp h
  obtain ⟨⟨a', ha', haz'⟩, ⟨b', hb', hbo'⟩, ⟨d', hd', hdt'⟩, ⟨g', hg', hg3'⟩, _⟩ :=
    (phi4_iff e').mp h'
  intro z
  constructor
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩
    · exact ⟨a', ha', Or.inl ⟨hzz, haz'⟩⟩
    · exact ⟨b', hb', Or.inr (Or.inl ⟨hzo, hbo'⟩)⟩
    · exact ⟨d', hd', Or.inr (Or.inr (Or.inl ⟨hzt, hdt'⟩))⟩
    · exact ⟨g', hg', Or.inr (Or.inr (Or.inr ⟨hz3, hg3'⟩))⟩
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩
    · exact ⟨a, ha, Or.inl ⟨hzz, haz⟩⟩
    · exact ⟨b, hb, Or.inr (Or.inl ⟨hzo, hbo⟩)⟩
    · exact ⟨d, hd, Or.inr (Or.inr (Or.inl ⟨hzt, hdt⟩))⟩
    · exact ⟨g, hg, Or.inr (Or.inr (Or.inr ⟨hz3, hg3⟩))⟩

end Rayo
