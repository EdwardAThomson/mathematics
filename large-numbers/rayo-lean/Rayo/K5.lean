/-
`Rayo.K5` — the k = 5 naming-cost item.

We name the von-Neumann natural `5 = {0, 1, 2, 3, 4}` with a first-order formula
over `∈` (and `=`), count its symbols under the frozen convention
(`notes/convention-notes.md`), and prove mechanically that its solutions are,
up to extensional equality, exactly `5`.

## The formula (convention form, `x = v₀`)

φ₅ is built *recursively* from φ₀ ("is 0"), φ₁ ("is 1"), φ₂ ("is 2"),
φ₃ ("is 3") and φ₄ ("is 4"):

    φ₅(x) := (∃ a ((a ∈ x) ∧ φ₀(a)))                              -- x has a 0-member
           ∧ (∃ b ((b ∈ x) ∧ φ₁(b)))                              -- x has a 1-member
           ∧ (∃ d ((d ∈ x) ∧ φ₂(d)))                              -- x has a 2-member
           ∧ (∃ g ((g ∈ x) ∧ φ₃(g)))                              -- x has a 3-member
           ∧ (∃ h ((h ∈ x) ∧ φ₄(h)))                              -- x has a 4-member
           ∧ (∀ c ¬((c ∈ x) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ (¬φ₂(c) ∧ (¬φ₃(c) ∧ ¬φ₄(c)))))))
                                                                  -- members are 0,1,2,3 or 4

with the sub-predicates φ₀, φ₁, φ₂, φ₃, φ₄ ("is 0/1/2/3/4") as in K0–K4.
The "0/1/2/3/4" clause is written directly in the primitive alphabet as a De
Morgan negation ("no member is none-of-0/1/2/3/4"), so no `or`/`implies`
abbreviation expansion is needed. `∃` is a convention primitive (one symbol); in
the `Formula` datatype it has no constructor and is represented by the standard
`¬∀¬` expansion (a mechanization-only choice that does not change the convention
count, exactly as in `Rayo.K1`–`Rayo.K4`).

## Symbol count n₅ = 3703

Counted under `notes/convention-notes.md` §2/§4 with the same fully-parenthesized
discipline as φ₀ (10), φ₁ (30), φ₂ (128), φ₃ (403) and φ₄ (1228): atom = 3;
`¬φ = |φ|+3`; `(φ ∧ ψ) = |φ|+|ψ|+3`; `Q v (φ) = |φ|+4` (`∃`/`∀` primitive, one
symbol each; each variable occurrence one). Each `E_i = ∃v ((v∈x) ∧ φ_i(v)) =
|φ_i|+10`.

    φ₀(t)                                            = 10   (as in K0)
    φ₁(t)                                            = 30   (as in K1)
    φ₂(t)                                            = 128  (as in K2)
    φ₃(t)                                            = 403  (as in K3)
    φ₄(t)                                            = 1228 (as in K4)
    E0 = ∃a ((a∈x) ∧ φ₀(a))       10+10              = 20
    E1 = ∃b ((b∈x) ∧ φ₁(b))       30+10              = 40
    E2 = ∃d ((d∈x) ∧ φ₂(d))       128+10             = 138
    E3 = ∃g ((g∈x) ∧ φ₃(g))       403+10             = 413
    E4 = ∃h ((h∈x) ∧ φ₄(h))       1228+10            = 1238
    U  = ∀c ¬((c∈x) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ (¬φ₂(c) ∧ (¬φ₃(c) ∧ ¬φ₄(c))))))
         ¬φ₀=13, ¬φ₁=33, ¬φ₂=131, ¬φ₃=406, ¬φ₄=1231,
         (¬φ₃∧¬φ₄)=406+1231+3=1640, (¬φ₂∧·)=131+1640+3=1774,
         (¬φ₁∧·)=33+1774+3=1810, (¬φ₀∧·)=13+1810+3=1826,
         (c∈x ∧ ·)=3+1826+3=1832, ¬·=1835, ∀c(·)=1835+4  = 1839
    φ₅ = (E0 ∧ (E1 ∧ (E2 ∧ (E3 ∧ (E4 ∧ U)))))
         20+40+138+413+1238+1839 + 5·3 = 3688 + 15    = 3703

n₅ = 3703. This is the cost of *this* recursive construction; it is an upper
bound on the true minimum, not a claim of minimality. Flagged per
`METHODOLOGY.md` C1.

## Extensionality (the k≥2 subtlety)

The HF model of `Rayo.Satisfaction` is non-extensional (a set is a *list*). As
for k=2,3,4, a member of a solution may be structurally different from the
canonical `0`/…/`4` yet extensionally equal, so strict structural uniqueness is
false and uniqueness holds only *up to extensional equality*. We state it with
`ClassEq5` (same 0/1/2/3/4 extensional class): `phi5_unique` shows any two
solutions have the same members up to `ClassEq5`, and the ten `not_is…_and_is…`
lemmas (six reused from `Rayo.K3`/`Rayo.K4`, four new here) show the classes are
pairwise disjoint, so a solution is extensionally `{0,1,2,3,4} = 5`.

## Mechanization note on bound variables

`Rayo.K4`'s `threeF` uses a *fixed* block `6..33` and requires its container
`< 6`. That fixed block cannot be applied to variable `6` (φ₅'s member
quantifier), so here we use `threeG`, an "is 3" predicate with fixed block
`7..34` requiring container `< 7`; it is applied to `3, 4, 6`. `fourF` ("is 4")
uses a fixed block for its own witnesses and reuses `threeG` for its "is 3"
sub-predicate. Choosing fixed bound-variable indices is a mechanization-only
convenience and does not affect the convention symbol count (variable identity is
free, `notes/convention-notes.md` §4).

## Finding (recorded here, per this item)

- k = 5
- formula: `phi5` below (convention form in the header)
- symbol count n₅ = 3703 (derivation above)
- Lean proof reference: `phi5_iff` (characterisation), `phi5_holds_of_five`
  (existence), `phi5_names_five` (member classification) and `phi5_unique`
  (uniqueness up to `ClassEq5`) in this file. The proofs have no proof holes.
-/

import Rayo.K4

namespace Rayo

/-- von-Neumann `5 = {0, 1, 2, 3, 4}`, as an HF term. -/
def five : HF := HF.mk [HF.empty, one, two, three, four]

/-- Extensional predicate "is (extensionally) `4 = {0, 1, 2, 3}`": has a
0-member, a 1-member, a 2-member, a 3-member, and every member is 0, 1, 2 or 3.
This is exactly `Rayo.K4`'s φ₄ characterisation, lifted to a standalone
predicate. -/
def IsFour (a : HF) : Prop :=
  (∃ z, z ∈ a.elems ∧ IsZero z)
  ∧ (∃ o, o ∈ a.elems ∧ IsOne o)
  ∧ (∃ w, w ∈ a.elems ∧ IsTwo w)
  ∧ (∃ v, v ∈ a.elems ∧ IsThree v)
  ∧ (∀ w, w ∈ a.elems → IsZero w ∨ IsOne w ∨ IsTwo w ∨ IsThree w)

/-! ### The "is 3" sub-formula `threeG(t)` — like `Rayo.K4`'s `threeF`, but with
fixed block `7..34` (requiring container `t < 7`), so it can also be applied to
variable `6` (φ₅'s member quantifier). -/

/-- `threeG t` — "`v_t` is extensionally `3 = {0, 1, 2}`": has a 0-member, a
1-member, a 2-member, and every member is 0, 1 or 2. Bound variables are the
fixed block `7..34`. -/
def threeG (t : Nat) : Formula :=
  .conj
    (.neg (.all 7 (.neg (.conj (.mem 7 t) (zF 7 11)))))
    (.conj
      (.neg (.all 8 (.neg (.conj (.mem 8 t) (oneF 8 12 13)))))
      (.conj
        (.neg (.all 9 (.neg (.conj (.mem 9 t) (twoF 9 14 15 16 17 18 19 20 21 22)))))
        (.all 10 (.neg (.conj (.mem 10 t)
          (.conj (.neg (zF 10 23))
            (.conj (.neg (oneF 10 24 25))
              (.neg (twoF 10 26 27 28 29 30 31 32 33 34)))))))))

theorem threeG_iff (e : Env) (t : Nat) (ht : t < 7) :
    Sat e (threeG t) ↔ IsThree (e t) := by
  have hz : ∀ val, Sat (Env.update e 7 val) (zF 7 11) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e 7 val) 7 11 (by decide)
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e 8 val) (oneF 8 12 13) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e 8 val) 8 12 13 (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have htt : ∀ val, Sat (Env.update e 9 val) (twoF 9 14 15 16 17 18 19 20 21 22) ↔ IsTwo val :=
    fun val => by
      have h := twoF_iff (Env.update e 9 val) 9 14 15 16 17 18 19 20 21 22
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
  have hE0 := exists_member_iff e t 7 (zF 7 11) IsZero (by omega) hz
  have hE1 := exists_member_iff e t 8 (oneF 8 12 13) IsOne (by omega) hoo
  have hE2 := exists_member_iff e t 9 (twoF 9 14 15 16 17 18 19 20 21 22) IsTwo (by omega) htt
  have hB : ∀ val, Sat (Env.update e 10 val)
      (.conj (.neg (zF 10 23))
        (.conj (.neg (oneF 10 24 25)) (.neg (twoF 10 26 27 28 29 30 31 32 33 34))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) := by
    intro val
    have hz9 : Sat (Env.update e 10 val) (zF 10 23) ↔ IsZero val := by
      have h := zF_iff (Env.update e 10 val) 10 23 (by decide)
      rwa [Env.update_same] at h
    have ho9 : Sat (Env.update e 10 val) (oneF 10 24 25) ↔ IsOne val := by
      have h := oneF_iff (Env.update e 10 val) 10 24 25 (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht9 : Sat (Env.update e 10 val) (twoF 10 26 27 28 29 30 31 32 33 34) ↔ IsTwo val := by
      have h := twoF_iff (Env.update e 10 val) 10 26 27 28 29 30 31 32 33 34
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz9, ho9, ht9]
  have hU := forall_member_not_bad e t 10
    (.conj (.neg (zF 10 23))
      (.conj (.neg (oneF 10 24 25)) (.neg (twoF 10 26 27 28 29 30 31 32 33 34))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) (by omega) hB
  have hsplit : Sat e (threeG t)
      ↔ Sat e (.neg (.all 7 (.neg (.conj (.mem 7 t) (zF 7 11)))))
        ∧ (Sat e (.neg (.all 8 (.neg (.conj (.mem 8 t) (oneF 8 12 13)))))
           ∧ (Sat e (.neg (.all 9 (.neg (.conj (.mem 9 t)
               (twoF 9 14 15 16 17 18 19 20 21 22)))))
              ∧ Sat e (.all 10 (.neg (.conj (.mem 10 t)
                  (.conj (.neg (zF 10 23))
                    (.conj (.neg (oneF 10 24 25))
                      (.neg (twoF 10 26 27 28 29 30 31 32 33 34))))))))) := Iff.rfl
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

/-! ### The "is 4" sub-formula `fourF(t)` on a container variable `t`.

`fourF`'s own witnesses use a fixed high block (`35..61`), its "is 3"
sub-predicate is `threeG` applied to the low variables `3, 4` (both `< 7`), and
the single hypotheses `t ≠ 3, 4, 35, 37, 40` discharge every "container ≠ bound
variable" side condition. In φ₅, `fourF` is applied only to variables `5` and
`6`, for which those inequalities hold. -/

/-- `fourF t` — "`v_t` is extensionally `4 = {0, 1, 2, 3}`": has a 0-member, a
1-member, a 2-member, a 3-member, and every member is 0, 1, 2 or 3. -/
def fourF (t : Nat) : Formula :=
  .conj
    (.neg (.all 35 (.neg (.conj (.mem 35 t) (zF 35 36)))))
    (.conj
      (.neg (.all 37 (.neg (.conj (.mem 37 t) (oneF 37 38 39)))))
      (.conj
        (.neg (.all 40 (.neg (.conj (.mem 40 t) (twoF 40 41 42 43 44 45 46 47 48 49)))))
        (.conj
          (.neg (.all 3 (.neg (.conj (.mem 3 t) (threeG 3)))))
          (.all 4 (.neg (.conj (.mem 4 t)
            (.conj (.neg (zF 4 50))
              (.conj (.neg (oneF 4 51 52))
                (.conj (.neg (twoF 4 53 54 55 56 57 58 59 60 61))
                  (.neg (threeG 4)))))))))))

theorem fourF_iff (e : Env) (t : Nat)
    (h3 : t ≠ 3) (h4 : t ≠ 4) (h35 : t ≠ 35) (h37 : t ≠ 37) (h40 : t ≠ 40) :
    Sat e (fourF t) ↔ IsFour (e t) := by
  have hz : ∀ val, Sat (Env.update e 35 val) (zF 35 36) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e 35 val) 35 36 (by decide)
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e 37 val) (oneF 37 38 39) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e 37 val) 37 38 39 (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have ht2 : ∀ val, Sat (Env.update e 40 val) (twoF 40 41 42 43 44 45 46 47 48 49) ↔ IsTwo val :=
    fun val => by
      have h := twoF_iff (Env.update e 40 val) 40 41 42 43 44 45 46 47 48 49
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
  have ht3 : ∀ val, Sat (Env.update e 3 val) (threeG 3) ↔ IsThree val := fun val => by
    have h := threeG_iff (Env.update e 3 val) 3 (by decide)
    rwa [Env.update_same] at h
  have hE0 := exists_member_iff e t 35 (zF 35 36) IsZero h35 hz
  have hE1 := exists_member_iff e t 37 (oneF 37 38 39) IsOne h37 hoo
  have hE2 := exists_member_iff e t 40 (twoF 40 41 42 43 44 45 46 47 48 49) IsTwo h40 ht2
  have hE3 := exists_member_iff e t 3 (threeG 3) IsThree h3 ht3
  have hB : ∀ val, Sat (Env.update e 4 val)
      (.conj (.neg (zF 4 50))
        (.conj (.neg (oneF 4 51 52))
          (.conj (.neg (twoF 4 53 54 55 56 57 58 59 60 61)) (.neg (threeG 4)))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val) := by
    intro val
    have hz5 : Sat (Env.update e 4 val) (zF 4 50) ↔ IsZero val := by
      have h := zF_iff (Env.update e 4 val) 4 50 (by decide)
      rwa [Env.update_same] at h
    have ho5 : Sat (Env.update e 4 val) (oneF 4 51 52) ↔ IsOne val := by
      have h := oneF_iff (Env.update e 4 val) 4 51 52 (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht5 : Sat (Env.update e 4 val) (twoF 4 53 54 55 56 57 58 59 60 61) ↔ IsTwo val := by
      have h := twoF_iff (Env.update e 4 val) 4 53 54 55 56 57 58 59 60 61
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht35 : Sat (Env.update e 4 val) (threeG 4) ↔ IsThree val := by
      have h := threeG_iff (Env.update e 4 val) 4 (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz5, ho5, ht5, ht35]
  have hU := forall_member_not_bad e t 4
    (.conj (.neg (zF 4 50))
      (.conj (.neg (oneF 4 51 52))
        (.conj (.neg (twoF 4 53 54 55 56 57 58 59 60 61)) (.neg (threeG 4)))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val) h4 hB
  have hsplit : Sat e (fourF t)
      ↔ Sat e (.neg (.all 35 (.neg (.conj (.mem 35 t) (zF 35 36)))))
        ∧ (Sat e (.neg (.all 37 (.neg (.conj (.mem 37 t) (oneF 37 38 39)))))
           ∧ (Sat e (.neg (.all 40 (.neg (.conj (.mem 40 t)
               (twoF 40 41 42 43 44 45 46 47 48 49)))))
              ∧ (Sat e (.neg (.all 3 (.neg (.conj (.mem 3 t) (threeG 3)))))
                 ∧ Sat e (.all 4 (.neg (.conj (.mem 4 t)
                     (.conj (.neg (zF 4 50))
                       (.conj (.neg (oneF 4 51 52))
                         (.conj (.neg (twoF 4 53 54 55 56 57 58 59 60 61))
                           (.neg (threeG 4))))))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hE3, hU]
  unfold IsFour
  constructor
  · rintro ⟨h0, h1, h2, h3', hu⟩
    refine ⟨h0, h1, h2, h3', ?_⟩
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
  · rintro ⟨h0, h1, h2, h3', hu⟩
    refine ⟨h0, h1, h2, h3', ?_⟩
    intro m hm
    rintro ⟨hnz, hno, hnt, hn3⟩
    rcases hu m hm with hzm | hom | htm | h3m
    · exact hnz hzm
    · exact hno hom
    · exact hnt htm
    · exact hn3 h3m

/-- The canonical `4 = {0,1,2,3}` is (extensionally) `4`. -/
theorem isFour_four : IsFour four := by
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ⟨two, ?_, isTwo_two⟩,
    ⟨three, ?_, isThree_three⟩, ?_⟩
  · simp [four, HF.elems]
  · simp [four, HF.elems]
  · simp [four, HF.elems]
  · simp [four, HF.elems]
  · intro w hw
    simp only [four, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl isOne_one)
    · subst h; exact Or.inr (Or.inr (Or.inl isTwo_two))
    · subst h; exact Or.inr (Or.inr (Or.inr isThree_three))

/-! ### The k = 5 formula and its characterisation. -/

/-- The k = 5 naming formula (see the file header for the convention form).
`x = v₀`; witnesses `a = v₁` (0-member), `b = v₂` (1-member), `d = v₃`
(2-member), `g = v₄` (3-member), `h = v₅` (4-member), member-quantifier
`c = v₆`; the `zF`/`oneF`/`twoF` sub-predicates use fresh bound variables
`62..85`, `threeG` uses its fixed block `7..34`, and `fourF` its own blocks. -/
def phi5 : Formula :=
  .conj
    (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 62)))))
    (.conj
      (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 63 64)))))
      (.conj
        (.neg (.all 3 (.neg (.conj (.mem 3 0) (twoF 3 65 66 67 68 69 70 71 72 73)))))
        (.conj
          (.neg (.all 4 (.neg (.conj (.mem 4 0) (threeG 4)))))
          (.conj
            (.neg (.all 5 (.neg (.conj (.mem 5 0) (fourF 5)))))
            (.all 6 (.neg (.conj (.mem 6 0)
              (.conj (.neg (zF 6 74))
                (.conj (.neg (oneF 6 75 76))
                  (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
                    (.conj (.neg (threeG 6))
                      (.neg (fourF 6)))))))))))))

/-- `φ₅` holds of `x` exactly when `x` has a 0-member, a 1-member, a 2-member, a
3-member, a 4-member, and every member is 0, 1, 2, 3 or 4 — i.e. `x` is
extensionally `{0, 1, 2, 3, 4} = 5`. -/
theorem phi5_iff (e : Env) :
    Sat e phi5 ↔
      ( (∃ a, a ∈ (e 0).elems ∧ IsZero a)
        ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
        ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
        ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
        ∧ (∃ p, p ∈ (e 0).elems ∧ IsFour p)
        ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c)) ) := by
  have hz : ∀ val, Sat (Env.update e 1 val) (zF 1 62) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e 1 val) 1 62 (by decide)
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e 2 val) (oneF 2 63 64) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e 2 val) 2 63 64 (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have ht2 : ∀ val, Sat (Env.update e 3 val) (twoF 3 65 66 67 68 69 70 71 72 73) ↔ IsTwo val :=
    fun val => by
      have h := twoF_iff (Env.update e 3 val) 3 65 66 67 68 69 70 71 72 73
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
  have ht3 : ∀ val, Sat (Env.update e 4 val) (threeG 4) ↔ IsThree val := fun val => by
    have h := threeG_iff (Env.update e 4 val) 4 (by decide)
    rwa [Env.update_same] at h
  have ht4 : ∀ val, Sat (Env.update e 5 val) (fourF 5) ↔ IsFour val := fun val => by
    have h := fourF_iff (Env.update e 5 val) 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have hE0 := exists_member_iff e 0 1 (zF 1 62) IsZero (by decide) hz
  have hE1 := exists_member_iff e 0 2 (oneF 2 63 64) IsOne (by decide) hoo
  have hE2 := exists_member_iff e 0 3 (twoF 3 65 66 67 68 69 70 71 72 73) IsTwo (by decide) ht2
  have hE3 := exists_member_iff e 0 4 (threeG 4) IsThree (by decide) ht3
  have hE4 := exists_member_iff e 0 5 (fourF 5) IsFour (by decide) ht4
  have hB : ∀ val, Sat (Env.update e 6 val)
      (.conj (.neg (zF 6 74))
        (.conj (.neg (oneF 6 75 76))
          (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
            (.conj (.neg (threeG 6)) (.neg (fourF 6))))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val) := by
    intro val
    have hz6 : Sat (Env.update e 6 val) (zF 6 74) ↔ IsZero val := by
      have h := zF_iff (Env.update e 6 val) 6 74 (by decide)
      rwa [Env.update_same] at h
    have ho6 : Sat (Env.update e 6 val) (oneF 6 75 76) ↔ IsOne val := by
      have h := oneF_iff (Env.update e 6 val) 6 75 76 (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht6 : Sat (Env.update e 6 val) (twoF 6 77 78 79 80 81 82 83 84 85) ↔ IsTwo val := by
      have h := twoF_iff (Env.update e 6 val) 6 77 78 79 80 81 82 83 84 85
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht36 : Sat (Env.update e 6 val) (threeG 6) ↔ IsThree val := by
      have h := threeG_iff (Env.update e 6 val) 6 (by decide)
      rwa [Env.update_same] at h
    have ht46 : Sat (Env.update e 6 val) (fourF 6) ↔ IsFour val := by
      have h := fourF_iff (Env.update e 6 val) 6 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz6, ho6, ht6, ht36, ht46]
  have hU := forall_member_not_bad e 0 6
    (.conj (.neg (zF 6 74))
      (.conj (.neg (oneF 6 75 76))
        (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
          (.conj (.neg (threeG 6)) (.neg (fourF 6))))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val) (by decide) hB
  have hsplit : Sat e phi5
      ↔ Sat e (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 62)))))
        ∧ (Sat e (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 63 64)))))
           ∧ (Sat e (.neg (.all 3 (.neg (.conj (.mem 3 0)
               (twoF 3 65 66 67 68 69 70 71 72 73)))))
              ∧ (Sat e (.neg (.all 4 (.neg (.conj (.mem 4 0) (threeG 4)))))
                 ∧ (Sat e (.neg (.all 5 (.neg (.conj (.mem 5 0) (fourF 5)))))
                    ∧ Sat e (.all 6 (.neg (.conj (.mem 6 0)
                        (.conj (.neg (zF 6 74))
                          (.conj (.neg (oneF 6 75 76))
                            (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
                              (.conj (.neg (threeG 6))
                                (.neg (fourF 6))))))))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hE3, hE4, hU]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, hu⟩
    refine ⟨h0, h1, h2, h3, h4, ?_⟩
    intro m hm
    rcases Classical.em (IsZero m) with hzm | hzm
    · exact Or.inl hzm
    · rcases Classical.em (IsOne m) with hom | hom
      · exact Or.inr (Or.inl hom)
      · rcases Classical.em (IsTwo m) with htm | htm
        · exact Or.inr (Or.inr (Or.inl htm))
        · rcases Classical.em (IsThree m) with h3m | h3m
          · exact Or.inr (Or.inr (Or.inr (Or.inl h3m)))
          · rcases Classical.em (IsFour m) with h4m | h4m
            · exact Or.inr (Or.inr (Or.inr (Or.inr h4m)))
            · exact absurd ⟨hzm, hom, htm, h3m, h4m⟩ (hu m hm)
  · rintro ⟨h0, h1, h2, h3, h4, hu⟩
    refine ⟨h0, h1, h2, h3, h4, ?_⟩
    intro m hm
    rintro ⟨hnz, hno, hnt, hn3, hn4⟩
    rcases hu m hm with hzm | hom | htm | h3m | h4m
    · exact hnz hzm
    · exact hno hom
    · exact hnt htm
    · exact hn3 h3m
    · exact hn4 h4m

/-- Existence: the canonical `5 = {0, 1, 2, 3, 4}` satisfies `φ₅`. -/
theorem phi5_holds_of_five : Sat (fun _ => five) phi5 := by
  rw [phi5_iff]
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ⟨two, ?_, isTwo_two⟩,
    ⟨three, ?_, isThree_three⟩, ⟨four, ?_, isFour_four⟩, ?_⟩
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · intro m hm
    simp only [five, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl isOne_one)
    · subst h; exact Or.inr (Or.inr (Or.inl isTwo_two))
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl isThree_three)))
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr isFour_four)))

/-- Naming: any solution has exactly the member-classification of `5` — a
0-member, a 1-member, a 2-member, a 3-member, a 4-member, and no other kind of
member. -/
theorem phi5_names_five (e : Env) (h : Sat e phi5) :
    (∃ a, a ∈ (e 0).elems ∧ IsZero a)
    ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
    ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
    ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
    ∧ (∃ p, p ∈ (e 0).elems ∧ IsFour p)
    ∧ (∀ c, c ∈ (e 0).elems → (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c)) :=
  (phi5_iff e).mp h

/-! ### Class disjointness (the new k = 5 cases). -/

/-- The 0-class and the 4-class are disjoint: nothing is both. A 4-set has a
member, but `0 = ∅` has none. -/
theorem not_isZero_and_isFour (a : HF) : ¬ (IsZero a ∧ IsFour a) := by
  rintro ⟨h0, hfour⟩
  have h0' : a = HF.empty := h0
  obtain ⟨⟨z, hz, _⟩, _, _, _, _⟩ := hfour
  rw [h0'] at hz
  simp [HF.empty, HF.elems] at hz

/-- The 1-class and the 4-class are disjoint: nothing is both. A member of a
1-set is empty, but a 4-set has a (nonempty) 2-member. -/
theorem not_isOne_and_isFour (a : HF) : ¬ (IsOne a ∧ IsFour a) := by
  rintro ⟨hone, hfour⟩
  obtain ⟨_, hallempty⟩ := hone
  obtain ⟨_, _, ⟨w, hw, hwTwo⟩, _, _⟩ := hfour
  have heq : w = HF.empty := hallempty w hw
  rw [heq] at hwTwo
  obtain ⟨⟨z, hz, _⟩, _, _⟩ := hwTwo
  simp [HF.empty, HF.elems] at hz

/-- The 2-class and the 4-class are disjoint: nothing is both. A 2-set's members
are only 0s and 1s, but a 4-set has a 3-member, and `3` is neither 0 nor 1. -/
theorem not_isTwo_and_isFour (a : HF) : ¬ (IsTwo a ∧ IsFour a) := by
  rintro ⟨htwo, hfour⟩
  obtain ⟨_, _, htwoAll⟩ := htwo
  obtain ⟨_, _, _, ⟨w, hw, hwThree⟩, _⟩ := hfour
  rcases htwoAll w hw with hzw | how
  · exact not_isZero_and_isThree w ⟨hzw, hwThree⟩
  · exact not_isOne_and_isThree w ⟨how, hwThree⟩

/-- The 3-class and the 4-class are disjoint: nothing is both. A 3-set's members
are only 0s, 1s and 2s, but a 4-set has a 3-member, and `3` is none of those. -/
theorem not_isThree_and_isFour (a : HF) : ¬ (IsThree a ∧ IsFour a) := by
  rintro ⟨hthree, hfour⟩
  obtain ⟨_, _, _, hthreeAll⟩ := hthree
  obtain ⟨_, _, _, ⟨w, hw, hwThree⟩, _⟩ := hfour
  rcases hthreeAll w hw with hzw | how | htw
  · exact not_isZero_and_isThree w ⟨hzw, hwThree⟩
  · exact not_isOne_and_isThree w ⟨how, hwThree⟩
  · exact not_isTwo_and_isThree w ⟨htw, hwThree⟩

/-- Same 0/1/2/3/4 extensional class. On φ₅-solutions (whose members are only 0s,
1s, 2s, 3s and 4s) this is genuine extensional equality. -/
def ClassEq5 (z m : HF) : Prop :=
  (IsZero z ∧ IsZero m) ∨ (IsOne z ∧ IsOne m) ∨ (IsTwo z ∧ IsTwo m)
    ∨ (IsThree z ∧ IsThree m) ∨ (IsFour z ∧ IsFour m)

/-- Uniqueness up to extensional equality: any two solutions of `φ₅` have exactly
the same members up to `ClassEq5`. With the ten disjointness lemmas this pins
every solution to the extensional set `{0, 1, 2, 3, 4} = 5`. -/
theorem phi5_unique (e e' : Env) (h : Sat e phi5) (h' : Sat e' phi5) :
    ∀ z, (∃ m, m ∈ (e 0).elems ∧ ClassEq5 z m)
        ↔ (∃ m, m ∈ (e' 0).elems ∧ ClassEq5 z m) := by
  obtain ⟨⟨a, ha, haz⟩, ⟨b, hb, hbo⟩, ⟨d, hd, hdt⟩, ⟨g, hg, hg3⟩, ⟨p, hp, hp4⟩, _⟩ :=
    (phi5_iff e).mp h
  obtain ⟨⟨a', ha', haz'⟩, ⟨b', hb', hbo'⟩, ⟨d', hd', hdt'⟩, ⟨g', hg', hg3'⟩, ⟨p', hp', hp4'⟩, _⟩ :=
    (phi5_iff e').mp h'
  intro z
  constructor
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩ | ⟨hz4, _⟩
    · exact ⟨a', ha', Or.inl ⟨hzz, haz'⟩⟩
    · exact ⟨b', hb', Or.inr (Or.inl ⟨hzo, hbo'⟩)⟩
    · exact ⟨d', hd', Or.inr (Or.inr (Or.inl ⟨hzt, hdt'⟩))⟩
    · exact ⟨g', hg', Or.inr (Or.inr (Or.inr (Or.inl ⟨hz3, hg3'⟩)))⟩
    · exact ⟨p', hp', Or.inr (Or.inr (Or.inr (Or.inr ⟨hz4, hp4'⟩)))⟩
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩ | ⟨hz4, _⟩
    · exact ⟨a, ha, Or.inl ⟨hzz, haz⟩⟩
    · exact ⟨b, hb, Or.inr (Or.inl ⟨hzo, hbo⟩)⟩
    · exact ⟨d, hd, Or.inr (Or.inr (Or.inl ⟨hzt, hdt⟩))⟩
    · exact ⟨g, hg, Or.inr (Or.inr (Or.inr (Or.inl ⟨hz3, hg3⟩)))⟩
    · exact ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr ⟨hz4, hp4⟩)))⟩

end Rayo
