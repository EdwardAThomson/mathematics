/-
`Rayo.K6` — the k = 6 naming-cost item.

We name the von-Neumann natural `6 = {0, 1, 2, 3, 4, 5}` with a first-order
formula over `∈` (and `=`), count its symbols under the frozen convention
(`notes/convention-notes.md`), and prove mechanically that its solutions are,
up to extensional equality, exactly `6`.

## The formula (convention form, `x = v₀`)

φ₆ is built *recursively* from φ₀ ("is 0"), …, φ₅ ("is 5"):

    φ₆(x) := (∃ a ((a ∈ x) ∧ φ₀(a)))                         -- x has a 0-member
           ∧ (∃ b ((b ∈ x) ∧ φ₁(b)))                         -- x has a 1-member
           ∧ (∃ d ((d ∈ x) ∧ φ₂(d)))                         -- x has a 2-member
           ∧ (∃ g ((g ∈ x) ∧ φ₃(g)))                         -- x has a 3-member
           ∧ (∃ p ((p ∈ x) ∧ φ₄(p)))                         -- x has a 4-member
           ∧ (∃ q ((q ∈ x) ∧ φ₅(q)))                         -- x has a 5-member
           ∧ (∀ c ¬((c ∈ x) ∧ (¬φ₀(c) ∧ (¬φ₁(c) ∧ (¬φ₂(c) ∧
                    (¬φ₃(c) ∧ (¬φ₄(c) ∧ ¬φ₅(c))))))))
                                                             -- members are 0,1,2,3,4 or 5

with the sub-predicates φ₀, …, φ₅ ("is 0/1/2/3/4/5") as in K0–K5. The
"0/1/2/3/4/5" clause is written directly in the primitive alphabet as a De
Morgan negation ("no member is none-of-0/1/2/3/4/5"), so no `or`/`implies`
abbreviation expansion is needed. `∃` is a convention primitive (one symbol); in
the `Formula` datatype it has no constructor and is represented by the standard
`¬∀¬` expansion (a mechanization-only choice that does not change the convention
count, exactly as in `Rayo.K1`–`Rayo.K5`).

## Symbol count n₆ = 11128

Counted under `notes/convention-notes.md` §2/§4 with the same fully-parenthesized
discipline as φ₀ (10), φ₁ (30), φ₂ (128), φ₃ (403), φ₄ (1228) and φ₅ (3703):
atom = 3; `¬φ = |φ|+3`; `(φ ∧ ψ) = |φ|+|ψ|+3`; `Q v (φ) = |φ|+4` (`∃`/`∀`
primitive, one symbol each; each variable occurrence one). Each
`E_i = ∃v ((v∈x) ∧ φ_i(v)) = |φ_i|+10`.

    φ₀(t)                                            = 10   (as in K0)
    φ₁(t)                                            = 30   (as in K1)
    φ₂(t)                                            = 128  (as in K2)
    φ₃(t)                                            = 403  (as in K3)
    φ₄(t)                                            = 1228 (as in K4)
    φ₅(t)                                            = 3703 (as in K5)
    E0 = ∃a ((a∈x) ∧ φ₀(a))       10+10              = 20
    E1 = ∃b ((b∈x) ∧ φ₁(b))       30+10              = 40
    E2 = ∃d ((d∈x) ∧ φ₂(d))       128+10             = 138
    E3 = ∃g ((g∈x) ∧ φ₃(g))       403+10             = 413
    E4 = ∃p ((p∈x) ∧ φ₄(p))       1228+10            = 1238
    E5 = ∃q ((q∈x) ∧ φ₅(q))       3703+10            = 3713
    U  = ∀c ¬((c∈x) ∧ (¬φ₀ ∧ (¬φ₁ ∧ (¬φ₂ ∧ (¬φ₃ ∧ (¬φ₄ ∧ ¬φ₅))))))
         ¬φ₀=13, ¬φ₁=33, ¬φ₂=131, ¬φ₃=406, ¬φ₄=1231, ¬φ₅=3706,
         (¬φ₄∧¬φ₅)=1231+3706+3=4940, (¬φ₃∧·)=406+4940+3=5349,
         (¬φ₂∧·)=131+5349+3=5483, (¬φ₁∧·)=33+5483+3=5519,
         (¬φ₀∧·)=13+5519+3=5535, (c∈x ∧ ·)=3+5535+3=5541,
         ¬·=5544, ∀c(·)=5544+4                       = 5548
    φ₆ = (E0 ∧ (E1 ∧ (E2 ∧ (E3 ∧ (E4 ∧ (E5 ∧ U))))))
         20+40+138+413+1238+3713+5548 + 6·3 = 11110 + 18 = 11128

n₆ = 11128. This is the cost of *this* recursive construction; it is an upper
bound on the true minimum, not a claim of minimality. Flagged per
`METHODOLOGY.md` C1.

## Extensionality (the k≥2 subtlety)

The HF model of `Rayo.Satisfaction` is non-extensional (a set is a *list*). As
for k=2,…,5, a member of a solution may be structurally different from the
canonical `0`/…/`5` yet extensionally equal, so strict structural uniqueness is
false and uniqueness holds only *up to extensional equality*. We state it with
`ClassEq6` (same 0/1/2/3/4/5 extensional class): `phi6_unique` shows any two
solutions have the same members up to `ClassEq6`, and the fifteen
`not_is…_and_is…` lemmas (ten reused from `Rayo.K3`/`K4`/`K5`, five new here)
show the classes are pairwise disjoint, so a solution is extensionally
`{0,1,2,3,4,5} = 6`.

## Mechanization note on bound variables

The member quantifier of φ₆ is variable `6`. `threeG` (fixed block `7..34`,
container `< 7`) and `fourF` (container `∉ {3,4,35,37,40}`) both apply to `6`, so
no new "is 3"/"is 4" predicate is needed. The new "is 5" predicate `fiveF` uses a
fresh high block `100..127` for its own witnesses, reusing the low variables `5`
and `2` for the two slots that must host `threeG`/`fourF` tests (both `< 7` and
`∉ {3,4,35,37,40}`), and is only ever applied to variables `6` and `7`. Choosing
fixed bound-variable indices is a mechanization-only convenience and does not
affect the convention symbol count (variable identity is free,
`notes/convention-notes.md` §4).

## Finding (recorded here, per this item)

- k = 6
- formula: `phi6` below (convention form in the header)
- symbol count n₆ = 11128 (derivation above)
- Lean proof reference: `phi6_iff` (characterisation), `phi6_holds_of_six`
  (existence), `phi6_names_six` (member classification) and `phi6_unique`
  (uniqueness up to `ClassEq6`) in this file. The proofs have no proof holes.
-/

import Rayo.K5

namespace Rayo

/-- von-Neumann `6 = {0, 1, 2, 3, 4, 5}`, as an HF term. -/
def six : HF := HF.mk [HF.empty, one, two, three, four, five]

/-- Extensional predicate "is (extensionally) `5 = {0, 1, 2, 3, 4}`": has a
0-member, a 1-member, a 2-member, a 3-member, a 4-member, and every member is
0, 1, 2, 3 or 4. This is exactly `Rayo.K5`'s φ₅ characterisation, lifted to a
standalone predicate. -/
def IsFive (a : HF) : Prop :=
  (∃ z, z ∈ a.elems ∧ IsZero z)
  ∧ (∃ o, o ∈ a.elems ∧ IsOne o)
  ∧ (∃ w, w ∈ a.elems ∧ IsTwo w)
  ∧ (∃ v, v ∈ a.elems ∧ IsThree v)
  ∧ (∃ u, u ∈ a.elems ∧ IsFour u)
  ∧ (∀ w, w ∈ a.elems → IsZero w ∨ IsOne w ∨ IsTwo w ∨ IsThree w ∨ IsFour w)

/-! ### The "is 5" sub-formula `fiveF(t)` on a container variable `t`.

`fiveF`'s own witnesses use a fresh high block (`100..127`), its "is 3"
sub-predicate is `threeG` applied to the low variable `5` (`< 7`), its "is 4"
sub-predicate is `fourF` applied to `115` and to the low variable `2`
(`∉ {3,4,35,37,40}`), and the single hypotheses `t ≠ 2, 5, 100, 102, 105, 115`
discharge every "container ≠ bound variable" side condition. In φ₆, `fiveF` is
applied only to variables `6` and `7`, for which those inequalities hold. -/

/-- `fiveF t` — "`v_t` is extensionally `5 = {0, 1, 2, 3, 4}`": has a 0-member, a
1-member, a 2-member, a 3-member, a 4-member, and every member is 0, 1, 2, 3
or 4. -/
def fiveF (t : Nat) : Formula :=
  .conj
    (.neg (.all 100 (.neg (.conj (.mem 100 t) (zF 100 101)))))
    (.conj
      (.neg (.all 102 (.neg (.conj (.mem 102 t) (oneF 102 103 104)))))
      (.conj
        (.neg (.all 105 (.neg (.conj (.mem 105 t) (twoF 105 106 107 108 109 110 111 112 113 114)))))
        (.conj
          (.neg (.all 5 (.neg (.conj (.mem 5 t) (threeG 5)))))
          (.conj
            (.neg (.all 115 (.neg (.conj (.mem 115 t) (fourF 115)))))
            (.all 2 (.neg (.conj (.mem 2 t)
              (.conj (.neg (zF 2 116))
                (.conj (.neg (oneF 2 117 118))
                  (.conj (.neg (twoF 2 119 120 121 122 123 124 125 126 127))
                    (.conj (.neg (threeG 2))
                      (.neg (fourF 2)))))))))))))

theorem fiveF_iff (e : Env) (t : Nat)
    (h2 : t ≠ 2) (h5 : t ≠ 5) (h100 : t ≠ 100) (h102 : t ≠ 102)
    (h105 : t ≠ 105) (h115 : t ≠ 115) :
    Sat e (fiveF t) ↔ IsFive (e t) := by
  have hz : ∀ val, Sat (Env.update e 100 val) (zF 100 101) ↔ IsZero val := fun val => by
    have h := zF_iff (Env.update e 100 val) 100 101 (by decide)
    rwa [Env.update_same] at h
  have hoo : ∀ val, Sat (Env.update e 102 val) (oneF 102 103 104) ↔ IsOne val := fun val => by
    have h := oneF_iff (Env.update e 102 val) 102 103 104 (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have ht2 : ∀ val, Sat (Env.update e 105 val) (twoF 105 106 107 108 109 110 111 112 113 114) ↔ IsTwo val :=
    fun val => by
      have h := twoF_iff (Env.update e 105 val) 105 106 107 108 109 110 111 112 113 114
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
  have ht3 : ∀ val, Sat (Env.update e 5 val) (threeG 5) ↔ IsThree val := fun val => by
    have h := threeG_iff (Env.update e 5 val) 5 (by decide)
    rwa [Env.update_same] at h
  have ht4 : ∀ val, Sat (Env.update e 115 val) (fourF 115) ↔ IsFour val := fun val => by
    have h := fourF_iff (Env.update e 115 val) 115 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have hE0 := exists_member_iff e t 100 (zF 100 101) IsZero h100 hz
  have hE1 := exists_member_iff e t 102 (oneF 102 103 104) IsOne h102 hoo
  have hE2 := exists_member_iff e t 105 (twoF 105 106 107 108 109 110 111 112 113 114) IsTwo h105 ht2
  have hE3 := exists_member_iff e t 5 (threeG 5) IsThree h5 ht3
  have hE4 := exists_member_iff e t 115 (fourF 115) IsFour h115 ht4
  have hB : ∀ val, Sat (Env.update e 2 val)
      (.conj (.neg (zF 2 116))
        (.conj (.neg (oneF 2 117 118))
          (.conj (.neg (twoF 2 119 120 121 122 123 124 125 126 127))
            (.conj (.neg (threeG 2)) (.neg (fourF 2))))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val) := by
    intro val
    have hz2 : Sat (Env.update e 2 val) (zF 2 116) ↔ IsZero val := by
      have h := zF_iff (Env.update e 2 val) 2 116 (by decide)
      rwa [Env.update_same] at h
    have ho2 : Sat (Env.update e 2 val) (oneF 2 117 118) ↔ IsOne val := by
      have h := oneF_iff (Env.update e 2 val) 2 117 118 (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht2' : Sat (Env.update e 2 val) (twoF 2 119 120 121 122 123 124 125 126 127) ↔ IsTwo val := by
      have h := twoF_iff (Env.update e 2 val) 2 119 120 121 122 123 124 125 126 127
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    have ht32 : Sat (Env.update e 2 val) (threeG 2) ↔ IsThree val := by
      have h := threeG_iff (Env.update e 2 val) 2 (by decide)
      rwa [Env.update_same] at h
    have ht42 : Sat (Env.update e 2 val) (fourF 2) ↔ IsFour val := by
      have h := fourF_iff (Env.update e 2 val) 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz2, ho2, ht2', ht32, ht42]
  have hU := forall_member_not_bad e t 2
    (.conj (.neg (zF 2 116))
      (.conj (.neg (oneF 2 117 118))
        (.conj (.neg (twoF 2 119 120 121 122 123 124 125 126 127))
          (.conj (.neg (threeG 2)) (.neg (fourF 2))))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val) h2 hB
  have hsplit : Sat e (fiveF t)
      ↔ Sat e (.neg (.all 100 (.neg (.conj (.mem 100 t) (zF 100 101)))))
        ∧ (Sat e (.neg (.all 102 (.neg (.conj (.mem 102 t) (oneF 102 103 104)))))
           ∧ (Sat e (.neg (.all 105 (.neg (.conj (.mem 105 t)
               (twoF 105 106 107 108 109 110 111 112 113 114)))))
              ∧ (Sat e (.neg (.all 5 (.neg (.conj (.mem 5 t) (threeG 5)))))
                 ∧ (Sat e (.neg (.all 115 (.neg (.conj (.mem 115 t) (fourF 115)))))
                    ∧ Sat e (.all 2 (.neg (.conj (.mem 2 t)
                        (.conj (.neg (zF 2 116))
                          (.conj (.neg (oneF 2 117 118))
                            (.conj (.neg (twoF 2 119 120 121 122 123 124 125 126 127))
                              (.conj (.neg (threeG 2))
                                (.neg (fourF 2))))))))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hE3, hE4, hU]
  unfold IsFive
  constructor
  · rintro ⟨h0, h1, h2', h3, h4, hu⟩
    refine ⟨h0, h1, h2', h3, h4, ?_⟩
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
  · rintro ⟨h0, h1, h2', h3, h4, hu⟩
    refine ⟨h0, h1, h2', h3, h4, ?_⟩
    intro m hm
    rintro ⟨hnz, hno, hnt, hn3, hn4⟩
    rcases hu m hm with hzm | hom | htm | h3m | h4m
    · exact hnz hzm
    · exact hno hom
    · exact hnt htm
    · exact hn3 h3m
    · exact hn4 h4m

/-- The canonical `5 = {0,1,2,3,4}` is (extensionally) `5`. -/
theorem isFive_five : IsFive five := by
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ⟨two, ?_, isTwo_two⟩,
    ⟨three, ?_, isThree_three⟩, ⟨four, ?_, isFour_four⟩, ?_⟩
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · simp [five, HF.elems]
  · intro w hw
    simp only [five, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl isOne_one)
    · subst h; exact Or.inr (Or.inr (Or.inl isTwo_two))
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl isThree_three)))
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr isFour_four)))

/-! ### The k = 6 formula and its characterisation. -/

/-- The k = 6 naming formula (see the file header for the convention form).
`x = v₀`; witnesses `a = v₁` (0-member), `b = v₂` (1-member), `d = v₃`
(2-member), `g = v₄` (3-member), `p = v₅` (4-member), `q = v₇` (5-member),
member-quantifier `c = v₆`; the `zF`/`oneF`/`twoF` sub-predicates use fresh bound
variables `62..85`, `threeG` uses its fixed block `7..34`, `fourF` its own
blocks, and `fiveF` its block `100..127`. -/
def phi6 : Formula :=
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
            (.conj
              (.neg (.all 7 (.neg (.conj (.mem 7 0) (fiveF 7)))))
              (.all 6 (.neg (.conj (.mem 6 0)
                (.conj (.neg (zF 6 74))
                  (.conj (.neg (oneF 6 75 76))
                    (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
                      (.conj (.neg (threeG 6))
                        (.conj (.neg (fourF 6))
                          (.neg (fiveF 6)))))))))))))))

/-- `φ₆` holds of `x` exactly when `x` has a 0-member, a 1-member, a 2-member, a
3-member, a 4-member, a 5-member, and every member is 0, 1, 2, 3, 4 or 5 — i.e.
`x` is extensionally `{0, 1, 2, 3, 4, 5} = 6`. -/
theorem phi6_iff (e : Env) :
    Sat e phi6 ↔
      ( (∃ a, a ∈ (e 0).elems ∧ IsZero a)
        ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
        ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
        ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
        ∧ (∃ p, p ∈ (e 0).elems ∧ IsFour p)
        ∧ (∃ q, q ∈ (e 0).elems ∧ IsFive q)
        ∧ (∀ c, c ∈ (e 0).elems →
            (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c ∨ IsFive c)) ) := by
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
  have ht5 : ∀ val, Sat (Env.update e 7 val) (fiveF 7) ↔ IsFive val := fun val => by
    have h := fiveF_iff (Env.update e 7 val) 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [Env.update_same] at h
  have hE0 := exists_member_iff e 0 1 (zF 1 62) IsZero (by decide) hz
  have hE1 := exists_member_iff e 0 2 (oneF 2 63 64) IsOne (by decide) hoo
  have hE2 := exists_member_iff e 0 3 (twoF 3 65 66 67 68 69 70 71 72 73) IsTwo (by decide) ht2
  have hE3 := exists_member_iff e 0 4 (threeG 4) IsThree (by decide) ht3
  have hE4 := exists_member_iff e 0 5 (fourF 5) IsFour (by decide) ht4
  have hE5 := exists_member_iff e 0 7 (fiveF 7) IsFive (by decide) ht5
  have hB : ∀ val, Sat (Env.update e 6 val)
      (.conj (.neg (zF 6 74))
        (.conj (.neg (oneF 6 75 76))
          (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
            (.conj (.neg (threeG 6))
              (.conj (.neg (fourF 6)) (.neg (fiveF 6)))))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val ∧ ¬ IsFive val) := by
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
    have ht56 : Sat (Env.update e 6 val) (fiveF 6) ↔ IsFive val := by
      have h := fiveF_iff (Env.update e 6 val) 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [Env.update_same] at h
    simp only [Sat, hz6, ho6, ht6, ht36, ht46, ht56]
  have hU := forall_member_not_bad e 0 6
    (.conj (.neg (zF 6 74))
      (.conj (.neg (oneF 6 75 76))
        (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
          (.conj (.neg (threeG 6))
            (.conj (.neg (fourF 6)) (.neg (fiveF 6)))))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val ∧ ¬ IsFive val)
    (by decide) hB
  have hsplit : Sat e phi6
      ↔ Sat e (.neg (.all 1 (.neg (.conj (.mem 1 0) (zF 1 62)))))
        ∧ (Sat e (.neg (.all 2 (.neg (.conj (.mem 2 0) (oneF 2 63 64)))))
           ∧ (Sat e (.neg (.all 3 (.neg (.conj (.mem 3 0)
               (twoF 3 65 66 67 68 69 70 71 72 73)))))
              ∧ (Sat e (.neg (.all 4 (.neg (.conj (.mem 4 0) (threeG 4)))))
                 ∧ (Sat e (.neg (.all 5 (.neg (.conj (.mem 5 0) (fourF 5)))))
                    ∧ (Sat e (.neg (.all 7 (.neg (.conj (.mem 7 0) (fiveF 7)))))
                       ∧ Sat e (.all 6 (.neg (.conj (.mem 6 0)
                           (.conj (.neg (zF 6 74))
                             (.conj (.neg (oneF 6 75 76))
                               (.conj (.neg (twoF 6 77 78 79 80 81 82 83 84 85))
                                 (.conj (.neg (threeG 6))
                                   (.conj (.neg (fourF 6))
                                     (.neg (fiveF 6))))))))))))))) := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hE3, hE4, hE5, hU]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, hu⟩
    refine ⟨h0, h1, h2, h3, h4, h5, ?_⟩
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
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4m))))
            · rcases Classical.em (IsFive m) with h5m | h5m
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h5m))))
              · exact absurd ⟨hzm, hom, htm, h3m, h4m, h5m⟩ (hu m hm)
  · rintro ⟨h0, h1, h2, h3, h4, h5, hu⟩
    refine ⟨h0, h1, h2, h3, h4, h5, ?_⟩
    intro m hm
    rintro ⟨hnz, hno, hnt, hn3, hn4, hn5⟩
    rcases hu m hm with hzm | hom | htm | h3m | h4m | h5m
    · exact hnz hzm
    · exact hno hom
    · exact hnt htm
    · exact hn3 h3m
    · exact hn4 h4m
    · exact hn5 h5m

/-- Existence: the canonical `6 = {0, 1, 2, 3, 4, 5}` satisfies `φ₆`. -/
theorem phi6_holds_of_six : Sat (fun _ => six) phi6 := by
  rw [phi6_iff]
  refine ⟨⟨HF.empty, ?_, rfl⟩, ⟨one, ?_, isOne_one⟩, ⟨two, ?_, isTwo_two⟩,
    ⟨three, ?_, isThree_three⟩, ⟨four, ?_, isFour_four⟩, ⟨five, ?_, isFive_five⟩, ?_⟩
  · simp [six, HF.elems]
  · simp [six, HF.elems]
  · simp [six, HF.elems]
  · simp [six, HF.elems]
  · simp [six, HF.elems]
  · simp [six, HF.elems]
  · intro m hm
    simp only [six, HF.elems, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr (Or.inl isOne_one)
    · subst h; exact Or.inr (Or.inr (Or.inl isTwo_two))
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl isThree_three)))
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl isFour_four))))
    · subst h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr isFive_five))))

/-- Naming: any solution has exactly the member-classification of `6` — a
0-member, a 1-member, a 2-member, a 3-member, a 4-member, a 5-member, and no
other kind of member. -/
theorem phi6_names_six (e : Env) (h : Sat e phi6) :
    (∃ a, a ∈ (e 0).elems ∧ IsZero a)
    ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
    ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
    ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
    ∧ (∃ p, p ∈ (e 0).elems ∧ IsFour p)
    ∧ (∃ q, q ∈ (e 0).elems ∧ IsFive q)
    ∧ (∀ c, c ∈ (e 0).elems →
        (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c ∨ IsFive c)) :=
  (phi6_iff e).mp h

/-! ### Class disjointness (the new k = 6 cases). -/

/-- The 0-class and the 5-class are disjoint: nothing is both. A 5-set has a
member, but `0 = ∅` has none. -/
theorem not_isZero_and_isFive (a : HF) : ¬ (IsZero a ∧ IsFive a) := by
  rintro ⟨h0, hfive⟩
  have h0' : a = HF.empty := h0
  obtain ⟨⟨z, hz, _⟩, _, _, _, _, _⟩ := hfive
  rw [h0'] at hz
  simp [HF.empty, HF.elems] at hz

/-- The 1-class and the 5-class are disjoint: nothing is both. A member of a
1-set is empty, but a 5-set has a (nonempty) 2-member. -/
theorem not_isOne_and_isFive (a : HF) : ¬ (IsOne a ∧ IsFive a) := by
  rintro ⟨hone, hfive⟩
  obtain ⟨_, hallempty⟩ := hone
  obtain ⟨_, _, ⟨w, hw, hwTwo⟩, _, _, _⟩ := hfive
  have heq : w = HF.empty := hallempty w hw
  rw [heq] at hwTwo
  obtain ⟨⟨z, hz, _⟩, _, _⟩ := hwTwo
  simp [HF.empty, HF.elems] at hz

/-- The 2-class and the 5-class are disjoint: nothing is both. A 2-set's members
are only 0s and 1s, but a 5-set has a 3-member, and `3` is neither 0 nor 1. -/
theorem not_isTwo_and_isFive (a : HF) : ¬ (IsTwo a ∧ IsFive a) := by
  rintro ⟨htwo, hfive⟩
  obtain ⟨_, _, htwoAll⟩ := htwo
  obtain ⟨_, _, _, ⟨w, hw, hwThree⟩, _, _⟩ := hfive
  rcases htwoAll w hw with hzw | how
  · exact not_isZero_and_isThree w ⟨hzw, hwThree⟩
  · exact not_isOne_and_isThree w ⟨how, hwThree⟩

/-- The 3-class and the 5-class are disjoint: nothing is both. A 3-set's members
are only 0s, 1s and 2s, but a 5-set has a 3-member, and `3` is none of those. -/
theorem not_isThree_and_isFive (a : HF) : ¬ (IsThree a ∧ IsFive a) := by
  rintro ⟨hthree, hfive⟩
  obtain ⟨_, _, _, hthreeAll⟩ := hthree
  obtain ⟨_, _, _, ⟨w, hw, hwThree⟩, _, _⟩ := hfive
  rcases hthreeAll w hw with hzw | how | htw
  · exact not_isZero_and_isThree w ⟨hzw, hwThree⟩
  · exact not_isOne_and_isThree w ⟨how, hwThree⟩
  · exact not_isTwo_and_isThree w ⟨htw, hwThree⟩

/-- The 4-class and the 5-class are disjoint: nothing is both. A 4-set's members
are only 0s, 1s, 2s and 3s, but a 5-set has a 4-member, and `4` is none of
those. -/
theorem not_isFour_and_isFive (a : HF) : ¬ (IsFour a ∧ IsFive a) := by
  rintro ⟨hfour, hfive⟩
  obtain ⟨_, _, _, _, hfourAll⟩ := hfour
  obtain ⟨_, _, _, _, ⟨w, hw, hwFour⟩, _⟩ := hfive
  rcases hfourAll w hw with hzw | how | htw | h3w
  · exact not_isZero_and_isFour w ⟨hzw, hwFour⟩
  · exact not_isOne_and_isFour w ⟨how, hwFour⟩
  · exact not_isTwo_and_isFour w ⟨htw, hwFour⟩
  · exact not_isThree_and_isFour w ⟨h3w, hwFour⟩

/-- Same 0/1/2/3/4/5 extensional class. On φ₆-solutions (whose members are only
0s, 1s, 2s, 3s, 4s and 5s) this is genuine extensional equality. -/
def ClassEq6 (z m : HF) : Prop :=
  (IsZero z ∧ IsZero m) ∨ (IsOne z ∧ IsOne m) ∨ (IsTwo z ∧ IsTwo m)
    ∨ (IsThree z ∧ IsThree m) ∨ (IsFour z ∧ IsFour m) ∨ (IsFive z ∧ IsFive m)

/-- Uniqueness up to extensional equality: any two solutions of `φ₆` have exactly
the same members up to `ClassEq6`. With the fifteen disjointness lemmas this pins
every solution to the extensional set `{0, 1, 2, 3, 4, 5} = 6`. -/
theorem phi6_unique (e e' : Env) (h : Sat e phi6) (h' : Sat e' phi6) :
    ∀ z, (∃ m, m ∈ (e 0).elems ∧ ClassEq6 z m)
        ↔ (∃ m, m ∈ (e' 0).elems ∧ ClassEq6 z m) := by
  obtain ⟨⟨a, ha, haz⟩, ⟨b, hb, hbo⟩, ⟨d, hd, hdt⟩, ⟨g, hg, hg3⟩, ⟨p, hp, hp4⟩, ⟨q, hq, hq5⟩, _⟩ :=
    (phi6_iff e).mp h
  obtain ⟨⟨a', ha', haz'⟩, ⟨b', hb', hbo'⟩, ⟨d', hd', hdt'⟩, ⟨g', hg', hg3'⟩, ⟨p', hp', hp4'⟩,
      ⟨q', hq', hq5'⟩, _⟩ :=
    (phi6_iff e').mp h'
  intro z
  constructor
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩ | ⟨hz4, _⟩ | ⟨hz5, _⟩
    · exact ⟨a', ha', Or.inl ⟨hzz, haz'⟩⟩
    · exact ⟨b', hb', Or.inr (Or.inl ⟨hzo, hbo'⟩)⟩
    · exact ⟨d', hd', Or.inr (Or.inr (Or.inl ⟨hzt, hdt'⟩))⟩
    · exact ⟨g', hg', Or.inr (Or.inr (Or.inr (Or.inl ⟨hz3, hg3'⟩)))⟩
    · exact ⟨p', hp', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz4, hp4'⟩))))⟩
    · exact ⟨q', hq', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz5, hq5'⟩))))⟩
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩ | ⟨hz4, _⟩ | ⟨hz5, _⟩
    · exact ⟨a, ha, Or.inl ⟨hzz, haz⟩⟩
    · exact ⟨b, hb, Or.inr (Or.inl ⟨hzo, hbo⟩)⟩
    · exact ⟨d, hd, Or.inr (Or.inr (Or.inl ⟨hzt, hdt⟩))⟩
    · exact ⟨g, hg, Or.inr (Or.inr (Or.inr (Or.inl ⟨hz3, hg3⟩)))⟩
    · exact ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz4, hp4⟩))))⟩
    · exact ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz5, hq5⟩))))⟩

end Rayo
