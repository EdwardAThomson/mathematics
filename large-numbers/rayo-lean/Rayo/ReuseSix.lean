/-
`Rayo.ReuseSix` — the reuse-based `Program` naming 6, its expansion, and the
proof that expansion is `Sat`-equivalent to `Rayo.K6`'s `phi6`.

## The program

Six definitions, indices `0..5`, each referencing only strictly earlier
ones, exactly mirroring the recursive "E_i / U" shape already visible in
`K2.lean`-`K6.lean` (`x`'s members are exactly the things satisfying
definition `0`, or `1`, ..., or `k-1`, plus a "nothing else qualifies"
exclusion clause) — except every embedded sub-formula is a `ref` (2 symbols)
instead of a full respelling:

* def 0 ("is 0"): `∀ v_inner ¬(v_inner ∈ t)` — no references (φ₀ has no
  sub-structure to reuse), internal variable `1000`.
* def 1 ("is 1"): `(∃ v_u (v_u ∈ t)) ∧ (∀ v_u ∀ v_v ¬((v_u ∈ t) ∧ (v_v ∈
  v_u)))` — no references either (φ₁ does not call φ₀; see `K1.lean`),
  internal variables `1001, 1002`.
* def 2 ("is 2"): references def 0 and def 1. Own block `1010..1012`.
* def 3 ("is 3"): references def 0, 1, 2. Own block `1020..1023`.
* def 4 ("is 4"): references def 0, 1, 2, 3. Own block `1030..1034`.
* def 5 ("is 5"): references def 0, 1, 2, 3, 4. Own block `1040..1045`.
* `final` ("is 6"): references def 0, 1, 2, 3, 4, 5, at `x = v0` (matching
  the existing convention that the one free variable is always `v0`). Own
  block `1050..1056`.

Every block is a fixed, pairwise-disjoint range (`1000..1056`, none
overlapping `v0` or any other block) — see `Reuse.lean`'s header for why
reusing a definition's own internal block across every call site is safe
(each occurrence sits under its own quantifiers).

## Correctness strategy

Definitions 0 and 1 have no `ref`s, so their expansion is *literally* (not
just `Sat`-equivalently) the existing `Rayo.zF`/`Rayo.oneF` formulas already
proved correct by `zF_iff`/`oneF_iff` in `K2.lean`. Definition 2's expansion
is literally `Rayo.twoF` (`K3.lean`) applied at the matching parameter
slots, so `twoF_iff` transfers directly with no new proof. From definition 3
onward there is no pre-existing lemma to reuse (the original `threeF`/
`fourF`/`fiveF` in `K4.lean`-`K6.lean` fully inline their sub-formulas
rather than `ref`-ing a shared definition 2, so they are different formulas,
merely `Sat`-equivalent ones) — those levels are proved fresh, by the same
two reusable combinators the K-files themselves already use,
`exists_member_iff` and `forall_member_not_bad` (`K3.lean`), chained on top
of the previous level's freshly-proved fact instead of on top of a fully
respelled sub-formula. The final target's characterisation comes out
syntactically identical to `phi6_iff`'s right-hand side, so the last step is
`(phi6_iff e).symm`.

No `sorry`, no `Classical.choice` beyond what `K2.lean`-`K6.lean` already
use internally (`Classical.em` inside `exists_member_iff`, imported, not
re-derived here).
-/

import Rayo.Reuse
import Rayo.K6

namespace Rayo

/-! ## The six definitions and the final target -/

/-- Def 0, "is 0": no references. -/
def defBody0 (t : Nat) : Formula' :=
  .all 1000 (.neg (.mem 1000 t))

/-- Def 1, "is 1": no references. -/
def defBody1 (t : Nat) : Formula' :=
  .conj
    (.neg (.all 1001 (.neg (.mem 1001 t))))
    (.all 1001 (.all 1002 (.neg (.conj (.mem 1001 t) (.mem 1002 1001)))))

/-- Def 2, "is 2": references def 0 (witness `1010`) and def 1 (witness
`1011`); exclusion variable `1012`. -/
def defBody2 (t : Nat) : Formula' :=
  .conj (.neg (.all 1010 (.neg (.conj (.mem 1010 t) (.ref 0 1010))))) (.conj (.neg (.all 1011 (.neg (.conj (.mem 1011 t) (.ref 1 1011))))) (.all 1012 (.neg (.conj (.mem 1012 t) (.conj (.neg (.ref 0 1012)) (.neg (.ref 1 1012)))))))

/-- Def 3, "is 3": references defs 0, 1, 2; exclusion variable `1023`. -/
def defBody3 (t : Nat) : Formula' :=
  .conj (.neg (.all 1020 (.neg (.conj (.mem 1020 t) (.ref 0 1020))))) (.conj (.neg (.all 1021 (.neg (.conj (.mem 1021 t) (.ref 1 1021))))) (.conj (.neg (.all 1022 (.neg (.conj (.mem 1022 t) (.ref 2 1022))))) (.all 1023 (.neg (.conj (.mem 1023 t) (.conj (.neg (.ref 0 1023)) (.conj (.neg (.ref 1 1023)) (.neg (.ref 2 1023)))))))))

/-- Def 4, "is 4": references defs 0, 1, 2, 3; exclusion variable `1034`. -/
def defBody4 (t : Nat) : Formula' :=
  .conj (.neg (.all 1030 (.neg (.conj (.mem 1030 t) (.ref 0 1030))))) (.conj (.neg (.all 1031 (.neg (.conj (.mem 1031 t) (.ref 1 1031))))) (.conj (.neg (.all 1032 (.neg (.conj (.mem 1032 t) (.ref 2 1032))))) (.conj (.neg (.all 1033 (.neg (.conj (.mem 1033 t) (.ref 3 1033))))) (.all 1034 (.neg (.conj (.mem 1034 t) (.conj (.neg (.ref 0 1034)) (.conj (.neg (.ref 1 1034)) (.conj (.neg (.ref 2 1034)) (.neg (.ref 3 1034)))))))))))

/-- Def 5, "is 5": references defs 0, 1, 2, 3, 4; exclusion variable `1045`. -/
def defBody5 (t : Nat) : Formula' :=
  .conj (.neg (.all 1040 (.neg (.conj (.mem 1040 t) (.ref 0 1040))))) (.conj (.neg (.all 1041 (.neg (.conj (.mem 1041 t) (.ref 1 1041))))) (.conj (.neg (.all 1042 (.neg (.conj (.mem 1042 t) (.ref 2 1042))))) (.conj (.neg (.all 1043 (.neg (.conj (.mem 1043 t) (.ref 3 1043))))) (.conj (.neg (.all 1044 (.neg (.conj (.mem 1044 t) (.ref 4 1044))))) (.all 1045 (.neg (.conj (.mem 1045 t) (.conj (.neg (.ref 0 1045)) (.conj (.neg (.ref 1 1045)) (.conj (.neg (.ref 2 1045)) (.conj (.neg (.ref 3 1045)) (.neg (.ref 4 1045)))))))))))))

/-- The final target, "is 6" at `x = v0`: references defs 0..5; exclusion
variable `1056`. -/
def sixFinal : Formula' :=
  .conj (.neg (.all 1050 (.neg (.conj (.mem 1050 0) (.ref 0 1050))))) (.conj (.neg (.all 1051 (.neg (.conj (.mem 1051 0) (.ref 1 1051))))) (.conj (.neg (.all 1052 (.neg (.conj (.mem 1052 0) (.ref 2 1052))))) (.conj (.neg (.all 1053 (.neg (.conj (.mem 1053 0) (.ref 3 1053))))) (.conj (.neg (.all 1054 (.neg (.conj (.mem 1054 0) (.ref 4 1054))))) (.conj (.neg (.all 1055 (.neg (.conj (.mem 1055 0) (.ref 5 1055))))) (.all 1056 (.neg (.conj (.mem 1056 0) (.conj (.neg (.ref 0 1056)) (.conj (.neg (.ref 1 1056)) (.conj (.neg (.ref 2 1056)) (.conj (.neg (.ref 3 1056)) (.conj (.neg (.ref 4 1056)) (.neg (.ref 5 1056)))))))))))))))


/-- The definition list, in order. -/
def sixDefs : List (Nat → Formula') :=
  [defBody0, defBody1, defBody2, defBody3, defBody4, defBody5]

/-- The whole reuse-program naming 6. -/
def sixProgram : Program := { defs := sixDefs, final := sixFinal }

/-! ## Correctness: `expand sixProgram` is `Sat`-equivalent to `phi6`

Definitions 0 and 1 have no `ref`s, so their expansion is *literally* the
existing `zF`/`oneF` formulas (already proved correct by `zF_iff`/`oneF_iff`
in `K2.lean`). Definition 2's expansion is literally `twoF` at matching
parameter slots, so `twoF_iff` (`K3.lean`) transfers with no new proof.
From definition 3 on there is no pre-existing lemma to reuse (the original
`threeF`/`fourF`/`fiveF` fully inline their sub-formulas rather than
referencing a shared definition 2), so those levels are proved fresh with
`exists_member_iff`/`forall_member_not_bad` (`K3.lean`), exactly the same
two combinators the K-files themselves use, chained on the *previous
level's freshly-proved fact* instead of on a fully respelled sub-formula. -/

theorem expand_defBody0 (bound t : Nat) :
    expandN sixDefs bound (defBody0 t) = zF t 1000 := by
  simp [defBody0, expandN_all, expandN_neg, expandN_mem, zF]

theorem expand_defBody1 (bound t : Nat) :
    expandN sixDefs bound (defBody1 t) = oneF t 1001 1002 := by
  simp [defBody1, expandN_all, expandN_neg, expandN_mem, expandN_conj, oneF]

/-- Definition 0 is legal reference target 0 of `sixDefs`. -/
theorem sixDefs_get0 : (sixDefs[0]'(by decide)) = defBody0 := rfl

theorem sixDefs_get1 : (sixDefs[1]'(by decide)) = defBody1 := rfl

theorem sixDefs_get2 : (sixDefs[2]'(by decide)) = defBody2 := rfl

theorem sixDefs_get3 : (sixDefs[3]'(by decide)) = defBody3 := rfl

theorem sixDefs_get4 : (sixDefs[4]'(by decide)) = defBody4 := rfl

theorem sixDefs_get5 : (sixDefs[5]'(by decide)) = defBody5 := rfl

/-- General wrapper: a `ref 0` occurrence, at any witness variable `w` other
than definition 0's own internal variable `1000`, `Sat`-means `IsZero`. -/
theorem sat_ref0 (e : Env) (bound w : Nat) (hb : 0 < bound) (hw : w ≠ 1000) (val : HF) :
    Sat (Env.update e w val) (expandN sixDefs bound (.ref 0 w)) ↔ IsZero val := by
  rw [expandN_ref sixDefs bound 0 w hb (by decide), sixDefs_get0, expand_defBody0]
  have h := zF_iff (Env.update e w val) w 1000 hw
  rwa [Env.update_same] at h

/-- General wrapper for `ref 1`. -/
theorem sat_ref1 (e : Env) (bound w : Nat) (hb : 1 < bound) (hw1 : w ≠ 1001) (hw2 : w ≠ 1002)
    (val : HF) :
    Sat (Env.update e w val) (expandN sixDefs bound (.ref 1 w)) ↔ IsOne val := by
  rw [expandN_ref sixDefs bound 1 w hb (by decide), sixDefs_get1, expand_defBody1]
  have h := oneF_iff (Env.update e w val) w 1001 1002 hw1 hw2 (by decide)
  rwa [Env.update_same] at h

/-- Definition 2's expansion is literally `twoF` at matching parameter
slots (`a=1010,b=1011,c=1012`; internal `z1=cz=1000`, `o1=co1=1001`,
`o2=co2=1002` — reusing the same fixed zF/oneF internals in the two
disjoint quantifier scopes is safe, exactly as the file header explains). -/
theorem expand_defBody2 (bound t : Nat) (hb : 2 ≤ bound) :
    expandN sixDefs bound (defBody2 t)
      = twoF t 1010 1011 1012 1000 1001 1002 1000 1001 1002 := by
  have hb0 : (0:Nat) < bound := by omega
  have hb1 : (1:Nat) < bound := by omega
  simp only [defBody2, expandN_conj, expandN_all, expandN_neg, expandN_mem,
    expandN_ref sixDefs bound 0 1010 hb0 (by decide), sixDefs_get0, expand_defBody0,
    expandN_ref sixDefs bound 1 1011 hb1 (by decide), sixDefs_get1, expand_defBody1,
    expandN_ref sixDefs bound 0 1012 hb0 (by decide),
    expandN_ref sixDefs bound 1 1012 hb1 (by decide)]
  rfl

theorem L2_iff (e : Env) (t : Nat) (bound : Nat) (hb : 2 ≤ bound)
    (ht1 : t ≠ 1010) (ht2 : t ≠ 1011) (ht3 : t ≠ 1012) :
    Sat e (expandN sixDefs bound (defBody2 t)) ↔ IsTwo (e t) := by
  rw [expand_defBody2 bound t hb]
  exact twoF_iff e t 1010 1011 1012 1000 1001 1002 1000 1001 1002
    ht1.symm (by decide) ht2.symm (by decide) (by decide) (by decide)
    ht3.symm (by decide) (by decide) (by decide) (by decide)

/-- General wrapper for `ref 2`. -/
theorem sat_ref2 (e : Env) (bound w : Nat) (hb : 2 < bound)
    (hw1 : w ≠ 1010) (hw2 : w ≠ 1011) (hw3 : w ≠ 1012) (val : HF) :
    Sat (Env.update e w val) (expandN sixDefs bound (.ref 2 w)) ↔ IsTwo val := by
  rw [expandN_ref sixDefs bound 2 w hb (by decide), sixDefs_get2]
  have h := L2_iff (Env.update e w val) w 2 (by omega) hw1 hw2 hw3
  rwa [Env.update_same] at h

/-- Level 3, "is 3": fresh proof (no pre-existing lemma to reuse — `K4.lean`'s
`threeF` fully inlines its sub-formulas instead of referencing a shared
definition 2), built from `exists_member_iff`/`forall_member_not_bad`
exactly as `K3.lean`-`K6.lean` build every level, chained on `sat_ref0`,
`sat_ref1`, `sat_ref2` instead of on `zF_iff`/`oneF_iff`/`twoF_iff`
directly. -/
theorem L3_iff (e : Env) (t bound : Nat) (hb : 3 ≤ bound)
    (ht1 : t ≠ 1020) (ht2 : t ≠ 1021) (ht3 : t ≠ 1022) (ht4 : t ≠ 1023) :
    Sat e (expandN sixDefs bound (defBody3 t)) ↔ IsThree (e t) := by
  have hb0 : (0:Nat) < bound := by omega
  have hb1 : (1:Nat) < bound := by omega
  have hb2 : (2:Nat) < bound := by omega
  have hexp : expandN sixDefs bound (defBody3 t)
      = (.conj (.neg (.all 1020 (.neg (.conj (.mem 1020 t) (expandN sixDefs bound (.ref 0 1020)))))) (.conj (.neg (.all 1021 (.neg (.conj (.mem 1021 t) (expandN sixDefs bound (.ref 1 1021)))))) (.conj (.neg (.all 1022 (.neg (.conj (.mem 1022 t) (expandN sixDefs bound (.ref 2 1022)))))) (.all 1023 (.neg (.conj (.mem 1023 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1023))) (.conj (.neg (expandN sixDefs bound (.ref 1 1023))) (.neg (expandN sixDefs bound (.ref 2 1023)))))))))))
      := by
    simp [defBody3, expandN_conj, expandN_neg, expandN_all, expandN_mem]
  rw [hexp]
  have hE0 := exists_member_iff e t 1020 (expandN sixDefs bound (.ref 0 1020)) IsZero
    (by omega) (fun val => sat_ref0 e bound 1020 hb0 (by decide) val)
  have hE1 := exists_member_iff e t 1021 (expandN sixDefs bound (.ref 1 1021)) IsOne
    (by omega) (fun val => sat_ref1 e bound 1021 hb1 (by decide) (by decide) val)
  have hE2 := exists_member_iff e t 1022 (expandN sixDefs bound (.ref 2 1022)) IsTwo
    (by omega) (fun val => sat_ref2 e bound 1022 hb2 (by decide) (by decide) (by decide) val)
  have hB : ∀ val, Sat (Env.update e 1023 val)
      (.conj (.neg (expandN sixDefs bound (.ref 0 1023)))
        (.conj (.neg (expandN sixDefs bound (.ref 1 1023)))
          (.neg (expandN sixDefs bound (.ref 2 1023)))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) := by
    intro val
    have h0 := sat_ref0 e bound 1023 hb0 (by decide) val
    have h1 := sat_ref1 e bound 1023 hb1 (by decide) (by decide) val
    have h2 := sat_ref2 e bound 1023 hb2 (by decide) (by decide) (by decide) val
    simp only [Sat, h0, h1, h2]
  have hU := forall_member_not_bad e t 1023
    (.conj (.neg (expandN sixDefs bound (.ref 0 1023)))
      (.conj (.neg (expandN sixDefs bound (.ref 1 1023)))
        (.neg (expandN sixDefs bound (.ref 2 1023)))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val) (by omega) hB
  have hsplit : Sat e (.conj (.neg (.all 1020 (.neg (.conj (.mem 1020 t) (expandN sixDefs bound (.ref 0 1020)))))) (.conj (.neg (.all 1021 (.neg (.conj (.mem 1021 t) (expandN sixDefs bound (.ref 1 1021)))))) (.conj (.neg (.all 1022 (.neg (.conj (.mem 1022 t) (expandN sixDefs bound (.ref 2 1022)))))) (.all 1023 (.neg (.conj (.mem 1023 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1023))) (.conj (.neg (expandN sixDefs bound (.ref 1 1023))) (.neg (expandN sixDefs bound (.ref 2 1023)))))))))))
      ↔ (Sat e (.neg (.all 1020 (.neg (.conj (.mem 1020 t) (expandN sixDefs bound (.ref 0 1020)))))) ∧ (Sat e (.neg (.all 1021 (.neg (.conj (.mem 1021 t) (expandN sixDefs bound (.ref 1 1021)))))) ∧ (Sat e (.neg (.all 1022 (.neg (.conj (.mem 1022 t) (expandN sixDefs bound (.ref 2 1022)))))) ∧ Sat e (.all 1023 (.neg (.conj (.mem 1023 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1023))) (.conj (.neg (expandN sixDefs bound (.ref 1 1023))) (.neg (expandN sixDefs bound (.ref 2 1023)))))))))))
      := Iff.rfl
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

/-- General wrapper for `ref 3`. -/
theorem sat_ref3 (e : Env) (bound w : Nat) (hb : 3 < bound)
    (hw1 : w ≠ 1020) (hw2 : w ≠ 1021) (hw3 : w ≠ 1022) (hw4 : w ≠ 1023) (val : HF) :
    Sat (Env.update e w val) (expandN sixDefs bound (.ref 3 w)) ↔ IsThree val := by
  rw [expandN_ref sixDefs bound 3 w hb (by decide), sixDefs_get3]
  have h := L3_iff (Env.update e w val) w 3 (by omega) hw1 hw2 hw3 hw4
  rwa [Env.update_same] at h

/-- Level 4, "is 4": same pattern as `L3_iff`, one level up. -/
theorem L4_iff (e : Env) (t bound : Nat) (hb : 4 ≤ bound)
    (ht1 : t ≠ 1030) (ht2 : t ≠ 1031) (ht3 : t ≠ 1032) (ht4 : t ≠ 1033) (ht5 : t ≠ 1034) :
    Sat e (expandN sixDefs bound (defBody4 t)) ↔ IsFour (e t) := by
  have hb0 : (0:Nat) < bound := by omega
  have hb1 : (1:Nat) < bound := by omega
  have hb2 : (2:Nat) < bound := by omega
  have hb3 : (3:Nat) < bound := by omega
  have hexp : expandN sixDefs bound (defBody4 t)
      = (.conj (.neg (.all 1030 (.neg (.conj (.mem 1030 t) (expandN sixDefs bound (.ref 0 1030)))))) (.conj (.neg (.all 1031 (.neg (.conj (.mem 1031 t) (expandN sixDefs bound (.ref 1 1031)))))) (.conj (.neg (.all 1032 (.neg (.conj (.mem 1032 t) (expandN sixDefs bound (.ref 2 1032)))))) (.conj (.neg (.all 1033 (.neg (.conj (.mem 1033 t) (expandN sixDefs bound (.ref 3 1033)))))) (.all 1034 (.neg (.conj (.mem 1034 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1034))) (.conj (.neg (expandN sixDefs bound (.ref 1 1034))) (.conj (.neg (expandN sixDefs bound (.ref 2 1034))) (.neg (expandN sixDefs bound (.ref 3 1034)))))))))))))
      := by
    simp [defBody4, expandN_conj, expandN_neg, expandN_all, expandN_mem]
  rw [hexp]
  have hE0 := exists_member_iff e t 1030 (expandN sixDefs bound (.ref 0 1030)) IsZero
    (by omega) (fun val => sat_ref0 e bound 1030 hb0 (by decide) val)
  have hE1 := exists_member_iff e t 1031 (expandN sixDefs bound (.ref 1 1031)) IsOne
    (by omega) (fun val => sat_ref1 e bound 1031 hb1 (by decide) (by decide) val)
  have hE2 := exists_member_iff e t 1032 (expandN sixDefs bound (.ref 2 1032)) IsTwo
    (by omega) (fun val => sat_ref2 e bound 1032 hb2 (by decide) (by decide) (by decide) val)
  have hE3 := exists_member_iff e t 1033 (expandN sixDefs bound (.ref 3 1033)) IsThree
    (by omega) (fun val => sat_ref3 e bound 1033 hb3 (by decide) (by decide) (by decide) (by decide) val)
  have hB : ∀ val, Sat (Env.update e 1034 val)
      (.conj (.neg (expandN sixDefs bound (.ref 0 1034))) (.conj (.neg (expandN sixDefs bound (.ref 1 1034))) (.conj (.neg (expandN sixDefs bound (.ref 2 1034))) (.neg (expandN sixDefs bound (.ref 3 1034))))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val) := by
    intro val
    have h0 := sat_ref0 e bound 1034 hb0 (by decide) val
    have h1 := sat_ref1 e bound 1034 hb1 (by decide) (by decide) val
    have h2 := sat_ref2 e bound 1034 hb2 (by decide) (by decide) (by decide) val
    have h3 := sat_ref3 e bound 1034 hb3 (by decide) (by decide) (by decide) (by decide) val
    simp only [Sat, h0, h1, h2, h3]
  have hU := forall_member_not_bad e t 1034
    (.conj (.neg (expandN sixDefs bound (.ref 0 1034))) (.conj (.neg (expandN sixDefs bound (.ref 1 1034))) (.conj (.neg (expandN sixDefs bound (.ref 2 1034))) (.neg (expandN sixDefs bound (.ref 3 1034))))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val) (by omega) hB
  have hsplit : Sat e (.conj (.neg (.all 1030 (.neg (.conj (.mem 1030 t) (expandN sixDefs bound (.ref 0 1030)))))) (.conj (.neg (.all 1031 (.neg (.conj (.mem 1031 t) (expandN sixDefs bound (.ref 1 1031)))))) (.conj (.neg (.all 1032 (.neg (.conj (.mem 1032 t) (expandN sixDefs bound (.ref 2 1032)))))) (.conj (.neg (.all 1033 (.neg (.conj (.mem 1033 t) (expandN sixDefs bound (.ref 3 1033)))))) (.all 1034 (.neg (.conj (.mem 1034 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1034))) (.conj (.neg (expandN sixDefs bound (.ref 1 1034))) (.conj (.neg (expandN sixDefs bound (.ref 2 1034))) (.neg (expandN sixDefs bound (.ref 3 1034)))))))))))))
      ↔ (Sat e (.neg (.all 1030 (.neg (.conj (.mem 1030 t) (expandN sixDefs bound (.ref 0 1030)))))) ∧ (Sat e (.neg (.all 1031 (.neg (.conj (.mem 1031 t) (expandN sixDefs bound (.ref 1 1031)))))) ∧ (Sat e (.neg (.all 1032 (.neg (.conj (.mem 1032 t) (expandN sixDefs bound (.ref 2 1032)))))) ∧ (Sat e (.neg (.all 1033 (.neg (.conj (.mem 1033 t) (expandN sixDefs bound (.ref 3 1033)))))) ∧ Sat e (.all 1034 (.neg (.conj (.mem 1034 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1034))) (.conj (.neg (expandN sixDefs bound (.ref 1 1034))) (.conj (.neg (expandN sixDefs bound (.ref 2 1034))) (.neg (expandN sixDefs bound (.ref 3 1034)))))))))))))
      := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hE3, hU]
  unfold IsFour
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

/-- General wrapper for `ref 4`. -/
theorem sat_ref4 (e : Env) (bound w : Nat) (hb : 4 < bound)
    (hw1 : w ≠ 1030) (hw2 : w ≠ 1031) (hw3 : w ≠ 1032) (hw4 : w ≠ 1033) (hw5 : w ≠ 1034)
    (val : HF) :
    Sat (Env.update e w val) (expandN sixDefs bound (.ref 4 w)) ↔ IsFour val := by
  rw [expandN_ref sixDefs bound 4 w hb (by decide), sixDefs_get4]
  have h := L4_iff (Env.update e w val) w 4 (by omega) hw1 hw2 hw3 hw4 hw5
  rwa [Env.update_same] at h

/-- Level 5, "is 5": same pattern, one level up. -/
theorem L5_iff (e : Env) (t bound : Nat) (hb : 5 ≤ bound)
    (ht1 : t ≠ 1040) (ht2 : t ≠ 1041) (ht3 : t ≠ 1042) (ht4 : t ≠ 1043) (ht5 : t ≠ 1044)
    (ht6 : t ≠ 1045) :
    Sat e (expandN sixDefs bound (defBody5 t)) ↔ IsFive (e t) := by
  have hb0 : (0:Nat) < bound := by omega
  have hb1 : (1:Nat) < bound := by omega
  have hb2 : (2:Nat) < bound := by omega
  have hb3 : (3:Nat) < bound := by omega
  have hb4 : (4:Nat) < bound := by omega
  have hexp : expandN sixDefs bound (defBody5 t)
      = (.conj (.neg (.all 1040 (.neg (.conj (.mem 1040 t) (expandN sixDefs bound (.ref 0 1040)))))) (.conj (.neg (.all 1041 (.neg (.conj (.mem 1041 t) (expandN sixDefs bound (.ref 1 1041)))))) (.conj (.neg (.all 1042 (.neg (.conj (.mem 1042 t) (expandN sixDefs bound (.ref 2 1042)))))) (.conj (.neg (.all 1043 (.neg (.conj (.mem 1043 t) (expandN sixDefs bound (.ref 3 1043)))))) (.conj (.neg (.all 1044 (.neg (.conj (.mem 1044 t) (expandN sixDefs bound (.ref 4 1044)))))) (.all 1045 (.neg (.conj (.mem 1045 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1045))) (.conj (.neg (expandN sixDefs bound (.ref 1 1045))) (.conj (.neg (expandN sixDefs bound (.ref 2 1045))) (.conj (.neg (expandN sixDefs bound (.ref 3 1045))) (.neg (expandN sixDefs bound (.ref 4 1045)))))))))))))))
      := by
    simp [defBody5, expandN_conj, expandN_neg, expandN_all, expandN_mem]
  rw [hexp]
  have hE0 := exists_member_iff e t 1040 (expandN sixDefs bound (.ref 0 1040)) IsZero
    (by omega) (fun val => sat_ref0 e bound 1040 hb0 (by decide) val)
  have hE1 := exists_member_iff e t 1041 (expandN sixDefs bound (.ref 1 1041)) IsOne
    (by omega) (fun val => sat_ref1 e bound 1041 hb1 (by decide) (by decide) val)
  have hE2 := exists_member_iff e t 1042 (expandN sixDefs bound (.ref 2 1042)) IsTwo
    (by omega) (fun val => sat_ref2 e bound 1042 hb2 (by decide) (by decide) (by decide) val)
  have hE3 := exists_member_iff e t 1043 (expandN sixDefs bound (.ref 3 1043)) IsThree
    (by omega) (fun val => sat_ref3 e bound 1043 hb3 (by decide) (by decide) (by decide) (by decide) val)
  have hE4 := exists_member_iff e t 1044 (expandN sixDefs bound (.ref 4 1044)) IsFour
    (by omega) (fun val => sat_ref4 e bound 1044 hb4 (by decide) (by decide) (by decide) (by decide) (by decide) val)
  have hB : ∀ val, Sat (Env.update e 1045 val)
      (.conj (.neg (expandN sixDefs bound (.ref 0 1045))) (.conj (.neg (expandN sixDefs bound (.ref 1 1045))) (.conj (.neg (expandN sixDefs bound (.ref 2 1045))) (.conj (.neg (expandN sixDefs bound (.ref 3 1045))) (.neg (expandN sixDefs bound (.ref 4 1045)))))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val) := by
    intro val
    have h0 := sat_ref0 e bound 1045 hb0 (by decide) val
    have h1 := sat_ref1 e bound 1045 hb1 (by decide) (by decide) val
    have h2 := sat_ref2 e bound 1045 hb2 (by decide) (by decide) (by decide) val
    have h3 := sat_ref3 e bound 1045 hb3 (by decide) (by decide) (by decide) (by decide) val
    have h4 := sat_ref4 e bound 1045 hb4 (by decide) (by decide) (by decide) (by decide) (by decide) val
    simp only [Sat, h0, h1, h2, h3, h4]
  have hU := forall_member_not_bad e t 1045
    (.conj (.neg (expandN sixDefs bound (.ref 0 1045))) (.conj (.neg (expandN sixDefs bound (.ref 1 1045))) (.conj (.neg (expandN sixDefs bound (.ref 2 1045))) (.conj (.neg (expandN sixDefs bound (.ref 3 1045))) (.neg (expandN sixDefs bound (.ref 4 1045)))))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val) (by omega) hB
  have hsplit : Sat e (.conj (.neg (.all 1040 (.neg (.conj (.mem 1040 t) (expandN sixDefs bound (.ref 0 1040)))))) (.conj (.neg (.all 1041 (.neg (.conj (.mem 1041 t) (expandN sixDefs bound (.ref 1 1041)))))) (.conj (.neg (.all 1042 (.neg (.conj (.mem 1042 t) (expandN sixDefs bound (.ref 2 1042)))))) (.conj (.neg (.all 1043 (.neg (.conj (.mem 1043 t) (expandN sixDefs bound (.ref 3 1043)))))) (.conj (.neg (.all 1044 (.neg (.conj (.mem 1044 t) (expandN sixDefs bound (.ref 4 1044)))))) (.all 1045 (.neg (.conj (.mem 1045 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1045))) (.conj (.neg (expandN sixDefs bound (.ref 1 1045))) (.conj (.neg (expandN sixDefs bound (.ref 2 1045))) (.conj (.neg (expandN sixDefs bound (.ref 3 1045))) (.neg (expandN sixDefs bound (.ref 4 1045)))))))))))))))
      ↔ (Sat e (.neg (.all 1040 (.neg (.conj (.mem 1040 t) (expandN sixDefs bound (.ref 0 1040)))))) ∧ (Sat e (.neg (.all 1041 (.neg (.conj (.mem 1041 t) (expandN sixDefs bound (.ref 1 1041)))))) ∧ (Sat e (.neg (.all 1042 (.neg (.conj (.mem 1042 t) (expandN sixDefs bound (.ref 2 1042)))))) ∧ (Sat e (.neg (.all 1043 (.neg (.conj (.mem 1043 t) (expandN sixDefs bound (.ref 3 1043)))))) ∧ (Sat e (.neg (.all 1044 (.neg (.conj (.mem 1044 t) (expandN sixDefs bound (.ref 4 1044)))))) ∧ Sat e (.all 1045 (.neg (.conj (.mem 1045 t) (.conj (.neg (expandN sixDefs bound (.ref 0 1045))) (.conj (.neg (expandN sixDefs bound (.ref 1 1045))) (.conj (.neg (expandN sixDefs bound (.ref 2 1045))) (.conj (.neg (expandN sixDefs bound (.ref 3 1045))) (.neg (expandN sixDefs bound (.ref 4 1045)))))))))))))))
      := Iff.rfl
  rw [hsplit, hE0, hE1, hE2, hE3, hE4, hU]
  unfold IsFive
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

/-- General wrapper for `ref 5`. -/
theorem sat_ref5 (e : Env) (bound w : Nat) (hb : 5 < bound)
    (hw1 : w ≠ 1040) (hw2 : w ≠ 1041) (hw3 : w ≠ 1042) (hw4 : w ≠ 1043) (hw5 : w ≠ 1044)
    (hw6 : w ≠ 1045) (val : HF) :
    Sat (Env.update e w val) (expandN sixDefs bound (.ref 5 w)) ↔ IsFive val := by
  rw [expandN_ref sixDefs bound 5 w hb (by decide), sixDefs_get5]
  have h := L5_iff (Env.update e w val) w 5 (by omega) hw1 hw2 hw3 hw4 hw5 hw6
  rwa [Env.update_same] at h

/-- The final target's expansion characterisation, at `bound = 6`
(`sixDefs.length`), matching `phi6_iff`'s right-hand side exactly. -/
theorem sixFinal_iff (e : Env) :
    Sat e (expandN sixDefs 6 sixFinal) ↔
      ( (∃ a, a ∈ (e 0).elems ∧ IsZero a)
        ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
        ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
        ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
        ∧ (∃ p, p ∈ (e 0).elems ∧ IsFour p)
        ∧ (∃ q, q ∈ (e 0).elems ∧ IsFive q)
        ∧ (∀ c, c ∈ (e 0).elems →
            (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c ∨ IsFive c)) ) := by
  have hb0 : (0:Nat) < 6 := by omega
  have hb1 : (1:Nat) < 6 := by omega
  have hb2 : (2:Nat) < 6 := by omega
  have hb3 : (3:Nat) < 6 := by omega
  have hb4 : (4:Nat) < 6 := by omega
  have hb5 : (5:Nat) < 6 := by omega
  have hexp : expandN sixDefs 6 sixFinal
      = (.conj (.neg (.all 1050 (.neg (.conj (.mem 1050 0) (expandN sixDefs 6 (.ref 0 1050)))))) (.conj (.neg (.all 1051 (.neg (.conj (.mem 1051 0) (expandN sixDefs 6 (.ref 1 1051)))))) (.conj (.neg (.all 1052 (.neg (.conj (.mem 1052 0) (expandN sixDefs 6 (.ref 2 1052)))))) (.conj (.neg (.all 1053 (.neg (.conj (.mem 1053 0) (expandN sixDefs 6 (.ref 3 1053)))))) (.conj (.neg (.all 1054 (.neg (.conj (.mem 1054 0) (expandN sixDefs 6 (.ref 4 1054)))))) (.conj (.neg (.all 1055 (.neg (.conj (.mem 1055 0) (expandN sixDefs 6 (.ref 5 1055)))))) (.all 1056 (.neg (.conj (.mem 1056 0) (.conj (.neg (expandN sixDefs 6 (.ref 0 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 1 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 2 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 3 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 4 1056))) (.neg (expandN sixDefs 6 (.ref 5 1056)))))))))))))))))
      := by
    simp [sixFinal, expandN_conj, expandN_neg, expandN_all, expandN_mem]
  rw [hexp]
  have hE0 := exists_member_iff e 0 1050 (expandN sixDefs 6 (.ref 0 1050)) IsZero
    (by omega) (fun val => sat_ref0 e 6 1050 hb0 (by decide) val)
  have hE1 := exists_member_iff e 0 1051 (expandN sixDefs 6 (.ref 1 1051)) IsOne
    (by omega) (fun val => sat_ref1 e 6 1051 hb1 (by decide) (by decide) val)
  have hE2 := exists_member_iff e 0 1052 (expandN sixDefs 6 (.ref 2 1052)) IsTwo
    (by omega) (fun val => sat_ref2 e 6 1052 hb2 (by decide) (by decide) (by decide) val)
  have hE3 := exists_member_iff e 0 1053 (expandN sixDefs 6 (.ref 3 1053)) IsThree
    (by omega) (fun val => sat_ref3 e 6 1053 hb3 (by decide) (by decide) (by decide) (by decide) val)
  have hE4 := exists_member_iff e 0 1054 (expandN sixDefs 6 (.ref 4 1054)) IsFour
    (by omega) (fun val => sat_ref4 e 6 1054 hb4 (by decide) (by decide) (by decide) (by decide) (by decide) val)
  have hE5 := exists_member_iff e 0 1055 (expandN sixDefs 6 (.ref 5 1055)) IsFive
    (by omega) (fun val => sat_ref5 e 6 1055 hb5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) val)
  have hB : ∀ val, Sat (Env.update e 1056 val)
      (.conj (.neg (expandN sixDefs 6 (.ref 0 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 1 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 2 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 3 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 4 1056))) (.neg (expandN sixDefs 6 (.ref 5 1056))))))))
      ↔ (¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val ∧ ¬ IsFive val) := by
    intro val
    have h0 := sat_ref0 e 6 1056 hb0 (by decide) val
    have h1 := sat_ref1 e 6 1056 hb1 (by decide) (by decide) val
    have h2 := sat_ref2 e 6 1056 hb2 (by decide) (by decide) (by decide) val
    have h3 := sat_ref3 e 6 1056 hb3 (by decide) (by decide) (by decide) (by decide) val
    have h4 := sat_ref4 e 6 1056 hb4 (by decide) (by decide) (by decide) (by decide) (by decide) val
    have h5 := sat_ref5 e 6 1056 hb5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) val
    simp only [Sat, h0, h1, h2, h3, h4, h5]
  have hU := forall_member_not_bad e 0 1056
    (.conj (.neg (expandN sixDefs 6 (.ref 0 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 1 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 2 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 3 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 4 1056))) (.neg (expandN sixDefs 6 (.ref 5 1056))))))))
    (fun val => ¬ IsZero val ∧ ¬ IsOne val ∧ ¬ IsTwo val ∧ ¬ IsThree val ∧ ¬ IsFour val ∧ ¬ IsFive val)
    (by omega) hB
  have hsplit : Sat e (.conj (.neg (.all 1050 (.neg (.conj (.mem 1050 0) (expandN sixDefs 6 (.ref 0 1050)))))) (.conj (.neg (.all 1051 (.neg (.conj (.mem 1051 0) (expandN sixDefs 6 (.ref 1 1051)))))) (.conj (.neg (.all 1052 (.neg (.conj (.mem 1052 0) (expandN sixDefs 6 (.ref 2 1052)))))) (.conj (.neg (.all 1053 (.neg (.conj (.mem 1053 0) (expandN sixDefs 6 (.ref 3 1053)))))) (.conj (.neg (.all 1054 (.neg (.conj (.mem 1054 0) (expandN sixDefs 6 (.ref 4 1054)))))) (.conj (.neg (.all 1055 (.neg (.conj (.mem 1055 0) (expandN sixDefs 6 (.ref 5 1055)))))) (.all 1056 (.neg (.conj (.mem 1056 0) (.conj (.neg (expandN sixDefs 6 (.ref 0 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 1 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 2 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 3 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 4 1056))) (.neg (expandN sixDefs 6 (.ref 5 1056)))))))))))))))))
      ↔ (Sat e (.neg (.all 1050 (.neg (.conj (.mem 1050 0) (expandN sixDefs 6 (.ref 0 1050)))))) ∧ (Sat e (.neg (.all 1051 (.neg (.conj (.mem 1051 0) (expandN sixDefs 6 (.ref 1 1051)))))) ∧ (Sat e (.neg (.all 1052 (.neg (.conj (.mem 1052 0) (expandN sixDefs 6 (.ref 2 1052)))))) ∧ (Sat e (.neg (.all 1053 (.neg (.conj (.mem 1053 0) (expandN sixDefs 6 (.ref 3 1053)))))) ∧ (Sat e (.neg (.all 1054 (.neg (.conj (.mem 1054 0) (expandN sixDefs 6 (.ref 4 1054)))))) ∧ (Sat e (.neg (.all 1055 (.neg (.conj (.mem 1055 0) (expandN sixDefs 6 (.ref 5 1055)))))) ∧ Sat e (.all 1056 (.neg (.conj (.mem 1056 0) (.conj (.neg (expandN sixDefs 6 (.ref 0 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 1 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 2 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 3 1056))) (.conj (.neg (expandN sixDefs 6 (.ref 4 1056))) (.neg (expandN sixDefs 6 (.ref 5 1056)))))))))))))))))
      := Iff.rfl
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

/-- **Main correctness theorem.** Expanding `sixProgram` — the reuse-based
program naming 6, built entirely from `ref`s to definitions 0-5 rather than
by respelling any sub-formula — produces a `Formula` that is `Sat`-equivalent
to `Rayo.K6`'s independently-built, fully self-contained `phi6`. This is the
mechanized correctness check the reuse mechanism exists to justify: the
compressed construction names exactly the same number, not merely a
shorter-looking one. -/
theorem sixProgram_correct (e : Env) : Sat e (expand sixProgram) ↔ Sat e phi6 := by
  show Sat e (expandN sixDefs sixDefs.length sixFinal) ↔ Sat e phi6
  rw [show sixDefs.length = 6 from rfl, sixFinal_iff, phi6_iff]

/-! ### Corollaries: the reuse program actually names 6

`sixProgram_correct` alone only says "equivalent to `phi6`"; composing it
with `K6.lean`'s own existence/uniqueness theorems for `phi6` upgrades that
to the same existence-and-uniqueness statement about `expand sixProgram`
directly, i.e. the reuse program really does name the number 6, not just
"a formula extensionally tied to one that does". -/

/-- Existence: the canonical `six = {0,1,2,3,4,5}` satisfies the expanded
reuse program. -/
theorem sixProgram_holds_of_six : Sat (fun _ => six) (expand sixProgram) :=
  (sixProgram_correct _).mpr phi6_holds_of_six

/-- Naming: any solution of the expanded reuse program has exactly the
member-classification of `six`. -/
theorem sixProgram_names_six (e : Env) (h : Sat e (expand sixProgram)) :
    (∃ a, a ∈ (e 0).elems ∧ IsZero a)
    ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
    ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
    ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
    ∧ (∃ p, p ∈ (e 0).elems ∧ IsFour p)
    ∧ (∃ q, q ∈ (e 0).elems ∧ IsFive q)
    ∧ (∀ c, c ∈ (e 0).elems →
        (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c ∨ IsFive c)) :=
  phi6_names_six e ((sixProgram_correct e).mp h)

/-- Uniqueness up to `ClassEq6`: any two solutions of the expanded reuse
program have exactly the same members up to `ClassEq6`. -/
theorem sixProgram_unique (e e' : Env)
    (h : Sat e (expand sixProgram)) (h' : Sat e' (expand sixProgram)) :
    ∀ z, (∃ m, m ∈ (e 0).elems ∧ ClassEq6 z m)
        ↔ (∃ m, m ∈ (e' 0).elems ∧ ClassEq6 z m) :=
  phi6_unique e e' ((sixProgram_correct e).mp h) ((sixProgram_correct e').mp h')

end Rayo
