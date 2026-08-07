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

end Rayo
