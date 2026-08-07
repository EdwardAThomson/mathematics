/-
`Rayo.Satisfaction` — a self-contained hereditarily-finite-set (HF) model and
the Tarski satisfaction relation `Sat` for `Rayo.Formula`.

An HF set is given by the finite list of its elements. Membership is list
membership on that element list. This is enough to state and prove the k = 0
uniqueness spike; extensionality (needed for larger k) is deliberately left
for later items.
-/

import Rayo.Syntax

namespace Rayo

/-- Hereditarily finite sets: a set is the (finite) list of its elements. -/
inductive HF where
  | mk : List HF → HF

namespace HF

/-- The element list of an HF set. -/
def elems : HF → List HF
  | .mk l => l

/-- Membership: `a ∈ x` iff `a` occurs in `x`'s element list. -/
def Mem (a x : HF) : Prop := a ∈ x.elems

/-- The empty set `∅`. -/
def empty : HF := .mk []

end HF

/-- A variable assignment maps each variable index to an HF set. -/
def Env := Nat → HF

/-- Update assignment `e` so that variable `n` is sent to `v`. -/
def Env.update (e : Env) (n : Nat) (v : HF) : Env :=
  fun m => if m = n then v else e m

/-- Tarski satisfaction of a formula under an assignment. -/
def Sat (e : Env) : Formula → Prop
  | .mem i j  => HF.Mem (e i) (e j)
  | .eq i j   => e i = e j
  | .neg φ    => ¬ Sat e φ
  | .conj φ ψ => Sat e φ ∧ Sat e ψ
  | .all n φ  => ∀ v : HF, Sat (Env.update e n v) φ

/-- Reading variable `n` back out of an updated assignment returns the new value. -/
theorem Env.update_same (e : Env) (n : Nat) (v : HF) :
    Env.update e n v n = v := by
  show (if n = n then v else e n) = v
  rw [if_pos rfl]

/-- Reading a *different* variable out of an updated assignment is unchanged. -/
theorem Env.update_other (e : Env) (n m : Nat) (v : HF) (h : m ≠ n) :
    Env.update e n v m = e m := by
  show (if m = n then v else e m) = e m
  rw [if_neg h]

end Rayo
