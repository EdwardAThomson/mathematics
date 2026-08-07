/-
`Rayo.K0` — the k = 0 feasibility spike.

We prove that the formula

    φ₀(x)  ≔  ∀ y, ¬ (y ∈ x)          -- here x = v₀, y = v₁

has, in the hereditarily-finite-set model, exactly one solution, namely the
empty set. This is the "names 0 = ∅" base case of the von-Neumann encoding.
The proof is complete: it discharges every goal with no proof holes.
-/

import Rayo.Satisfaction

namespace Rayo

/-- The k = 0 naming formula `φ₀(v₀) ≔ ∀ v₁, ¬ (v₁ ∈ v₀)`. -/
def phi0 : Formula := .all 1 (.neg (.mem 1 0))

/-- Specialized assignment-lookup rewrites for the two variables of `φ₀`. -/
private theorem upd11 (e : Env) (v : HF) : Env.update e 1 v 1 = v :=
  Env.update_same e 1 v

private theorem upd10 (e : Env) (v : HF) : Env.update e 1 v 0 = e 0 :=
  Env.update_other e 1 0 v (by decide)

/-- An HF set has no members iff it is the empty set. -/
theorem no_mem_iff_empty (x : HF) :
    (∀ v : HF, ¬ v ∈ x.elems) ↔ x = HF.empty := by
  cases x with
  | mk l =>
    simp only [HF.elems, HF.empty]
    constructor
    · intro h
      cases l with
      | nil => rfl
      | cons b rest => exact absurd (show b ∈ b :: rest by simp) (h b)
    · intro h v
      injection h with hl
      subst hl
      simp

/-- `φ₀` holds of `v₀` under an assignment exactly when `v₀` is the empty set. -/
theorem phi0_iff_empty (e : Env) : Sat e phi0 ↔ e 0 = HF.empty := by
  have key : Sat e phi0 ↔ (∀ v : HF, ¬ v ∈ (e 0).elems) := by
    simp only [phi0, Sat, HF.Mem, upd11, upd10]
  rw [key]
  exact no_mem_iff_empty (e 0)

/-- Existence: the all-empty assignment satisfies `φ₀`. -/
theorem phi0_holds_of_empty : Sat (fun _ => HF.empty) phi0 :=
  (phi0_iff_empty _).2 rfl

/-- Uniqueness: any two assignments satisfying `φ₀` agree on `v₀`
(both give the empty set). -/
theorem phi0_unique (e e' : Env)
    (h : Sat e phi0) (h' : Sat e' phi0) : e 0 = e' 0 := by
  rw [(phi0_iff_empty e).1 h, (phi0_iff_empty e').1 h']

/-- The unique solution is the empty set. -/
theorem phi0_solution_is_empty (e : Env) (h : Sat e phi0) :
    e 0 = HF.empty :=
  (phi0_iff_empty e).1 h

end Rayo
