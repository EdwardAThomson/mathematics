/-
`Rayo.Syntax` — the syntax of first-order formulas of set theory over the
single binary relation symbol `∈` ("in"), plus equality.

This is the self-contained (no-Mathlib) formalization for the Rayo-function
family. Variables are natural-number indices `v₀, v₁, v₂, …`. Only the
*primitive* connectives are represented here; `∨`, `→`, `↔`, `∃`, `∃!` are
regarded as abbreviations expanded into these, matching the symbol-counting
convention fixed for this run.
-/

namespace Rayo

/-- Formulas of first-order set theory over `∈`.

* `mem i j`  encodes `vᵢ ∈ vⱼ`
* `eq i j`   encodes `vᵢ = vⱼ`
* `neg φ`    encodes `¬ φ`
* `conj φ ψ` encodes `φ ∧ ψ`
* `all n φ`  encodes `∀ vₙ, φ`
-/
inductive Formula where
  | mem  : Nat → Nat → Formula
  | eq   : Nat → Nat → Formula
  | neg  : Formula → Formula
  | conj : Formula → Formula → Formula
  | all  : Nat → Formula → Formula
  deriving Repr, DecidableEq

end Rayo
