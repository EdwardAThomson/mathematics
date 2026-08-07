/-
`RayoBoolos.Probe` — a small, machine-checked confirmation of an indexing
convention needed for Step 4 (`BOOLOS-B0-WELLDEFINEDNESS.md` §6, B3):
when a multi-variable `Foundation` semisentence is built via the header
form `“name0 name1 ... . body”` and then applied via `!θ a0 a1 ...`, do
the listed application arguments fill the header names in the SAME
left-to-right order (`a0 ↦ name0`, `a1 ↦ name1`, ...)? Confirmed here: yes.
This matters because Foundation's own "Function via" graph-encoding
convention (e.g. `Bootstrapping.Arithmetic.ssnum`, `Bootstrapping/
FixedPoint.lean`) lists the OUTPUT variable first in the header — a
two-variable Σ1 "graph of f" semisentence `θ` should therefore be written
`“y x. body(y,x)”` (value first, argument second) to compose correctly
with `Semiformula.existsUnique`/`∃¹!`, which existentially quantifies over
slot `#0`.
-/

module

public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness

@[expose] public section

namespace RayoBoolos.Probe

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

def probeLt : ArithmeticSemisentence 2 := “x y. x < y”

example : probeLt.Evalb (M := ℕ) ![3, 5] := by
  simp [probeLt]

def probeApply : ArithmeticSemisentence 0 := “!probeLt 3 5”

example : probeApply.Evalb (M := ℕ) ![] := by
  simp [probeApply, probeLt]

end RayoBoolos.Probe
