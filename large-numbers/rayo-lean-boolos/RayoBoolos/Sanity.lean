/-
Step 1 baseline sanity check: `Foundation`'s own Gödel first-incompleteness
theorem, `#print axioms`-checked from this checkout. Not new content — just
confirms the dependency is usable and sorry-free before Step 3 builds on it.
-/

module

public import Foundation.FirstOrder.Incompleteness.First

@[expose] public section

#print axioms LO.FirstOrder.Arithmetic.incomplete
#print axioms LO.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence
