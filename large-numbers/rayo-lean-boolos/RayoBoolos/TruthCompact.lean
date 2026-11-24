/-
`RayoBoolos.TruthCompact`: the Busy Beaver upper bound for `Σ₁` truth naming
(`TruthBig_sigma1_le_BB`) with an explicit `O(n log n)` input length in place
of the unbounded function `h`, using the compact formula code of
`RayoBoolos.CompactCode`.
-/

module

public import RayoBoolos.TruthNaming
public import RayoBoolos.CompactCode

@[expose] public section

namespace RayoBoolos

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **`Σ₁` truth naming, upper bound with explicit input length.** One fixed
partial recursive function `g` outputs every number named by a true `Σ₁`
formula of size at most `n`, on some input of fewer than
`4·n·(log₂(n+16)+1)` bits. -/
theorem TruthBig_sigma1_compact :
    ∃ g : ℕ →. ℕ, Partrec g ∧ ∀ n m, m ∈ truthValues 𝚺 1 n →
      ∃ x, Nat.log2 x < 4 * n * (Nat.log2 (n + 16) + 1) ∧ m ∈ g x := by
  obtain ⟨g, hg, hs⟩ := exists_truth_search
  refine ⟨fun x => g (compactDecode x), hg.comp primrec_compactDecode.to_comp, ?_⟩
  rintro n m ⟨φ, hφ, hsz, hm⟩
  refine ⟨compactCode φ, ?_, by simpa [compactDecode_compactCode] using hs φ m hφ hm⟩
  have h := log2_compactCode_lt φ
  have hb : cbase φ + 1 ≤ n + 16 := by unfold cbase; omega
  have hl := log2_mono hb
  calc _ < _ := h
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hsz) (by omega)

end RayoBoolos

#print axioms RayoBoolos.TruthBig_sigma1_compact
