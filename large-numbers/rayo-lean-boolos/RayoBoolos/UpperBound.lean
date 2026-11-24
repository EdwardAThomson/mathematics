/-
`RayoBoolos.UpperBound`: the upper half of the sandwich, and full
independence of the axioms.

For a consistent, computably axiomatized `T ⊇ 𝗣𝗔⁻` (`[T.Δ₁]`), proof search
is a partial recursive function: given the code of the formula
`nameTemplate φ (y) := ∀x (φ(x) ↔ x = y)` it looks for a `k` with
`T ⊢ nameTemplate φ (k̄)` (`exists_search`). Feeding that function to
`BoolosBigIn_partrec_bound` gives `BoolosBigIn_le_any`:

    BoolosBigIn T n ≤ BoolosBigIn U (C + 6·log₂ (templateCode n))

for every consistent `U ⊇ 𝗣𝗔⁻`, where `templateCode n` is the largest Gödel
number of a naming template for a formula of size at most `n` and does not
depend on `T` or `U`. So any two such theories have the same provable-naming
function up to one fixed rescaling of the argument plus a constant.

Not proved here: an explicit bound on `templateCode n`. With an efficient
encoding it is `2^{O(n log n)}`; `Foundation`'s encoding uses nested pairing
and is larger.
-/

module

public import RayoBoolos.BusyBeaver

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic
open Bootstrapping Bootstrapping.Arithmetic

section
variable (T : ArithmeticTheory) [T.Δ₁]

/-- `ProvAt T x k`: `x` codes a formula `N` with one free variable, and `T`
proves `N(k̄)`. -/
def ProvAt (x k : ℕ) : Prop :=
  IsSemiformula ℒₒᵣ 1 x ∧ Provable T (subst ℒₒᵣ ?[numeral k] x)

lemma provAt_sigma1 : 𝚺₁-Relation (ProvAt T) := by
  unfold ProvAt; definability

lemma provAt_spec (N : ArithmeticSemisentence 1) (k : ℕ) :
    ProvAt T ⌜N⌝ k ↔ T ⊢ (N/[↑k] : ArithmeticSentence) := by
  simp [ProvAt, ←provable_iff_provable, Sentence.quote_def,
    Rewriting.emb_subst_eq_subst_coe₁, Semiformula.quote_def]

lemma provAt_re : REPred fun p : ℕ × ℕ => ProvAt T p.1 p.2 := by
  obtain ⟨φ, hφ⟩ := provAt_sigma1 T
  have hRe : REPred fun p : ℕ × ℕ ↦
      φ.val.Eval (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2).get id :=
    (sigma1_re id φ.sigma_prop).comp
      (Primrec.to_comp <| Primrec.vector_cons.comp .fst
        (Primrec.vector_cons.comp .snd (.const List.Vector.nil)))
  exact hRe.of_eq fun p => by simpa [List.Vector.cons_get] using hφ ![p.1, p.2]

end

open Nat.Partrec (Code) in
/-- Selection: from a recursively enumerable relation, a partial recursive
function that picks a witness whenever one exists. -/
lemma re_select {P : ℕ × ℕ → Prop} (hP : REPred P) :
    ∃ g : ℕ →. ℕ, Partrec g ∧ (∀ x v, v ∈ g x → P (x, v)) ∧
      (∀ x k, P (x, k) → (g x).Dom) := by
  obtain ⟨h, hh, rfl⟩ := REPred.iff.mp hP
  have h1 : Partrec (fun n : ℕ => (h n.unpair).map fun _ => (0 : ℕ)) :=
    (hh.comp Computable.unpair).map (Computable.const 0).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp h1)
  let F : ℕ → ℕ → Option ℕ := fun x m =>
    (Code.evaln m.unpair.2 c (Nat.pair x m.unpair.1)).map fun _ => m.unpair.1
  have hF : Computable₂ F := by
    have e : Computable fun p : ℕ × ℕ => Code.evaln p.2.unpair.2 c (Nat.pair p.1 p.2.unpair.1) :=
      Code.primrec_evaln.to_comp.comp
        (((Computable.snd.comp (Computable.unpair.comp Computable.snd)).pair (Computable.const c)).pair
          (Primrec₂.natPair.to_comp.comp Computable.fst
            (Computable.fst.comp (Computable.unpair.comp Computable.snd))))
    exact (Computable.option_map e
      ((Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))).to₂)).to₂
  refine ⟨fun x => Nat.rfindOpt (F x), Partrec.rfindOpt hF, ?_, ?_⟩
  · intro x v hv
    obtain ⟨m, hm⟩ := Nat.rfindOpt_spec hv
    simp only [F, Option.mem_def, Option.map_eq_some_iff] at hm
    obtain ⟨u, hu, rfl⟩ := hm
    have := Code.evaln_sound hu
    rw [hc] at this
    have this' : u ∈ (h (Nat.pair x m.unpair.1).unpair).map fun _ => (0 : ℕ) := this
    rw [Nat.unpair_pair] at this'
    obtain ⟨_, ⟨hdom, _⟩, _⟩ := (Part.mem_map_iff _).mp this'
    exact hdom
  · intro x k hk
    have hmem : (0 : ℕ) ∈ Code.eval c (Nat.pair x k) := by
      rw [hc]
      show (0 : ℕ) ∈ (h (Nat.pair x k).unpair).map fun _ => (0 : ℕ)
      rw [Nat.unpair_pair]
      exact (Part.mem_map_iff _).mpr ⟨(), ⟨hk, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := Code.evaln_complete.mp hmem
    apply Nat.rfindOpt_dom.mpr
    refine ⟨Nat.pair k s, k, ?_⟩
    show (Code.evaln (Nat.pair k s).unpair.2 c (Nat.pair x (Nat.pair k s).unpair.1)).map
      (fun _ => (Nat.pair k s).unpair.1) = some k
    rw [Nat.unpair_pair, Option.mem_def.mp hs]
    rfl

/-- The naming condition as a formula in the named value:
`nameTemplate φ (y)` is `∀x (φ(x) ↔ x = y)`. -/
noncomputable def nameTemplate (φ : ArithmeticSemisentence 1) : ArithmeticSemisentence 1 :=
  “y. ∀ x, !φ x ↔ x = y”

lemma eval_nameTemplate {M : Type} [ORingStructure M] (φ : ArithmeticSemisentence 1) (a : M) :
    (nameTemplate φ).Evalb (M := M) ![a] ↔ ∀ x : M, φ.Evalb (M := M) ![x] ↔ x = a := by
  simp [nameTemplate, Semiformula.eval_substs]

lemma template_iff (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSemisentence 1) (k : ℕ) :
    T ⊢ ((nameTemplate φ)/[↑k] : ArithmeticSentence) ↔ NamesIn T φ k := by
  have key : ∀ (M : Type) [ORingStructure M],
      (M↓[ℒₒᵣ] ⊧ ((nameTemplate φ)/[↑k] : ArithmeticSentence)) ↔ (M↓[ℒₒᵣ] ⊧ namesSentence φ k) := by
    intro M _
    simp [namesSentence, models_iff, Semiformula.eval_substs, eval_nameTemplate]
  unfold NamesIn
  constructor
  · intro h
    exact Arithmetic.complete.{0} T _ (fun (M : Type) _ hM ↦ (key M).mp (models_of_provable hM h))
  · intro h
    exact Arithmetic.complete.{0} T _ (fun (M : Type) _ hM ↦ (key M).mpr (models_of_provable hM h))

/-- The largest Gödel number of a naming template for a formula of size at
most `n`. This does not depend on any theory. -/
noncomputable def templateCode (n : ℕ) : ℕ :=
  (formsUpTo_finite n 1).toFinset.sup fun φ => Encodable.encode (nameTemplate φ)

/-- **Proof search.** For a computably axiomatized consistent `T ⊇ 𝗣𝗔⁻` there
is a partial recursive function `g` which, given the code of the naming
template of `φ`, returns the number `φ` names in `T` whenever there is one. -/
theorem exists_search (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    ∃ g : ℕ →. ℕ, Partrec g ∧ ∀ (φ : ArithmeticSemisentence 1) (k : ℕ),
      NamesIn T φ k → k ∈ g (Encodable.encode (nameTemplate φ)) := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ (𝗣𝗔⁻ : ArithmeticTheory)) inferInstance
  obtain ⟨g, hg, hsound, hdom⟩ := re_select (provAt_re T)
  refine ⟨g, hg, fun φ k hk => ?_⟩
  have hcode : (⌜nameTemplate φ⌝ : ℕ) = Encodable.encode (nameTemplate φ) :=
    Sentence.quote_eq_encode_nat _
  have hP : ProvAt T (Encodable.encode (nameTemplate φ)) k := by
    rw [← hcode]; exact (provAt_spec T _ k).mpr ((template_iff T φ k).mpr hk)
  have hd := hdom _ k hP
  have hv := hsound _ _ (Part.get_mem hd)
  have hv' : ProvAt T ⌜nameTemplate φ⌝ ((g (Encodable.encode (nameTemplate φ))).get hd) := by
    rw [hcode]; exact hv
  have hname := (template_iff T φ _).mp ((provAt_spec T _ _).mp hv')
  have : (g (Encodable.encode (nameTemplate φ))).get hd = k := NamesIn.unique hname hk
  rw [← this]; exact Part.get_mem hd

/-- **The upper bound, and full independence of the axioms.** Let `T` be
consistent, computably axiomatized, and contain `𝗣𝗔⁻`. There is a constant
`C` such that for every consistent `U ⊇ 𝗣𝗔⁻` and every `n`,
`BoolosBigIn T n ≤ BoolosBigIn U (C + 6·log₂ (templateCode n))`. -/
theorem BoolosBigIn_le_any (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    ∃ C, ∀ (U : ArithmeticTheory) [𝗣𝗔⁻ ⪯ U] [Entailment.Consistent U],
      ∀ n, BoolosBigIn T n ≤ BoolosBigIn U (C + 6 * Nat.log2 (templateCode n)) := by
  obtain ⟨g, hg, hsearch⟩ := exists_search T
  obtain ⟨C, hC⟩ := BoolosBigIn_partrec_bound hg
  refine ⟨C, fun U _ _ n => ?_⟩
  apply BoolosBigIn_le
  rintro k ⟨φ, hφ, hk⟩
  have hle : Encodable.encode (nameTemplate φ) ≤ templateCode n :=
    Finset.le_sup (f := fun φ => Encodable.encode (nameTemplate φ))
      ((Set.Finite.mem_toFinset _).mpr hφ)
  have hmono : C + 6 * Nat.log2 (Encodable.encode (nameTemplate φ)) ≤
      C + 6 * Nat.log2 (templateCode n) := by
    have := log2_mono hle; omega
  exact le_trans (hC U _ k (hsearch φ k hk)) (BoolosBigIn_mono hmono)

/-- The upper bound for `𝗣𝗔`: every consistent `U ⊇ 𝗣𝗔⁻`, however weak,
catches up with `BoolosBig_PA` after the fixed rescaling. -/
theorem BoolosBig_PA_le_any :
    ∃ C, ∀ (U : ArithmeticTheory) [𝗣𝗔⁻ ⪯ U] [Entailment.Consistent U],
      ∀ n, BoolosBig_PA n ≤ BoolosBigIn U (C + 6 * Nat.log2 (templateCode n)) := by
  obtain ⟨C, hC⟩ := BoolosBigIn_le_any 𝗣𝗔
  exact ⟨C, fun U _ _ n => by rw [← BoolosBigIn_PA]; exact hC U n⟩

end RayoBoolos

#print axioms RayoBoolos.exists_search
#print axioms RayoBoolos.BoolosBigIn_le_any
#print axioms RayoBoolos.BoolosBig_PA_le_any
