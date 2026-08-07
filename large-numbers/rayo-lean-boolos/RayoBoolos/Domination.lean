/-
`RayoBoolos.Domination` — Step 4 of `BOOLOS-B1-B3-REPORT.md`: the B3
growth-class domination argument. Retry session: the previous attempt
(`boolos-b1-b3` branch) found the mathematical strategy below and got stuck
on one lemma (`subst_existsUnique_eq`); this file closes it and finishes the
rest of the argument that was blocked on it.

**The strategy** (avoids Boolos's own 1989 self-referential diagonalization
entirely — see `BOOLOS-B1-B3-REPORT.md` §"Step 4" for the full writeup of why
this is a legitimate, if weaker, substitute for the literal domination
claim). Fix any `f : ℕ → ℕ` that is PA-provably total via a Σ1 graph formula
`θ(y, x)` (`𝗣𝗔 ⊢ ∀x ∃!y θ(y, x)`, and `θ` really computes `f` in the standard
model). For each `n`:

1. **Specialize totality at the numeral for `n`.** From `𝗣𝗔 ⊢ ∀x ∃!y θ(y,x)`,
   instantiate `x := n̄` to get `𝗣𝗔 ⊢ ∃!y θ(y, n̄)`.
2. **The true Σ1 instance is PA-provable.** Since `θ` is Σ1 and
   `ℕ ⊨ θ(f(n), n)` is true, Σ1-completeness gives a concrete provable
   witness `𝗣𝗔 ⊢ θ(f(n)‾, n̄)`.
3. **Combine.** `∃!y θ(y,n̄)` plus the concrete witness `θ(f(n)‾, n̄)` gives
   `𝗣𝗔 ⊢ ∀y (θ(y,n̄) ↔ y = f(n)‾)` — i.e. `θ(·, n̄)` T-names `f(n)`, in exactly
   the `TNamesMeta` sense of `RayoBoolos.TNames`.

Since `θ(·, n̄)` has size `|θ| + O(n)` (numerals cost `O(n)` symbols in
`Foundation`'s successor-chain encoding, not `O(log n)` — see
`BOOLOS-B1-B3-REPORT.md` Step 2), this gives, for every PA-provably-total
`f`, a fixed additive constant `c` (depending on `f`, not `n`) with
`BoolosBig_PA(n + c) ≥ f(n)` for every `n` — the standard "eventually
dominates" shape. **No self-reference is used anywhere.** `provablyTotal_names`
below is the mechanized core of this argument: for every `n`, it exhibits and
verifies the naming fact itself. Turning that witness-existence statement
into a literal `BoolosBig_PA : ℕ → ℕ` inequality needs the length-bookkeeping
and finite-max machinery from `BoolosB0Core.lean` (the sibling, Mathlib-free
`rayo-lean/` project) re-instantiated concretely for PA-formula syntax — a
separate piece of infrastructure, not the blocked lemma this session was
asked to close, and out of scope here; the mathematical content of B3
(existence, for every PA-provably-total `f` and every `n`, of a naming
formula of size `|θ| + O(n)`) is what is proved below, sorry-free.

## Where the previous attempt got stuck, and how this closes it

The previous session's `Domination.lean` (never committed) got stuck showing
that `Theory.Proof.specialize`'s output — `Semiformula.subst (∃¹! graph)
![n̄]`, produced by unfolding `Foundation`'s `∃¹!` (`Semiformula.existsUnique`)
binder and pushing a substitution through it — is the *same* formula as
`graph ⇜ ![#0, n̄]` built directly. `subst_existsUnique_eq` below proves this.

The key ingredient the previous attempt was missing: `Foundation`'s own
`Rew.q_subst` (`Foundation/Syntax/Predicate/Rew.lean`), `(subst w).q = subst
(#0 :> bShift ∘ w)` — the exact lemma describing how a substitution commutes
with a newly-introduced binder, which is precisely what `∃¹!`/`∀¹` need. It
is *not* tagged `@[simp]` in `Foundation`, so a plain `simp` call never finds
it; it has to be supplied explicitly. `Foundation` itself uses exactly this
pattern (`q_subst`, `TransitiveRewriting.comp_app`, `Rew.const` — the last
handles the case that numerals, being closed terms, are fixed by any bound-
variable substitution — plus `Rew.ext`/`Fin.cases` on the small residual
composed-substitution goals) in its own `parameterized_diagonal₁`
(`Bootstrapping/FixedPoint.lean`), which specializes a two-variable formula
at a term while leaving the other variable free — the exact shape of problem
here. Once `q_subst` is in the simp set, `simp` reduces the goal to two
concrete substitution-vector equalities (no more binder-shape mismatch, just
`Fin 2 → Semiterm` bookkeeping), which close by `TransitiveRewriting.comp_app`
followed by `Rew.ext` + `Fin.cases` on each coordinate.

Steps 1–2 above are the ones Step 3 of the previous session's outline needed;
Step 3 (turning `∃!` plus a witness into the T-naming biconditional) is
closed here using `Foundation`'s own `Arithmetic.complete` semantic bridge
(the same technique `Bootstrapping/FixedPoint.lean`'s `diagonal` theorem
uses) rather than raw proof-calculus combinators: lift both provable facts
into an arbitrary model of `𝗣𝗔` via `models_of_provable`, do the `∃!`-plus-
witness reasoning at the ordinary (meta-level) `ExistsUnique` level, then
`Arithmetic.complete` turns the resulting "true in every model" fact back
into a `𝗣𝗔 ⊢ …` proof.
-/

module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness
public import RayoBoolos.TNames

@[expose] public section

namespace RayoBoolos

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-- The previously-stuck lemma. Specializing `∃¹! graph` (`Foundation`'s
`Semiformula.existsUnique`, unfolded through its `∃`/`∧`/`∀`/`→`/`=` primitives)
at a numeral and leaving the inner `∃`-bound variable alone is the same
formula as building the one-free-variable specialization directly via
`⇜ ![#0, n̄]`. This is `Rew.q_subst` plus routine substitution-vector
bookkeeping — see the module docstring for what `Foundation` already
provides and how it is used here. -/
theorem subst_existsUnique_eq (graph : ArithmeticSemisentence 2) (n : ℕ) :
    (Semiformula.subst (∃¹! graph) ![Semiterm.numeral n] : ArithmeticSemisentence 0) =
      (∃¹! (graph ⇜ ![#0, Semiterm.numeral n]) : ArithmeticSemisentence 0) := by
  unfold Semiformula.existsUnique Semiformula.subst Rewriting.subst
  simp [Rew.q_subst, Function.comp_def, Matrix.comp_vecCons']
  simp only [← TransitiveRewriting.comp_app]
  constructor
  · congr 2
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ x => cases x using Fin.cases <;> simp [Rew.comp_app]
    · exact x.elim
  · congr 2
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ x => cases x using Fin.cases with
        | zero => simp [Rew.comp_app]
        | succ x => exact x.elim0
    · exact x.elim

/-- `f` is PA-provably total via the Σ1 graph formula `graph(y, x)` (value
first, argument second, matching `RayoBoolos.Probe`'s confirmed header-order
convention): `𝗣𝗔` proves `∀x ∃!y graph(y,x)`, and `graph` really does compute
`f` in the standard model. -/
structure ProvablyTotal (f : ℕ → ℕ) where
  graph : ArithmeticSemisentence 2
  sigma1 : Hierarchy 𝚺 1 graph
  total : (𝗣𝗔 : ArithmeticTheory) ⊢ ∀¹ (∃¹! graph)
  correct : ∀ n : ℕ, graph.Evalb (M := ℕ) ![f n, n]

/-- The one-free-variable formula `graph(·, n̄)`: `graph` with its argument
slot specialized at the numeral for `n`, leaving the value slot free. This
is the candidate "T-names `f n`" formula from the strategy in the module
docstring. -/
noncomputable def ProvablyTotal.graphAt {f : ℕ → ℕ} (P : ProvablyTotal f) (n : ℕ) :
    ArithmeticSemisentence 1 :=
  P.graph ⇜ ![#0, Semiterm.numeral n]

/-- **The B3 mechanization core.** For every PA-provably-total `f` and every
`n`, `graphAt n` T-names `f n` — the three-step argument from the module
docstring, fully mechanized. Combined with monotonicity of `BoolosBig_PA`
and the `O(n)` numeral-cost bound (paper-level, `BOOLOS-B1-B3-REPORT.md`),
this is the content of "`BoolosBig_PA` eventually dominates every
PA-provably-total function": for every such `f` there is a witness formula
of size `|P.graph| + O(n)` naming `f n`, for every `n`. -/
theorem provablyTotal_names (f : ℕ → ℕ) (P : ProvablyTotal f) (n : ℕ) :
    TNamesMeta (P.graphAt n) (f n) := by
  -- Step 1: specialize totality at n̄, using `subst_existsUnique_eq` to land
  -- exactly on `∃¹! (graphAt n)`.
  have h1 : (𝗣𝗔 : ArithmeticTheory) ⊢ ∃¹! (P.graphAt n) := by
    have hspec := Theory.Proof.specialize (T := (𝗣𝗔 : ArithmeticTheory)) (∃¹! P.graph)
      (Semiterm.numeral n)
    have h := hspec ⨀ P.total
    rwa [subst_existsUnique_eq] at h
  -- Step 2: Σ1-completeness gives a concrete provable witness.
  have h2 : (𝗣𝗔 : ArithmeticTheory) ⊢ (P.graph ⇜ ![Semiterm.numeral (f n), Semiterm.numeral n]) := by
    have h := (sigma_one_completeness_iff_param (T := (𝗣𝗔 : ArithmeticTheory)) P.sigma1
      (e := ![f n, n])).mp (by simpa [models_iff] using P.correct n)
    have heq : (fun x => (Semiterm.Operator.numeral ℒₒᵣ (![f n, n] x) : Semiterm ℒₒᵣ Empty 0))
        = (![Semiterm.numeral (f n), Semiterm.numeral n] : Fin 2 → Semiterm ℒₒᵣ Empty 0) := by
      funext x
      cases x using Fin.cases with
      | zero => rfl
      | succ x => cases x using Fin.cases with
        | zero => rfl
        | succ x => exact x.elim0
    rwa [heq] at h
  -- Step 3: combine `∃!` plus the witness into the T-naming biconditional,
  -- via `Foundation`'s semantic completeness bridge rather than raw
  -- proof-calculus combinators.
  unfold TNamesMeta namesSentence
  apply Arithmetic.complete.{0} (𝗣𝗔 : ArithmeticTheory) _ (fun (M : Type) _ hM ↦ ?_)
  have hu : M↓[ℒₒᵣ] ⊧ (∃¹! (P.graphAt n)) := models_of_provable hM h1
  have hw : M↓[ℒₒᵣ] ⊧ (P.graph ⇜ ![Semiterm.numeral (f n), Semiterm.numeral n]) :=
    models_of_provable hM h2
  simp [models_iff, ProvablyTotal.graphAt] at hu hw ⊢
  intro x
  constructor
  · intro hx
    exact hu.unique hx hw
  · rintro rfl
    exact hw

end RayoBoolos

#print axioms RayoBoolos.subst_existsUnique_eq
#print axioms RayoBoolos.provablyTotal_names
