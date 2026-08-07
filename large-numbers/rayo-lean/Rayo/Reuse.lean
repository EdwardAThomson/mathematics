/-
`Rayo.Reuse` — a "program" language on top of `Rayo.Formula` that lets a
formula *reference* an earlier named definition instead of fully respelling
it, plus the expansion semantics that reduces a program back to an ordinary,
fully self-contained `Formula`.

## Design (stated and justified, per `rayo-notes/convention-notes.md`'s own
practice of flagging definitional choices)

**`Formula'`** extends `Formula` with one new constructor:

    | ref : Nat → Nat → Formula'

`ref i t` means "invoke the predicate named `i` at variable `t`" — i.e. plug
`t` in for the one free variable of definition `i`'s body. `Formula'` is a
strict superset of `Formula`'s five constructors (`mem`, `eq`, `neg`, `conj`,
`all`), reproduced verbatim so every existing `Formula` embeds into
`Formula'` with no `ref` nodes.

**`Program`** is a list of named definitions plus a final target:

    structure Program where
      defs  : List (Nat → Formula')
      final : Formula'

Each definition is represented directly as a Lean function `Nat → Formula'`
from its one "self" variable to its body, rather than as a `Formula'` term
paired with a distinguished parameter number. This is a definitional choice
(flagged, arbitrary but stated, exactly as `convention-notes.md` flags its
own choices):

* It mirrors the *existing* mechanization style already used throughout
  `K2.lean`-`K6.lean` (`zF`, `oneF`, `twoF`, `threeF`, `fourF`, `fiveF` are
  all Lean functions `Nat → Formula` from a "self" variable to a body, not
  `Formula` terms with a placeholder substituted in after the fact). Using
  the same shape here means definition bodies can be built by direct
  application (`d t`) rather than by a generic capture-avoiding substitution
  operation on `Formula'`, which would need its own correctness lemmas about
  free/bound variables that the project does not otherwise need.
* Each definition's *internal* bound variables (used inside its own body,
  distinct from the one "self" parameter) are hard-coded at fixed,
  per-definition-index numeric blocks disjoint from every other
  definition's block and from the range of "self"/witness variables ever
  used as an argument — exactly the convention `K4.lean` already
  establishes for `threeF` ("fixed bound-variable block 6..33", justified
  there as "a mechanization-only convenience that does not affect the
  convention symbol count", `notes/convention-notes.md` §4: variable
  identity and index are free). Reusing the *same* fixed internal block at
  every call site of a given definition is safe: each occurrence of a
  definition's body sits under its own quantifiers, which locally shadow
  the block's names and never leak them free, so two unrelated occurrences
  of `ref 0 _` never interact even though both unfold using the same
  hard-coded internal variable names.

`ref` names are plain `Nat` indices into `defs` (position in the list), not
a distinct abstract `Name` type. A well-formed program only ever has
`ref i _` with `i` less than the index of the definition containing it (so
definitions form a DAG that is, in fact, a total order — each may only
reference *strictly earlier* ones), and `final` may reference any index
`< defs.length`. This ordering restriction is what makes expansion
terminate (see `expandN` below) and is exactly the "each number embeds all
the ones before it" recursive shape already visible in `K2.lean`-`K6.lean`.

## Semantics: expansion

`expandN defs bound f` expands a `Formula'` into an ordinary `Formula` by
unfolding every `ref` node, recursively. `bound` is the well-formedness
ceiling on legal reference targets at the current expansion point: only
`ref i _` with `i < bound` (and `i` a legal index into `defs`) is unfolded
by looking up `defs[i]` and continuing expansion of the result with a
*strictly smaller* ceiling `i` — this is what turns "definitions may only
reference strictly earlier ones" into a decreasing measure and makes the
recursion well-founded (Lean checks this via the lexicographic measure
`(bound, sizeOf f)`: the `ref` case strictly decreases `bound`; every other
case leaves `bound` unchanged and strictly decreases the `Formula'`
subterm). A `ref` that is out of range (self- or forward-reference, or an
unknown index) is not well-formed input and is never produced by any
program built below; `expandN` still needs a total, terminating value for
it and returns the fixed fallback formula `Formula.eq 0 0` ("0 = 0", always
true, chosen only so the function is total — it never actually arises).

`expand p := expandN p.defs p.defs.length p.final` expands a whole program:
the final target may reference any definition in the list, and each
definition's own body is itself expanded (recursively, through further
`ref`s) as soon as it is unfolded.
-/

import Rayo.Syntax

namespace Rayo

/-- `Formula'` — `Formula` plus one new constructor, `ref i t`: "invoke
named definition `i` at variable `t`" rather than respelling its body. -/
inductive Formula' where
  | mem  : Nat → Nat → Formula'
  | eq   : Nat → Nat → Formula'
  | neg  : Formula' → Formula'
  | conj : Formula' → Formula' → Formula'
  | all  : Nat → Formula' → Formula'
  | ref  : Nat → Nat → Formula'
  deriving Repr

/-- A reuse-program: a list of named definitions (each a function from its
one "self" variable to a `Formula'` body, which may `ref` any strictly
earlier definition — see the file header) plus a final target `Formula'`,
which may `ref` any definition in the list. -/
structure Program where
  defs  : List (Nat → Formula')
  final : Formula'

/-- Expand a `Formula'` into an ordinary `Formula`, unfolding every `ref`
node by looking it up in `defs` and recursively expanding the result, under
the decreasing well-formedness ceiling `bound` (see the file header). -/
def expandN : List (Nat → Formula') → Nat → Formula' → Formula
  | _defs, _bound, .mem i j => .mem i j
  | _defs, _bound, .eq i j  => .eq i j
  | defs,  bound,  .neg f   => .neg (expandN defs bound f)
  | defs,  bound,  .conj f g => .conj (expandN defs bound f) (expandN defs bound g)
  | defs,  bound,  .all n f => .all n (expandN defs bound f)
  | defs,  bound,  .ref i t =>
      if h : i < bound ∧ i < defs.length then
        expandN defs i ((defs[i]'h.2) t)
      else
        .eq 0 0
termination_by _defs bound f => (bound, sizeOf f)
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Expand a whole `Program` into an ordinary, fully self-contained
`Formula`: expand `final` against the full definition list, with ceiling
`defs.length` (every definition is a legal reference target from the final
target). -/
def expand (p : Program) : Formula :=
  expandN p.defs p.defs.length p.final

/-! ### Expansion equations

These restate `expandN`'s defining equations as ordinary theorems, usable by
`rw`/`simp` without ever forcing `defs`/`bound`/`f` to reduce to fully
concrete literals first (unlike `simp [expandN]` on its own, which only
fires once the scrutinees are already in constructor form). This is what
lets the correctness proofs in `ReuseSix.lean` push `Sat`/`expandN` inward
compositionally, exactly the way `Rayo.exists_member_iff` /
`Rayo.forall_member_not_bad` (`K3.lean`) already let the K-files push `Sat`
inward without hand-unfolding every occurrence. -/

theorem expandN_mem (defs : List (Nat → Formula')) (bound i j : Nat) :
    expandN defs bound (.mem i j) = .mem i j := by simp [expandN]

theorem expandN_eqf (defs : List (Nat → Formula')) (bound i j : Nat) :
    expandN defs bound (.eq i j) = .eq i j := by simp [expandN]

theorem expandN_neg (defs : List (Nat → Formula')) (bound : Nat) (f : Formula') :
    expandN defs bound (.neg f) = .neg (expandN defs bound f) := by simp [expandN]

theorem expandN_conj (defs : List (Nat → Formula')) (bound : Nat) (f g : Formula') :
    expandN defs bound (.conj f g) = .conj (expandN defs bound f) (expandN defs bound g) := by
  simp [expandN]

theorem expandN_all (defs : List (Nat → Formula')) (bound n : Nat) (f : Formula') :
    expandN defs bound (.all n f) = .all n (expandN defs bound f) := by simp [expandN]

/-- The key `ref`-unfolding equation: expanding `ref i t` under ceiling
`bound` (with `i` a legal, in-range target, `i < bound`) is the same as
looking up definition `i`, applying it to `t`, and continuing expansion with
the strictly smaller ceiling `i` (definition `i` may itself only reference
indices `< i`). -/
theorem expandN_ref (defs : List (Nat → Formula')) (bound i t : Nat)
    (h1 : i < bound) (h2 : i < defs.length) :
    expandN defs bound (.ref i t) = expandN defs i ((defs[i]'h2) t) := by
  simp [expandN, h1, h2]

/-! ### Symbol cost

The cost function for `Formula'`, under the same per-occurrence convention
as `rayo-notes/convention-notes.md` (mirrored in `Formula`'s cost, computed
by hand throughout `K0.lean`-`K6.lean`): an atomic `mem`/`eq` node costs 3
(two variable occurrences + one binary relation symbol); `¬φ` costs `|φ|+3`
(the `¬` symbol plus its mandatory wrapping parens); `(φ ∧ ψ)` costs
`|φ|+|ψ|+3` (the `∧` symbol plus its wrapping parens); `∀v(φ)`/`∃v(φ)` costs
`|φ|+4` (the quantifier symbol, the bound variable, plus its wrapping
parens).

**`ref i t` costs 2 — stated and justified, an arbitrary-but-principled
choice in the same spirit `convention-notes.md` flags its own choices.** We
treat a reference to a named definition as a fresh *unary* relation symbol
(`Pᵢ`) applied to its one argument variable — the same shape as how the
convention already prices the two *binary* primitive relation symbols
`∈`/`=`: an atomic occurrence of a relation of arity `n` costs `n` variable
occurrences plus 1 for the relation symbol itself, i.e. `n + 1`. For `∈`/`=`
(arity 2) that formula gives `2 + 1 = 3`, exactly `convention-notes.md`'s
stated atom cost. Generalizing the same `n + 1` rule to a unary reference
(arity 1: one argument variable, no "self" variable spelled out at the call
site) gives `1 + 1 = 2`. This is the cost charged **at every call site**;
the referenced definition's own body is priced once, separately (see
`Program.cost` below) — that separation is exactly the point of the
mechanism this file builds. -/
def costF' : Formula' → Nat
  | .mem _ _  => 3
  | .eq _ _   => 3
  | .neg f    => costF' f + 3
  | .conj f g => costF' f + costF' g + 3
  | .all _ f  => costF' f + 4
  | .ref _ _  => 2

/-- The cost of a whole `Program`: each named definition's body is priced
once (`costF'` applied to the body — the specific "self" variable supplied
does not affect the count, since `costF'` never inspects variable identity,
matching `convention-notes.md` §4's "variable identity is free"), summed
over the definition list, plus the cost of the final target. A call site
that references definition `i` never re-adds definition `i`'s own body
cost — only the fixed 2-symbol `ref` cost above — which is exactly the
"charge each definition once, not once per reference" requirement this
mechanism exists to satisfy. -/
def Program.cost (p : Program) : Nat :=
  (p.defs.map (fun d => costF' (d 0))).sum + costF' p.final

/-- The marginal cost of the final target alone, *assuming* every
definition in `p.defs` already exists (i.e. excluding their one-time
definition cost) — directly comparable to `RAYO-EXPLAINER.md`'s "~161
symbols... if φ₀-φ₅ already exist as reusable definitions" estimate. -/
def Program.marginalCost (p : Program) : Nat :=
  costF' p.final

end Rayo
