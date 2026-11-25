# Second-order Rayo: naming with classes

Written 2026-11-24, from the questions "what if we allow more expressive
languages than first-order set theory?" and "what could we do with
second-order set theory?" It defines the second-order analogue of Rayo's
function, shows that it beats Rayo's function and the whole "Rayo+" family
of iterated truth predicates, and says what it costs to believe in it.

Tags as in the rest of the project: **[paper]** argued here and not
independently checked, **[classical]** a known result cited from memory,
**[expected]** believed true but not proved here, **[open]**. Nothing here
is machine-checked. Written in one pass; not yet re-read.

> **Update 2026-11-24 (second pass).** Re-read in `SECOND-ORDER-RAYO-II.md`.
> Theorem 1 stands. Theorem 2 stands after a repair: use one truth predicate
> with the stage as an argument, not one symbol per ordinal. Two corrections:
> §5's "Henkin semantics breaks Theorem 1" is wrong, because definable
> classes give exactly the first Rayo+ step (Theorem A there). §4's "costs
> about an inaccessible" mixes belief, proof strength and one picture of
> classes (§3 there). Proposition 3 generalises: one more order equals one
> more powerset level (Theorem C there).

## 0. In plain language

Rayo's language talks about sets. Second-order set theory can also talk
about **classes**: arbitrary collections of sets, including ones too big to
be sets, such as "all sets" or "all ordinals". A formula may say "for every
class" or "there is a class".

1. **It beats Rayo.** One fixed formula can say "`T` is the class of true
   first-order statements (with their assignments)". Exactly one class fits
   that description. A short formula can then say "one more than the
   largest number named by a first-order formula of at most `n` symbols".
   So second-order naming beats Rayo's function, at the cost of a constant
   plus the length of `n` written in binary (Theorem 1).
2. **It swallows the "Rayo+" family.** Adding a truth predicate, then a truth
   predicate for the new language, and so on, even along a sequence as long
   as all the ordinals, can all be described by one class. So all of these
   sit inside one second-order language (Theorem 2).
3. **It costs more belief.** You need a fixed answer to "which classes
   exist?", namely all sub-collections of the universe. A clean picture: the
   universe of sets is `V_κ` for an inaccessible cardinal `κ`, inside a
   bigger universe, and classes are the subsets of `V_κ`. In that picture,
   second-order Rayo for `V_κ` is beaten by ordinary first-order Rayo for
   the bigger universe (§4). So a stronger *language* and a bigger
   *universe* are two ways of paying for the same step.
4. **The limits stay.** Second-order set theory has finitely many formulas
   of each size, so it has a record it cannot name (Claim A). Third-order set
   theory beats it (Claim B). There is no top.

## 1. Setting

**Language `L₂`.** Set variables `x, y, …` and class variables
`X, Y, …`; atoms `x ∈ y`, `x = y`, `x ∈ X`; connectives `¬`, `∧`;
quantifiers `∃x` and `∃X`. Size is symbol count, as for Rayo's language
(`RAYO-R0-WELLDEFINEDNESS.md` §1). `L₁` is Rayo's first-order language,
the fragment with no class variables.

**Semantics.** *Full* second-order semantics over the universe `V`: set
variables range over `V`, class variables over **all** sub-collections of
`V`. This is the reading under which Rayo's own definition of satisfaction
was given (one level down), and it is what makes the comparison below
meaningful. With *Henkin* semantics (classes range over some fixed
collection, such as the definable ones), the results change; see §5.

**Naming.** An `L₂` formula `φ(x)` with one free set variable and no free
class variables *names* `m ∈ ℕ` if `m` is the only set satisfying it. Let

```
N₁(n) := largest m named by an L₁ formula of size ≤ n     (so Rayo(n) = N₁(n) + 1)
N₂(n) := largest m named by an L₂ formula of size ≤ n.
```

Both are well defined given a definite truth notion for the language,
by the finiteness argument of `BN-function.md`. **[paper]** For `N₁` that
truth notion is the one `RAYO-R0-WELLDEFINEDNESS.md` discusses; for `N₂` it
is truth under full second-order semantics, discussed in §4.

`N₁(n) ≤ N₂(n)` trivially, since `L₁ ⊆ L₂`.

## 2. Theorem 1: second-order naming beats Rayo

**Lemma (first-order truth is one class).** There is an `L₂` formula
`Sat(T)` such that, under full semantics, exactly one class satisfies it:
the satisfaction relation of `L₁` over `V`, that is the class of pairs
`(⌜ψ⌝, s)` with `ψ` an `L₁` formula and `s` an assignment of sets to its
variables such that `V ⊨ ψ[s]`.

*Proof sketch.* Codes of formulas are hereditarily finite sets;
assignments are functions from finite sets of variable indices to `V`,
which are sets. `Sat(T)` lists Tarski's clauses: `(⌜x_i ∈ x_j⌝, s) ∈ T`
iff `s(i) ∈ s(j)`, likewise for `=`; negation and conjunction clauses; and
`(⌜∃x_i ψ⌝, s) ∈ T` iff some `s′` that differs from `s` at most at `i` has
`(⌜ψ⌝, s′) ∈ T`. Uniqueness: two classes obeying the clauses agree on
every formula, by induction on the formula. Existence: the true
satisfaction relation is a sub-collection of `V`, so under full semantics
it is a class. ∎ **[paper; classical in substance: this is the standard
fact that full second-order logic over `V` defines first-order truth]**

**Theorem 1.** There is a constant `c` with

```
N₂( c + 6·log₂(n+2) )  >  N₁(n)      for every n.
```

*Proof.* Let `ν_n(z)` be an `L₁` formula of size at most `c₀ + 6·log₂(n+2)`
that defines the von Neumann numeral `n`. It writes `n` in binary using
fixed definitions of `0`, successor and doubling on `ω`, as in `bin(n)` of
the Busy Beaver note. **[paper; constants not computed]** Let `ψ_n(x)` say:

> there is a class `T` with `Sat(T)`, and there is `z` with `ν_n(z)`, such
> that `x` is one more than the largest `k ∈ ω` for which some code `⌜φ⌝`
> of an `L₁` formula with one free variable and size `≤ z` satisfies:
> `(⌜φ⌝, k)` is in `T`, and no `k′ ≠ k` has `(⌜φ⌝, k′)` in `T`.

Everything after "there is a class `T`" is a fixed `L₂` formula apart from
`ν_n`. There are finitely many codes of size `≤ n`, so the largest such
`k` exists. By the Lemma, `T` is the true satisfaction relation, so that
largest `k` is `N₁(n)`, and `ψ_n` names `N₁(n) + 1`. Its size is at most
`c + 6·log₂(n+2)`. ∎ **[paper]**

This is Claim B of `THE-LADDER.md` §3 with `R = L₁` and `R⁺ = L₂`. By the
Lean form of Claim B (`record_lt_at_log_budget` in
`rayo-lean/Rayo/NoTop.lean`), `N₂` outgrows `N₁` by more than an
exponential stretch of the input. **[the abstract step is Lean; its
hypotheses here are paper]**

## 3. Theorem 2: the Rayo+ family is inside one second-order language

`THE-LADDER.md` places "Rayo+" above Rayo: add a predicate `Tr` for truth
of `L₁`, take naming in `L₁ + Tr`, then add truth for that language, and
repeat. Write `L^α` for the language obtained by iterating this `α` times,
for an ordinal `α`, with predicates `Tr_β` (`β < α`) where `Tr_β` is truth
for `L^β`. Let `N^α` be its naming function. (Fish number 7 is a version of
this construction. Its exact definition has not been checked against this
one. **[expected]**)

**Theorem 2.** Let `α` be an ordinal, or the class of all ordinals, defined
by an `L₂` formula `δ` without parameters. There is a constant `c_δ` with

```
N₂( c_δ + 6·log₂(n+2) )  >  N^α(n)      for every n.
```

*Proof sketch.* Under full semantics, the whole sequence `⟨Tr_β : β < α⟩`
is a single class: the class of triples `(β, ⌜ψ⌝, s)` with `β < α` and
`ψ` true under `s` in the language `L^β`. It is characterized by one
`L₂` formula, `IterSat_δ(S)`, which says that each slice of `S` obeys
Tarski's clauses for `L^β`, reading the atoms `Tr_γ` (`γ < β`) off the
earlier slices. Uniqueness: by induction on `β`, and inside each `β` by
induction on formulas. This is legitimate even when `α` is all the
ordinals, because the ordinals are well-ordered. Existence: the true
iterated satisfaction relation is a sub-collection of `V`. Then argue as in
Theorem 1, reading names off the slices below `α`. ∎ **[paper]**

So every iterated-truth extension of Rayo's language whose length can be
described, including one as long as all the ordinals, is beaten by plain
second-order naming at a constant extra cost.

*Remark (provability versus truth).* This is about truth under full
semantics, not about what a class theory proves. Morse–Kelley class theory
(MK) may not *prove* that such iterated satisfaction classes exist for
class-length iterations: elementary transfinite recursion over classes is
not obviously available in MK, and work of Gitman, Hamkins and others on
class choice in MK bears on this. **[classical in outline; not checked;
see the paper cited in `RAYO-R0-WELLDEFINEDNESS.md`]** Under full semantics
the classes exist whether or not a given theory proves it.

## 4. What it costs, and how it meets the large cardinals

**What must be accepted.** To make `N₂` definite one needs a definite range
for the class quantifiers, namely all sub-collections of `V`, and a
definite truth notion for `L₂` over it. That is one level above Rayo's
commitment: Rayo needs definite truth for statements about sets, and `N₂`
needs definite truth for statements about all collections of sets.
**[paper]**

**The inaccessible picture.** There is a standard way to make this
concrete. Let `κ` be an inaccessible cardinal. Then `V_κ`, with
`V_{κ+1}` (the subsets of `V_κ`) as its classes, is a model of
second-order set theory under full semantics. Conversely, Zermelo showed
that every model of second-order ZF under full semantics is isomorphic
to some `V_κ` with `κ` inaccessible. **[classical: Zermelo 1930,
quasi-categoricity]** So believing in full second-order truth over the
universe is very close to believing that the universe is `V_κ`, for an
inaccessible `κ`, sitting inside something larger.

**Language versus universe.** In that picture there is a trade-off.

**Proposition 3.** Suppose `κ` is the least inaccessible cardinal. Let
`N₂^{V_κ}` be second-order naming with `V_κ` as the universe and
`V_{κ+1}` as its classes. Then there is a constant `c` with

```
N₁( c + 6·log₂(n+2) )  >  N₂^{V_κ}(n)      for every n,
```

where `N₁` is ordinary first-order Rayo naming in `V`.

*Proof sketch.* "The least inaccessible cardinal" is a fixed `L₁` formula.
In `V`, second-order truth over `(V_κ, V_{κ+1})` is an ordinary set: it is
defined by recursion on formulas inside `V_{κ+2}`. So "one more than the
largest number named by an `L₂` formula of size `≤ n` over `V_κ`" is an
`L₁` formula of size `c + 6·log₂(n+2)` in `V`. ∎ **[paper]**

So second-order Rayo for a small universe is beaten by first-order Rayo for
a bigger one. Climbing in *expressive power* and climbing in *size of
universe* are two prices for the same kind of step. This is where the size
ladder of `LARGE-CARDINALS-AND-THE-LADDER.md` and the naming ladder of
`THE-LADDER.md` interlock. **[paper]** The same proof with the least Mahlo
cardinal, least weakly compact cardinal and so on gives a chain of such
comparisons. **[expected]**

**Reflection.** Second-order statements over `V` can express reflection
principles: "every second-order statement true in `V` is true in some
`V_α`". A cardinal `κ` for which `V_κ` has such properties is
*indescribable*. The `Π¹₁`-indescribable cardinals are exactly the weakly
compact cardinals. **[classical: Hanf–Scott]** So which second-order
sentences are true over `V` depends on how "tall" `V` is, in the sense of
large-cardinal-like properties of the class of all ordinals. Second-order
naming is therefore sensitive to the height of the universe in a way that
first-order truth, by the Lévy–Montague reflection theorem, partly hides.
**[classical ingredients; the comment is ours, [expected]]**

## 5. The limits

- **Claim A.** `L₂` has finitely many formulas of each size and each names
  at most one number, so `N₂(n)` exists for each `n` and `L₂` cannot name
  `N₂(n) + 1` with a formula of size about `log n`. Second-order truth over
  `V` is not definable in `L₂` over `V`, by Tarski's theorem in its
  second-order form. **[classical for undefinability; Claim A is Lean in the
  abstract]**
- **Claim B, one step up.** Third-order set theory (quantifying over
  collections of classes) defines `L₂`-truth as one object, exactly as in
  the Lemma of §2, and beats `N₂` as in Theorem 1. **[paper; same
  argument]** Then fourth order, every finite order, a truth predicate for
  all finite orders, and so on. There is no top.
- **Henkin semantics.** If class variables range only over a fixed
  collection, such as the classes first-order definable with parameters,
  Theorem 1 fails. The satisfaction class is not definable (Tarski), so no
  class in range satisfies `Sat(T)`. Quantifying over definable classes
  amounts to quantifying over definitions, and reading membership off a
  definition uses first-order truth, so this `L₂` sits roughly between `L₁`
  and `L₁ + Tr`. Whether it is a new rung is unclear. Which semantics one
  picks is exactly the "what must be accepted" choice. **[expected]**
- **Overreach.** BIG FOOT tried to go further by positing a larger "oodle"
  universe above `V` with new primitive symbols. Its definition does not
  determine a number (`phase0/e-foot.md`). The step of §2 is safe because
  it adds only quantifiers over sub-collections of the existing universe,
  with Tarski's clauses fixing everything.

## 6. Open items

1. Re-read Theorems 1 and 2 and the Lemma, especially the uniqueness of
   iterated satisfaction classes along all the ordinals.
2. Compare Theorem 2 with the actual definition of Fish number 7.
3. Make Proposition 3 precise for the least Mahlo and weakly compact
   cardinals, and state the general pattern: which universe's first-order
   Rayo beats which universe's second-order Rayo.
4. Under Henkin semantics with definable classes, decide whether `N₂` is
   a new rung above `N₁`, and where it sits relative to `L₁ + Tr`.
5. Literature: second-order set theory and indescribability are classical.
   Not searched: whether "second-order Rayo" has been defined in googology
   sources.
