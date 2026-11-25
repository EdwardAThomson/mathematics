# Second-order Rayo, second pass: re-read, corrections, and order versus height

Written 2026-11-24 as a follow-up to `SECOND-ORDER-RAYO.md` (call it "the
first note"). It re-reads that note sceptically, corrects two of its claims,
and proves three new things: what the weak ("definable classes") reading of
second-order Rayo is worth, that one more order of language is the same as one
more powerset level of universe, and what tall, reflecting universes do to
naming. It also places Fish number 7 and records a literature check.

Tags as in the rest of the project: **[paper]** argued here and not
independently checked, **[classical]** a known result cited from memory or
from the source named, **[expected]** believed true but not proved here,
**[open]**. Nothing here is machine-checked. One pass, re-read once.

## 0. In plain language

1. **The first note's main theorems stand, with one repair.** "Classes beat
   Rayo" is right. In fact Rayo's own definition of his number already uses a
   class quantifier ("for every relation R ..."), so it is itself a short
   second-order formula. "Classes swallow the whole Rayo+ family" is right
   too, but the first note wrote the iterated languages with a separate symbol
   for each ordinal. That gives infinitely many formulas of some sizes, and the
   naming function would not exist. The fix is one truth predicate that takes
   the stage as an argument (§1.2).

2. **Correction: the weak reading of "class" does not break the theorem.**
   The first note said that if "class" only means "definable class",
   second-order naming falls apart. It doesn't. You never need the whole of
   truth at once, only truth for formulas up to the size you are looking at,
   and that piece is always a definable class. With that change, second-order
   naming with definable classes is **exactly the first Rayo+ step**: Rayo's
   language plus a truth predicate (Theorem A). The same rewrite shows that
   Rayo's own number does not depend on which reading of "class" you pick.
   An earlier note found a collapse under the weak reading, and that came from
   the way Rayo worded his definition, not from his number (§2).

3. **Correction: "costs about an inaccessible" mixes up three costs.**
   - *Belief.* Every Rayo+ level, even one iterated along all the ordinals, is
     fixed once ordinary truth about sets is fixed, so it adds nothing to
     believe. Full second-order Rayo does add something: a definite answer to
     "which collections of sets exist".
   - *Proof.* A theory that proves Rayo's function is well defined for every
     `n` needs only a modest recursion principle (the "ETR" family). That sits
     far below Morse–Kelley class theory, and further below an inaccessible.
   - *Picture.* The inaccessible appears only if you picture the universe as
     one set inside a bigger one. Then it comes from the universe satisfying
     second-order ZF (Zermelo), not from the naming (§3).

4. **One more order = one more powerset.** Naming in `(k+1)`-th order logic
   over a universe `V_κ` is the same, up to a constant factor in symbols, as
   ordinary first-order Rayo over `V_{κ+k}`, the universe with `k` more
   powerset levels on top (Theorem C). So second-order Rayo *is* first-order
   Rayo in a universe one level taller. The "language versus universe"
   trade-off in the first note is not an analogy but an identity. The
   higher-order ladder is the height ladder carried on past the top of the
   universe. Nothing special happens at Mahlo or weakly compact cardinals.
   What matters is only whether the smaller universe can be pointed to from
   inside the bigger one.

5. **Tall universes that reflect give no extra naming power at any fixed
   size.** If the height of the universe is an *indescribable* cardinal, then
   for each symbol budget `n` there is a shorter universe with exactly the same
   naming record at size `n` (Proposition D). Height helps naming only insofar
   as short formulas can describe it.

6. **Fish number 7** adds an oracle for the previous function, not a truth
   predicate. Its hierarchy sits inside the Rayo+ family along a small
   countable ordinal, so second-order Rayo beats it with a few symbols to
   spare (§6). *[Corrected 2026-11-25: it sits even lower, below the first
   Rayo+ step; see `ABOVE-RAYO.md` §2.]* **Literature:** one 2026 preprint (the "Arias function")
   defines a second-order Rayo iteration. Only its abstract was read. Nothing
   else found (§7).

## 1. Re-read of the first note

### 1.1 Lemma and Theorem 1 (classes beat Rayo): correct

The Lemma (Tarski's clauses have exactly one solution under full semantics)
and Theorem 1 are correct as written. **[paper; re-read]** Two remarks.

- *Rayo's number is already second-order.* Rayo's published definition of
  `Sat([φ], s)` reads "for any `R`: if `R` obeys Tarski's clauses then
  `R([φ], s)`". That is a class quantifier. So "the number Rayo(n)" is
  written by an `L₂` formula of size `c + O(log n)`, and Theorem 1 is
  essentially this observation. **[classical in substance; see
  `RAYO-R0-WELLDEFINEDNESS.md` §1–§4]**
- *A sturdier form.* Instead of one class `T` for all of first-order truth,
  use a class for truth of formulas **up to size `z`**:

  > `PartSat(T, z)`: `T` is a set of pairs `(⌜ψ⌝, s)` with `ψ` an `L₁`
  > formula of size `≤ z`, and `T` obeys Tarski's clauses for those formulas.

  For each `z ∈ ω` there is exactly one such `T`, by induction on formula size
  up to `z`, and it is the true satisfaction relation restricted to size
  `≤ z`. Theorem 1's formula `ψ_n` goes through unchanged with
  `∃T (PartSat(T, z) ∧ …)`. The gain is that this `T` is always a
  *first-order definable* class: truth for formulas of size `≤ k` is
  definable by a single formula, for example `Σ_k` satisfaction. That is what
  §2 uses. **[paper]**

### 1.2 Theorem 2 (classes swallow Rayo+): correct after a repair

**The gap.** The first note defined `L^α` with a separate predicate symbol
`Tr_β` for each `β < α`. For `α > ω` that alphabet is infinite, and once
`α ≥ ω₁` it is uncountable. Formulas of a given size are then infinitely
many. `N^α(n)` would be a supremum over infinitely many named numbers and
need not exist. So the theorem as written compares with an undefined function.
**[paper]**

**The repair (standard).** Use one predicate `S(b, e, s)`, read "stage `b`
says formula `e` holds under assignment `s`". `L^α` is `L₁ + S`, with `S`
interpreted as the *ramified* truth hierarchy along `α`: for `β < α`,
`S(β, ⌜ψ⌝, s)` holds iff `ψ` (an `L₁ + S` formula) is true under `s` when
every atom `S(b, …)` inside it is read as false unless `b < β`, and read off
stage `b` when it is. The stage is now a set variable, so the alphabet is
finite and the naming function is well defined by the finiteness argument
of `BN-function.md`. **[paper]**

**Uniqueness along all the ordinals.** Suppose two classes both obey the
clauses for every stage below `α` (with `α ≤ Ord`) and differ somewhere.
The stages where they differ form a nonempty class of ordinals, which has a
least element `β`. Below `β` they agree, so at `β` both obey Tarski's clauses
for the same structure, and they agree by induction on formulas, a
contradiction. This uses only that every nonempty class of ordinals has a
least element, which holds in `V` for the classes in range under full
semantics. **[paper; re-read]** The same argument works for any class
well-order `W` in place of `α`, for example `Ord·2` or `Ord^Ord`, as long as
`W` is defined by an `L₂` formula. So Theorem 2 holds in that wider form.
**[paper]**

### 1.3 The cost: "about an inaccessible" is wrong as stated

Corrected in §3. In short: the inaccessible belongs to one *picture* of what
classes are, not to the naming function.

### 1.4 Proposition 3 (bigger universe beats stronger language): correct, and nothing specific to inaccessibles

The proof uses only two facts: `κ` is defined by a short `L₁` formula in the
big universe, and second-order truth over `V_κ` is a set there. Neither
depends on `κ` being inaccessible. The same proof works for the least Mahlo,
the least weakly compact, or any definable `κ`. It also works for any finite
order, not just the second, since `V_{κ+k}` is a set too. So open item 3 of
the first note is closed by Corollary C2 below. The interesting question is
the *undefinable* case, which is left open (§8). **[paper]**

### 1.5 Henkin semantics: §5 of the first note was wrong

The first note said Theorem 1 fails when classes range only over the
first-order definable ones, because the full satisfaction class is not
definable. The full class is not definable, but the size-bounded classes of
§1.1 are, and they suffice. Theorem A below gives the correct statement.
**[paper]**

### 1.6 Limits (Claims A and B one level up): correct

No change. **[paper; re-read]**

## 2. Theorem A: definable classes give exactly the first Rayo+ step

Let `Def(V)` be the classes first-order definable over `V` with set
parameters. Write `N₂^Def` for naming in `L₂` with class variables ranging
over `Def(V)`. Write `N_Tr` for naming in `L₁ + Tr`, where `Tr(e, s)` is the
satisfaction predicate for `L₁` over `V`. This is the first rung of Rayo+.

**Theorem A.** There is a constant `c` such that for every `n`:

```
N₂^Def(n) ≤ N_Tr(c·n + c)      and      N_Tr(n) ≤ N₂^Def(c·n + c).
```

*Proof.* (Down.) A definable class is `{x : V ⊨ θ(x, p)}` for some `L₁`
formula `θ` and parameter `p`. So `∃X φ(X)` is equivalent to
`∃e ∃p φ′`, where `e` ranges over codes of `L₁` formulas with two free
variables, and `φ′` replaces each atom `x ∈ X` by `Tr(e, ⟨x, p⟩)`, the
assignment written with a fixed small formula. Each class quantifier and each
atom costs a constant number of extra symbols. A formula therefore names the
same number before and after translation.

(Up.) Replace each atom `Tr(e, s)` by

```
∃T ( PartSat(T, size(e)) ∧ (e, s) ∈ T ).
```

Here `size(e)` is a fixed `Δ₁` formula on codes. `PartSat(T, k)` has exactly
one solution among *all* classes (§1.1), and that solution is the definable
class of truths of size `≤ k`, so it lies in `Def(V)`. Hence the replacement
is equivalent to `Tr(e, s)` in `(V, Def(V))`. It costs a constant number of
symbols per atom. ∎ **[paper]**

**Consequences.**

- *The Henkin rung is a known rung.* Open item 4 of the first note is
  answered. Second-order naming with definable classes is neither below Rayo
  nor a new rung. It is the first Rayo+ step, up to a linear change of symbol
  count. It beats Rayo by Theorem 1 (sturdy form) and Claim B. **[paper]**
- *The whole Rayo+ ladder is a ladder of class ranges.* Let classes range
  over the sets definable in `L₁ + S` up to stage `β` (from §1.2). The same
  proof gives stage `β + 1` of Rayo+. Full semantics takes every class at once
  and lands above every stage (Theorem 2). **[paper; same proof]**
- *Rayo's number does not depend on the reading of "class".*
  `RAYO-R0-WELLDEFINEDNESS.md` §4 found that under a predicative (NBG-style)
  reading, Rayo's `Sat` degenerates and nothing gets named. That is a fact
  about Rayo's *wording*, which asks for one class holding all of truth.
  Rewritten with `PartSat`, the definition names the same number in every
  class range that contains `Def(V)`. That includes every model of GBC whose
  sets are the real `V`. So Rayo's commitment is exactly "first-order truth
  about sets is definite", with no choice about classes. **[paper; this
  refines R0 §4 and does not contradict its literal claim]**

## 3. Three different costs

The first note said full second-order Rayo "costs about an inaccessible's
worth of belief". There are three separate prices, and the inaccessible
belongs to only one of them.

### 3.1 Belief: what must be fixed for the numbers to be definite

**Proposition B.** If first-order truth over `V` is definite, then so is
every stage of Rayo+ along any first-order definable class well-order,
including along all the ordinals. **[paper]** *Reason:* stage 0 is
first-order truth. Each later stage is fixed by the earlier ones, by Tarski's
clauses. The uniqueness argument of §1.2 is a transfinite induction that
needs nothing beyond `V`.

Full second-order truth over `V` is **not** fixed by first-order truth over
`V`. Whether the class of all ordinals behaves like a weakly compact cardinal,
for example, is a second-order statement (§5), and first-order truth should
not settle it: two universes `V_κ`, `V_κ′` can agree on every first-order
sentence while only one of `κ`, `κ′` is weakly compact. **[expected]** So the first real new commitment on
this ladder is full second-order Rayo: a definite answer to "which
sub-collections of `V` exist". The Rayo+ family is free in belief. It costs
only in proof strength.

How to picture the new commitment:

- **Plurals (Boolos, and Rayo himself in his philosophical work).** "There are
  some sets such that …" is read as plural talk about sets. No new objects and
  no bigger universe. The commitment is that plural quantification over `V`
  is definite. **[classical]**
- **A set inside a bigger universe.** `V` is a set `V_κ` in some bigger `W`,
  and classes are its subsets, that is `V_{κ+1}`. If `V` also satisfies
  second-order ZF, Zermelo's theorem forces `κ` to be inaccessible.
  **[classical: Zermelo 1930]** Here the inaccessible comes from the
  universe obeying ZF₂, not from the naming function. In this picture the
  real cost of second-order Rayo is one extra powerset level of the universe
  (§4).

### 3.2 Proof: what a theory needs to prove the function is well defined for every `n`

For each *fixed* `n`, plain ZFC already proves "there is a largest number
named by an `L₁` formula of size `≤ n`". There are finitely many such
formulas, and for each one "it names `k`" is a first-order formula. So
separation gives the finite set of named numbers. **[paper]** The same holds
in KM for `N₂` and each fixed `n`. The real cost is the *uniform* statement
"for every `n`", which needs truth as one object.

| function | object needed | theory that suffices | where it sits |
|---|---|---|---|
| Rayo, `N₁` | a first-order truth class for `V` | GBC + `ETR_ω` | not provable in GBC; gives `Con(ZFC)` |
| Rayo+ along `Ord` | an `Ord`-iterated truth class | GBC + `ETR_Ord`, which is *equivalent* to it | above `ETR_ω` |
| Rayo+ along every class well-order | iterated truth along any class well-order | GBC + `ETR` (= clopen determinacy for class games) | strictly below GBC + `Π¹₁`-CA, strictly below KM |
| second-order Rayo, `N₂` | a truth object for `L₂`, which is third-order | a third-order class theory with the analogue of `ETR_ω` one type up | **[expected]** above KM-level truth, below ZFC + an inaccessible |

Sources: the equivalence of `ETR_Ord` with `Ord`-iterated truth predicates
is item (10) ⇔ (12) of the Main Theorem of Gitman, Hamkins, Holy, Schlicht
and Williams, *The exact strength of the class forcing theorem* (JSL 2020;
arXiv 1707.03700). That paper also says `ETR_ω` is not provable in GBC
(§2). Clopen determinacy ⇔ `ETR`, and "strictly weaker than GBC + `Π¹₁`-CA,
which is strictly weaker than KM", is Gitman–Hamkins, *Open determinacy for
class games* (arXiv 1509.01099), Main Theorem. **[classical; read in the
sources' own words up to the cited sections, rest not checked]** That
`ETR_ω` gives a first-order truth class is the standard recursion on formula
complexity. **[classical]** The last row is **[expected]**: `V_κ`,
`V_{κ+1}`, `V_{κ+2}` for inaccessible `κ` give a model, so it is below an
inaccessible.

This refines `LARGE-CARDINALS-AND-THE-LADDER.md` §2, which put Rayo's cost
"between ZFC and one inaccessible (MK)". KM is enough but far more than
needed: the recursion principle `ETR_ω` suffices.

## 4. Theorem C: one more order is one more powerset level

For a limit ordinal `λ > ω`, let `N_k^{V_λ}` be naming in `k`-th order logic
over `V_λ` under full semantics. Type 1 ranges over `V_λ`, type 2 over
subsets of `V_λ`, type 3 over sets of those, and so on. Let `N₁^{M}` be
ordinary first-order Rayo with universe the set structure `(M, ∈)`.

The observation behind it: type 2 objects are exactly the elements of
`V_{λ+1}`, type 3 objects are exactly the elements of `V_{λ+2}`, and so on.
`P(V_λ) = V_{λ+1}` and `P(V_{λ+1}) = V_{λ+2}`. So the domains of higher-order
logic over `V_λ` *are* the next levels of the cumulative hierarchy.

**Theorem C.** For each `k ≥ 1` there is a constant `c_k` such that for every
limit `λ > ω` and every `n`:

```
N_{k+1}^{V_λ}(n) ≤ N₁^{V_{λ+k}}(c_k·n + c_k)   and   N₁^{V_{λ+k}}(n) ≤ N_{k+1}^{V_λ}(c_k·n + c_k).
```

*Proof sketch.* (Down.) In `V_{λ+k}`, the set `V_{λ+k-1}` is definable as
the `⊆`-largest element, since every element of `V_{λ+k}` is a subset of it.
Repeating that `k` times defines `V_λ`, then `V_{λ+1}`, … by a formula of size
`O(k)`. A type-`j` quantifier becomes a quantifier bounded to `V_{λ+j-1}`.
Typed membership becomes `∈`.

(Up.) An element of `V_{λ+k}` is a type-`(k+1)` object. A first-order
quantifier over `V_{λ+k}` becomes a type-`(k+1)` quantifier. The only work is
membership between objects of mixed type, because a set in `V_λ` is also a
subset of `V_λ`. Fix formulas `Same_{i,j}(a, b)` ("type-`i` object `a` and
type-`j` object `b` are the same set") by recursion on `max(i, j) ≤ k+1`.
Then each atom `x ∈ y` becomes a disjunction over type pairs, of size
`O(k²)`, a constant for fixed `k`. ∎ **[paper; details of `Same_{i,j}` not
written out]**

**Corollary C1 (the identity behind the first note's trade-off).**
Second-order Rayo over `V_κ` and first-order Rayo over `V_{κ+1}` are the same
function up to a linear change of symbol count. **[paper]** If the universe
is `V_κ`, "second-order Rayo" is "Rayo in the universe with one more
powerset on top". Third-order is two more, and so on.

**Corollary C2 (Proposition 3 in general form).** Let `W` be a universe
containing `V_{κ+ω}`, in which `V_κ` is defined by an `L₁` formula of size
`d`. Then for every `k` there is `c_k` with
`N₁^W(c_k + d + 6·log₂(n+2)) > N_k^{V_κ}(n)` for every `n`. *Proof:* by
Theorem C, `N_k^{V_κ}` is first-order naming over `V_{κ+k-1}`, whose truth
is a set in `W`. Then apply Claim B. **[paper]** This covers the least
inaccessible, least Mahlo, least weakly compact, and any other definable
height.

**The picture.** Put universes `V_α` on a line by height. First-order Rayo
over `V_α` increases with `α` wherever each step is definable from the next.
**[paper]** The real universe `V` sits at height `Ord`. Second-order Rayo over
`V` is "Rayo at height `Ord + 1`", third-order is `Ord + 2`, and "all finite
orders at once" is `Ord + ω`. **The higher-order ladder is the height ladder
continued past the top of the universe.** Both are the same Claim-B step
repeated: add one powerset, and truth for the old level becomes a single
object. **[paper]**

## 5. Reflection: tall universes that look short to short formulas

**Classical background.** Lévy–Montague reflection says that any first-order
sentence true in `V` is true in some `V_α`. Hanf and Scott defined
`κ` to be `Π^m_n`-*indescribable* if every `Π^m_n` sentence, with a
parameter `A ⊆ V_κ`, that holds in `(V_κ, ∈, A)` also holds in
`(V_α, ∈, A ∩ V_α)` for some `α < κ`. `Π¹₁`-indescribable is equivalent to
weakly compact. **[classical: Hanf–Scott 1961; Lévy 1960]**

**Proposition D.** Let `n` be a size bound and let `κ` be
`Π¹_{n+2}`-indescribable. Then there is `α < κ` with
`N₂^{V_α}(n) = N₂^{V_κ}(n)`, and the same formulas of size `≤ n` name the
same numbers in both. If `κ` is totally indescribable (all `Π^m_n`), the
same holds for every finite order. For first order, any `V` and any `n`,
there are unboundedly many `α` with `N₁^{V_α}(n) = N₁^V(n)`. **[paper;
classical ingredients; the index `n+2` is not optimised]**

*Proof sketch.* List the finitely many `L₂` formulas `φ_1, …, φ_r` of size
`≤ n` with one free variable. The *naming record at size `n`* says, for each
`i`, whether `φ_i` names a number and which one, `m_i`. Put the `m_i` into a
parameter `A ⊆ V_ω`. The record is one conjunction of sentences of the form
"`∃!x (x ∈ ω ∧ φ_i(x)) ∧ φ_i(m_i)`" or its negation. A formula of size `≤ n`
has at most `n` alternations of class quantifiers, so the conjunction is
`Π¹_{n+2}` (with room to spare). Add the first-order conjunct "`ω` exists",
so that any reflecting `α` is above `ω`. By indescribability the record holds in some
`V_α`, `α < κ`, with `A ∩ V_α = A`. Being a natural number is absolute
between `V_α` and `V_κ`. ∎

**Plain reading.** If the universe is tall in this reflecting sense, no short
formula can tell it apart from some shorter universe. So at any fixed symbol
budget, its naming record is already the record of a shorter universe. The
extra height gives no naming power that a size-`n` formula can use. The
shorter universe it reflects to depends on `n`, so the *function* need not
equal any single shorter universe's function.

**Contrast.** The least inaccessible `κ` is the opposite case. "Second-order
ZF holds and there is no inaccessible below the height" is one short `L₂`
sentence true in `V_κ` and in no `V_α` with `α < κ`. By Zermelo it pins
`V_κ` down up to isomorphism. So height helps naming exactly where short
formulas can describe it. **[paper; classical ingredients]**

This makes precise the first note's remark that second-order naming is
"sensitive to the height of the universe". It is sensitive to the
*describable* features of the height, and indescribability is the measure of
how much is hidden. **[paper]**

## 6. Fish number 7

> **Correction 2026-11-25.** The placement below is too high. A function
> oracle is just a set parameter, and parameters never reach the next truth
> step. The whole of Fish's hierarchy sits strictly between Rayo and Rayo+
> stage 1. See `ABOVE-RAYO.md` §1–§2.

Source: the Googology Wiki page "Fish number 7" (read 2026-11-24). Fish's
2013 originals were not read. **[definition second-hand]** Fish adds to
Rayo's micro-language one oracle formula `f(a) = b`. `RR(f)` is Rayo's
function for that language. Then

```
R_0(n) = n,   R_{α+1} = RR(R_α),   R_λ(n) = R_{λ[n]}(n)  (fundamental sequences),
F7(x) ≈ R_{ζ₀}(x),   Fish number 7 = F7^{63}(10^100).
```

**Where it sits.** Each `R_α` is definable from the Rayo+ stages up to `α`.
`R_1` is Rayo's function, which `L₁ + Tr` defines in `c + O(log n)`
symbols (Theorem 1 in sturdy form, with `Tr` in place of `PartSat`). If
`R_α` is definable in `L₁ + S` using stages below `β`, then truth for
"`L₁` + an oracle symbol for `R_α`" is definable from stage `β`. So
`R_{α+1} ≤` stage `β + 1`, up to linear rescaling, and limits take the
union. By induction, `R_α` sits at or below Rayo+ stage `α` (roughly).
`ζ₀` is a small countable ordinal with a first-order definable fundamental
sequence system. **[paper; upper bound only]**

So Fish number 7 lies inside the Rayo+ family along about `ζ₀ + 1` stages.
That is far below the stage-`Ord` iteration, which Theorem 2 already puts
below second-order Rayo. As a single number it is named by an `L₂` formula of
fixed size, so `N₂(c) > ` Fish number 7 for a modest constant `c`.
**[paper]** Whether an oracle for `R_α` gives as much as a full truth
predicate at the same stage (a lower bound) is **[open]**. It is not needed
for the comparison.

Note: this replaces the "Fish number 7 is a version of this construction
**[expected]**" line of the first note. Fish iterates function oracles, not
truth predicates. The two are close but not obviously equal.

## 7. Literature check (light)

- **"The Arias function: an iteration of the Rayo operator in a second-order
  language"**, Zenodo record 18421517, January 2026, independent author.
  Its abstract describes a function "defined by iterating the Rayo operator
  in a second-order formal language", whose canonical form is "a functional
  iteration of Rayo₂". This is the only prior second-order Rayo definition
  found. Only the abstract was read, not the PDF. By Claim B, iterating any
  fixed function a computable number of times stays below the next rung, so
  it should sit below third-order Rayo. **[expected; not checked against its
  definition]**
- **Googology Wiki:** Fish number 7 and BIG FOOT are the set-theory-based
  numbers listed beside Rayo. Neither uses second-order quantifiers (§6;
  `phase0/e-foot.md` for BIG FOOT).
- **Class theories:** Gitman–Hamkins–Holy–Schlicht–Williams and
  Gitman–Hamkins, cited in §3.2. **Higher-order logic and categoricity:**
  Zermelo 1930; the Stanford Encyclopedia entry "Second-order and
  Higher-order Logic". **Indescribability:** Hanf–Scott 1961. All cited from
  memory except the two arXiv papers.

## 8. Open items

> **Update 2026-11-25.** `ABOVE-RAYO.md` answers item 1: no in general,
> because a small universe of undefinable height can name faster (its
> Proposition 4). It answers item 2 by placing Fish below stage 1, so the
> question is moot. It advances item 3 with the fine ladder (Theorem 3) and
> writes out `Same_{i,j}` from item 6.

1. **Undefinable heights.** If `V = V_κ` inside `W` and `κ` is *not*
   definable in `W`, does first-order Rayo over `W` still beat second-order
   Rayo over `V_κ`? First-order Rayo over `W` cannot point at `κ`. Taking a
   maximum over all candidate `κ′` can fail to be finite, because a fixed
   formula can name different numbers in different `V_κ′`.
2. **Lower bound for Fish's hierarchy.** Does `RR(R_α)` reach Rayo+ stage
   `α + 1`, or does an oracle for a function carry less than a truth predicate?
3. **Other class ranges.** Between `Def(V)` (Theorem A) and all classes
   (full semantics) lie the class ranges of minimal models of `ETR`, `Π¹₁`-CA
   and KM. Is naming monotone in the class range, and where do these sit?
4. **Read the Arias-function PDF** and place it exactly.
5. **Check the class-theory citations** in §3.2 against the full texts. Only
   their opening sections were read verbatim.
6. **Write out `Same_{i,j}`** in Theorem C and the exact indescribability
   index in Proposition D.
