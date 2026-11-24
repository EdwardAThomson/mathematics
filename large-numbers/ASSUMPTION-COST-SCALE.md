# Is there one scale of assumption cost for the whole ladder?

Written 2026-11-24. This tests the proposal at the end of `THE-LADDER.md` §4:
price each naming scheme by **the weakest standard theory that proves the
scheme's numbers exist**, and see whether that price orders the rungs the same
way growth does.

Tags as in the rest of the project: **[Lean]** machine-checked here,
**[paper]** argued here and not independently checked, **[classical]** a known
result cited from the literature (from memory unless a source is named), and
**[expected]** believed standard but neither proved here nor checked against a
source.

## 0. The answer in plain language

**No single theory-strength scale works, and the failure is sharp and
informative.** The proposal mixes two different kinds of assumption, which
move independently:

1. **Believing a process stops.** A computable scheme (Goodstein, TREE,
   Bashicu matrices, Loader's number) needs you to believe that some
   evaluation always terminates. That is a belief that a certain ordering has
   no infinite descending chain. Its price is an ordinal, and stronger
   schemes really do cost more. This is the only thing that moves on rung 0.
2. **Believing a body of truths is a finished object.** Busy Beaver and
   everything above it need you to believe that every question of some kind
   (does this program halt? is this arithmetic sentence true? is this
   statement about sets of numbers true?) has a definite answer. Its price is
   how much truth you treat as given. This is the only thing that moves on
   the rungs above rung 0.

Each kind is free where the other one does the work. Classical logic gives
you the existence of `BB(n)` almost for nothing: of the finitely many
programs of size `n`, each halts or does not, so the longest halting time is
a definite number, even though you cannot find it. A very weak fragment of
arithmetic proves that. But proving that TREE(n) exists for every `n` needs
a theory far stronger than the one that proves Busy Beaver exists, or even
the one that proves that full arithmetic-truth naming exists.

So under "weakest theory proving existence" TREE costs more than
arithmetic-truth naming, which outgrows it beyond recognition. **That is the
break: the scale is inverted at the boundary between rung 0 and rung 1.**

What survives is a clean law with **two coordinates, read in order**:

- first, **how much truth the scheme consults** (the halting problem, the
  `k`-th jump, arithmetic truth, truth about sets of numbers, truth about
  all sets). Measured in reverse mathematics by which set-existence axiom
  makes that body of truth into an object. This orders all rungs above 0,
  in agreement with every growth theorem the project has;
- then, **how strong a termination proof is needed**, measured by a
  proof-theoretic ordinal. This orders the schemes inside rung 0, and does
  nothing above it. That last point is a theorem of this project: provable
  naming in PA and in ZFC are the same growth class.

Description length (`κ`, bits) is a third measure, and it is flat above
rung 1. So there are three measures, each flat exactly where another one
moves.

## 1. What "the weakest theory proving its numbers exist" can mean

For a scheme `R` with record function `BN_R` (`THE-LADDER.md` §1) there are
three natural readings.

- **(P) The pointwise sentence.** "For every `n`, `BN_R(n)` exists", written
  as a single sentence of first-order arithmetic. Only possible when the
  naming relation of `R` is arithmetically definable.
- **(F) The function as an object.** In second-order arithmetic (reverse
  mathematics): "there is a function `f` with `f(n) = BN_R(n)` for all `n`".
  The weakest subsystem proving it is the price.
- **(C) Consistency strength / ordinal.** The proof-theoretic ordinal (or the
  consistency strength) of the theory found in (P) or (F).

All three are tested below. They agree on where the scale breaks.

## 2. Rung by rung

### Rung 0: computable schemes

For a scheme whose evaluation is a terminating computation indexed by an
ordinal notation of length `α`, "every expression evaluates" is a `Π₂`
sentence whose proof needs, roughly, well-foundedness of `α`. For natural
notation systems a theory proves totality of `f_α` exactly when `α` is below
its proof-theoretic ordinal. **[classical: Schwichtenberg and Wainer,
*Proofs and Computations* (2012); Buchholz and Wainer (1987)]**

| scheme | growth | weakest theory proving every value exists | status |
|---|---|---|---|
| power towers | `f_3` | `IΣ₁` (primitive recursive) | [classical: Parsons; Mints] |
| Knuth arrows, Graham | `f_ω`, `f_{ω+1}` | not `IΣ₁`; `IΣ₂` (Ackermann-type recursion) | [classical] |
| Goodstein, hydra, single-row BMS | `f_{ε₀}` | not PA; `PA + TI(ε₀)`; under (F), not `ACA₀`, since `ACA₀` is conservative over PA | [classical: Kirby–Paris 1982] |
| TREE | at least the small Veblen ordinal | not `ATR₀`; provable in `Π¹₁-CA₀` | [classical: Friedman; Simpson, "Nonprovability of certain combinatorial properties of finite trees" (1985)] |
| multi-row BMS | open | termination rests on an unrefereed proof (`BMS-WELLDEFINEDNESS-AUDIT.md`) | open |
| Loader's number (CoC) | beyond all of the above | strong normalization of the Calculus of Constructions; needs roughly higher-order arithmetic, beyond `Z₂` | [expected] |

Here the proposal works: higher ordinal, higher price, faster growth.

### Rung 1: Busy Beaver, `Σ₁` truth, provable naming in any theory

**(P)** "For every `n`, `BB(n)` exists" is provable in `IΣ₁`. *Sketch:* `IΣ₁`
proves bounded `Σ₁` comprehension (for each `b` the set
`{p < b : p halts}` is coded by a number) and `Σ₁` collection, so it gets a
bound on the halting times of the halting programs below `b`, and takes the
largest. **[expected; standard facts about `IΣ₁`, e.g. Hájek and Pudlák,
*Metamathematics of First-Order Arithmetic*, ch. I]**

The same sketch works word for word for `BoolosBig_T` for *any* computably
axiomatized `T`, ZFC included, since "`φ` `T`-names `k`" is again a `Σ₁`
relation. So the price at rung 1 does not depend on `T`, matching the
theorem that the growth does not either (`PROVABLE-NAMING-REPORT.md`
Theorems 5, 6, 11). What `IΣ₁` cannot do is find a value: no consistent `T`
proves an exact value or an upper bound of its own naming function
**[Lean, `RayoBoolos/NoExactValue.lean`]**. Existence is cheap; knowledge is
not.

**(F)** `BB` is Turing-equivalent to the halting problem `0′`
**[classical]**, so the function exists as an object exactly when `0′` does:
`RCA₀ + "0′ exists"`, a subtheory of `ACA₀`.

**(C)** `ACA₀` is conservative over PA, ordinal `ε₀` **[classical]**.

### Rungs `k + 1`: oracle Busy Beaver, `Π_k` and `Σ_{k+1}` truth naming

These grow like `BB^{(k)}` (`MIDDLE-RUNGS.md`), and `BB^{(k)}` is
Turing-equivalent to `0^{(k+1)}` **[classical; the same argument as for
`BB`]**.

**(P)** `IΣ_{k+1}`, by the same sketch one level up **[expected]**.
**(F)** `RCA₀ + "0^{(k+1)} exists"`. **(C)** Every finite rung sits inside
`ACA₀`, ordinal `ε₀`.

### Rung ω: arithmetic-truth naming

**(P)** Not expressible: the uniform sentence needs a truth predicate for
arithmetic, which arithmetic lacks (Tarski). For each *fixed* `n` the formulas
of size `≤ n` have bounded quantifier depth, so PA proves "`N_TA(n)` exists"
for each numeral `n` separately. That is why reading (P) is the wrong one
above rung 1: it would put the whole arithmetic ladder at PA.

**(F)** The function is computable from `0^{(ω)}` (`GENERAL-NAMING-THEOREM.md`
Theorem 8), and from `0^{(ω)}` one gets a satisfaction class for arithmetic.
So `RCA₀ + "0^{(ω)} exists"` suffices, which is inside `ACA₀⁺` ("every set has
an `ω`-th jump"). **[paper, from classical facts]**

**(C)** `ACA₀⁺ ⊆ ATR₀`, so its ordinal is below `Γ₀`. **[classical: Simpson,
*Subsystems of Second Order Arithmetic*; Marcone and Montalbán, "The Veblen
functions for computability theorists" (2011)]**

### The rungs about sets of numbers

The rung just above arithmetic truth is being proved in a separate thread
("Prove the rung above arithmetic truth"); its result is not yet in. On the
sketch sent there, naming by `Σ¹₁` or `Π¹₁` truth grows like Busy Beaver
over all hyperarithmetic oracles, is computable from Kleene's `O`, and
`Σ¹₂` naming reaches Busy Beaver with oracle `O`. If that holds, under
(F) the price of the `Σ¹₁` rung lies between "every hyperarithmetic set
exists" and `Π¹₁-CA₀` ("`O` exists"), and the `Σ¹_k` rungs need `Π¹_k-CA₀`.
**[depends on the other thread; to be filled in when it lands]**

Full truth for second-order arithmetic needs a satisfaction class for `Z₂`,
beyond `Z₂` itself. **[expected]**

### Rayo's rung

A satisfaction class for the universe of sets. `RAYO-R0-WELLDEFINEDNESS.md`
shows Morse–Kelley class theory suffices and plain first-order set theory
does not. A weaker class theory with an explicit truth-class axiom likely
suffices too **[expected]**; this does not change the ordering.

## 3. Where it breaks

Put the rows together.

| scheme | rung | price under (F) | ordinal of that theory |
|---|---|---|---|
| Busy Beaver | 1 | `RCA₀ + 0′` ⊆ `ACA₀` | `≤ ε₀` |
| oracle BB, any finite level | `k + 1` | ⊆ `ACA₀` | `≤ ε₀` |
| arithmetic-truth naming | ω | ⊆ `ACA₀⁺` | `< Γ₀` |
| Goodstein | 0 | beyond `ACA₀` | `> ε₀` |
| TREE | 0 | beyond `ATR₀` | `> Γ₀` |
| Loader | 0 | beyond `Z₂` | [expected] |

**Inversion 1 (every reading).** Goodstein's function grows far slower than
Busy Beaver but costs more: PA does not prove it total, while `IΣ₁` proves
`BB` total. Under reading (P) the inversion starts even lower: Knuth's
arrows need `IΣ₂`, more than Busy Beaver's `IΣ₁`. **[classical ingredients,
with `BB` in `IΣ₁` tagged [expected] in §2; the comparison is ours]**

**Inversion 2 (readings F and C).** TREE is computable, so arithmetic-truth
naming outgrows it enormously, yet `ATR₀` proves that arithmetic-truth naming
is total and does not prove that TREE is. **[classical ingredients; the
comparison is ours]**

**Inversion 3 [expected].** Loader's number, on rung 0, costs more than every
rung defined inside second-order arithmetic.

So the proposed single scale is not monotone in growth. Two further, smaller
breaks:

- **It is too coarse.** All finite rungs sit inside `ACA₀`; the "Big Five" of
  reverse mathematics do not separate them. A fine-grained version
  (`RCA₀ + "0^{(k)} exists"`) does.
- **It is not a line.** By `GENERAL-NAMING-THEOREM.md` Corollary 6, every
  Turing degree is the rung of some theory. Turing degrees are only
  partially ordered, so any scale that tracks rungs must be partial there.
  Whether two rungs with incomparable degrees can have comparable growth is
  open.

## 4. Why, and the law that survives

**Why.** The two kinds of assumption in §0 are different logical
commitments.

- A termination claim is `Π¹₁` in character (a well-ordering has no
  descending sequence). Its strength is measured by ordinals. It never needs
  any set of truths to exist.
- A rung above 0 needs no termination proof at all: its existence follows
  by excluded middle, applied to finitely many questions of the kind the
  rung consults. What it needs is that those questions have answers, and to
  have the function as an object, that the set of answers exists. Its
  strength is measured by comprehension (`0′`, `0^{(k)}`, `0^{(ω)}`, `O`, …,
  a truth class for V).

The project's theorem that `BoolosBig_T` is Busy Beaver class for every
consistent computably axiomatized `T` (`PROVABLE-NAMING-REPORT.md` Theorems
5, 6; lower bound [Lean]) is exactly the statement that the first kind of
strength buys nothing above rung 0.

**The two-coordinate law.** Price a scheme `R` by the pair

```
( deg(R), ord(R) )
```

where `deg(R)` is the body of truth its naming relation consults, as a Turing
degree (equivalently, which set-existence axiom makes `BN_R` an object), and
`ord(R)` is the proof-theoretic ordinal needed to prove totality given that
truth. Compare pairs lexicographically, first coordinate first.

What is proved or classical about this order:

- **Same degree `0` (rung 0): the ordinal decides.** For natural notation
  systems, `f_α` with `α` below a theory's ordinal is provably total there,
  and higher `α` grows faster. **[classical]**
- **Positive degree beats degree `0`, whatever the ordinal.** `BB` dominates
  every computable function. **[classical, Radó]**
- **Within a rung of the form `BB^A`, the ordinal is irrelevant.** Any two
  consistent theories `T, T′ ⊇ PA⁻` deciding the same `A` that lists their
  theorems have `Big_T ≈ Big_{T′} ≈ BB^A`. **[paper,
  `GENERAL-NAMING-THEOREM.md` Corollary 6; the case `A = ∅` has its lower
  bound in Lean]**
- **Degree order gives growth order between oracle rungs.** If `A ≤_T B`
  then `BB^A(ℓ) ≤ BB^B(ℓ + c)` (simulate the `A`-oracle with `B`). If `B`
  computes `A′`, then `BB^B` beats `BB^A` by an exponential stretch of the
  argument (`GENERAL-NAMING-THEOREM.md` Proposition 7(c), since `A′`
  computes `BB^A`). **[paper, routine]**
- **Every natural rung the project has fits.** Rung 1 (`0′`), rung `k + 1`
  (`0^{(k+1)}`), rung ω (`0^{(ω)}`, a limit), Rayo (truth for V). The rungs
  about sets of numbers are expected to fit (§2), pending the other thread.

What is not claimed: that `deg(A) <_T deg(B)` always gives strictly faster
growth when `B` does not compute `A′`; that is open. And not every function
of high degree grows fast; the law is about naming functions, which are
all of Busy Beaver type above rung 0 by the general naming theorem.

## 5. What this does to the `κ` question

`KAPPA-TABLE.md` asked whether growth scales with the bits needed to state the
rulebook, and found no clean law. With this note there are three measures:

| measure | moves on rung 0 | moves above rung 0 |
|---|---|---|
| bits to state the rulebook (`κ`) | yes, roughly | no (constant per rung) |
| termination strength (ordinal) | yes | no (Theorem 5/6/11) |
| truth consulted (degree / comprehension) | no (all computable) | yes |

So the honest summary of the project's original question: growth on rung 0
tracks the ordinal (and loosely the bits); growth across rungs tracks only
how much truth you accept as given; and the two cannot be merged into a
single "assumption cost" without the inversions of §3.

## 6. Is this known?

Searched 2026-11-24 (web, and `LITERATURE-SURVEY.md`), for prior statements
pricing large-number schemes by the strength of the theory proving them well
defined, and for the contrast between Busy Beaver's cheap totality and the
expensive totality of slower computable functions.

- Every ingredient is classical: provably total functions and ordinal
  analysis; Kirby–Paris; Friedman's finite Kruskal theorem and
  `ATR₀`; conservativity of `ACA₀`; the reverse-mathematics systems
  `ACA₀⁺`, `ATR₀`, `Π¹_k-CA₀` (Simpson's book).
- The observation that "`BB` is total" is provable by excluded middle while
  values are not provable appears informally (for example in online
  discussion), but we found no source stating any theory for it, and none
  contrasting it with Goodstein or TREE.
- Simmons (arXiv:1809.08676) compares naming systems by the strength of the
  theory, at fixed inputs, for computably axiomatized systems; by this
  project's theorems that comparison never changes the growth class.
- We found no statement of the inversion or of the two-coordinate law.
  Suggested wording: "Pricing a naming scheme by the weakest theory proving
  it well defined is not monotone in growth: termination strength orders
  computable schemes, and the amount of truth consulted orders the rest.
  The ingredients are classical; we found no earlier statement of the
  comparison."

## 7. Open items

1. Turn the two **[expected]** `IΣ_{k+1}` sketches into a proof with a
   reference, or a Lean statement over Foundation's `IΣ` fragments.
2. Fill in the second-order rows when the "rung above arithmetic truth"
   thread reports, in particular whether the `Σ¹₁` naming function computes
   `O`, which decides whether its price is `Π¹₁-CA₀` or something weaker.
3. Pin down the strength needed for Loader's number (strong normalization of
   CoC) with a source.
4. Rungs of incomparable Turing degree: can their naming functions have
   comparable growth?
