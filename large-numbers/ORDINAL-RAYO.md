# Rayo for infinite numbers: the largest ordinal nameable in n symbols

Written 2026-11-24, from two questions about Rayo's function: "does it say
anything about infinity?" and "could we get faster growth by allowing real
numbers?" The answers are "it uses infinity but outputs finite numbers" and
"no". Asking for infinite outputs gives a genuinely different record, and
that record is the subject of this note.

Tags as in the rest of the project: **[paper]** argued here and not
independently checked, **[classical]** a known result cited from memory,
**[expected]** believed true but not proved here, **[open]**. Nothing here
is machine-checked. The arguments are short. What the note offers is the
definition and the comparisons.

## 0. In plain language

**Rayo's function** asks for the biggest *whole number* you can pin down
with a formula of set theory of at most `n` symbols. Its formulas may talk
about infinite sets, but the answer is always finite.

**Real numbers add nothing** (§1). A huge real pinned down in `n` symbols
gives a whole number just below it for a few symbols more. Rayo's formulas
can already talk about reals.

**Infinite answers do add something** (§2 onwards). An *ordinal* is a
counting number that keeps going past the finite ones: 0, 1, 2, …, then
ω (the first infinite one), ω + 1, …, ω·2, …, then ω₁ (the first one with
uncountably many before it), and so on, without end. Ask:

> what is the largest ordinal that a formula of at most `n` symbols can
> single out?

Call the answer `ORayo(n)`. It is a well-defined ordinal for each `n`, given
the same assumption Rayo's function needs (one fixed universe of sets).
Some facts about it:

1. **It keeps climbing.** A few symbols more always gets you a bigger one:
   "one more than the ordinal this formula picks out".
2. **It overtakes every ordinal googology uses almost at once.** All the
   ordinals that measure big-number systems (ε₀, Γ₀, the Bashicu matrix
   ordinals, …) are *countable*. "The first uncountable ordinal" takes only
   a short formula, so from a small `n` on, `ORayo(n)` is beyond all of them.
   The same goes for "the first ordinal no program can describe" (ω₁^CK).
3. **It runs into the large cardinals.** "The least inaccessible cardinal"
   and "the least measurable cardinal" are short formulas, so if these
   cardinals exist, `ORayo` passes them at modest `n`. If they don't exist,
   those formulas name nothing. So `ORayo` depends on the universe of sets
   much more visibly than Rayo's function does.
4. **It never reaches the top of what it names.** Only countably many
   ordinals can be named by any formula at all. The limit of the named
   ordinals is an ordinal that no formula can name, because if one could,
   a few symbols more would name the next one up. This is Kőnig's paradox ("the least ordinal that
   cannot be defined") turned into a theorem, the same way Rayo's function
   turns Berry's paradox into one.

So the ordinal version is a different kind of record from Rayo's function.
It does not grow faster, because "faster" compares finite outputs. It
measures how far into the infinite a short description can reach.

## 1. Real numbers do not help

Let `RealRayo(n)` be the largest real number `r` such that some formula of
at most `n` symbols is true of `r` and of nothing else (take the supremum
if there is no largest; it doesn't matter below).

**Claim 1.** There is a constant `c` with
`Rayo(n) ≤ RealRayo(n) < Rayo(n + c) + 1` for all `n`, under the usual
convention that whole numbers are among the reals.

*Proof.* The first inequality holds because every whole number is a real
(with a fixed translation, which only changes constants). For the second,
let `φ` single out the real `r`. Then
`ψ(x) :≡ ∃y (φ(y) ∧ x = ⌊y⌋)` singles out the whole number `⌊r⌋`, and
"`x = ⌊y⌋`" is a fixed formula of set theory, of constant size `c`. So
`⌊r⌋ ≤ Rayo(n + c)`, and `r < ⌊r⌋ + 1`. ∎ **[paper]**

So allowing real answers changes Rayo's function only by a constant in the
input. The same argument works for any kind of answer that rounds to a
whole number by a fixed formula: rationals, reals, complex numbers by
absolute value, and so on.

**Why the restriction to whole numbers doesn't hold Rayo back.** ℵ₀ counts
how many whole numbers there are, but each whole number is finite, and
there is no largest. Rayo's numbers are big because of *where* they are on
the number line, and the whole numbers reach as far along it as the reals
do. **[classical]**

**And the formulas already use the reals.** Rayo's quantifiers range over
every set, including every real, every set of reals, and every infinite
cardinal. Allowing reals inside the formulas changes nothing.
(`RAYO-R0-WELLDEFINEDNESS.md` §1.)

## 2. The definition

The language is Rayo's: first-order formulas built from `∈`, `=`, `¬`, `∧`,
`∃` and variables, interpreted in the universe of sets `V`, with no
parameters. Size is symbol count, as in `RAYO-R0-WELLDEFINEDNESS.md`.

A formula `φ(x)` with one free variable **names** the ordinal `α` if `α` is
the only set satisfying `φ` in `V` (so in particular the only ordinal).
Then

```
ORayo(n) := the largest ordinal named by some formula of size ≤ n.
```

**Claim 2 (well defined).** For each `n` the maximum exists.

*Proof.* There are finitely many formulas of size at most `n`, each names
at most one ordinal, and at least one names something once `n` is big
enough to write "`x` is empty" (that names 0). A finite non-empty set of
ordinals has a largest element. ∎ **[paper]**

What this needs is the same as for Rayo's function: a definite notion of
"true in `V`" for every formula. `RAYO-R0-WELLDEFINEDNESS.md` showed that
Morse–Kelley class theory (MK) supplies it and ZFC alone does not. Nothing
more is needed here. **[paper, by that note]**

## 3. Basic facts

**Claim 3 (it keeps climbing).** There is a constant `c` with
`ORayo(n + c) > ORayo(n)` for every `n` past the first value.

*Proof.* If `φ` names `α`, then
`ψ(x) :≡ ∃y (φ(y) ∧ x = y ∪ {y})` names `α + 1`, and the clause
"`x = y ∪ {y}`" has fixed size. ∎ **[paper]**

By the same kind of argument, a constant number of extra symbols gets you
`α + α`, `α·α`, `ω^α`, the `α`-th infinite cardinal `ℵ_α`, the next
inaccessible above `α` (if there is one), and so on. Each is a fixed formula
applied to `α`. **[paper]**

**Claim 4 (where the first values land).** For some small `s₁ < s₂ < s₃`:

- `ORayo(n) ≥ ω` once `n ≥ s₁` ("the least non-zero limit ordinal");
- `ORayo(n) ≥ ω₁^CK` once `n ≥ s₂`, where ω₁^CK is the least ordinal that is
  not the order type of any computable well-ordering of the whole numbers;
- `ORayo(n) ≥ ω₁` once `n ≥ s₃` ("the least ordinal not in one-to-one
  correspondence with ω").

**[paper; the constants are not computed]** In Rayo's bare `∈`-language,
none of these is a *small* formula in absolute terms, since even "is an
ordinal" takes dozens of symbols. But each is a fixed formula. So the
ordinal-notation ruler that measures rung 0 of `THE-LADDER.md` (ε₀, Γ₀,
the Bachmann–Howard ordinal, the Bashicu matrix ordinal, all below ω₁^CK)
is left behind after a fixed number of symbols. **[classical: those
ordinals are below ω₁^CK]**

**Claim 5 (it never reaches its own limit).** Let `σ*` be the supremum of
all ordinals named by some formula, of any size. Then `ORayo(n) < σ*` for
every `n`, the values `ORayo(n)` tend to `σ*`, and `σ*` itself is not named.

*Proof.* Every named ordinal `α` has `α + 1` named (Claim 3), so the named
ordinals have no largest element. Every named ordinal is `ORayo(n)` or below
it for some `n`, so `sup_n ORayo(n) = σ*`, and no `ORayo(n)` equals `σ*`.
If `φ` named `σ*`, Claim 3 would name `σ* + 1`, which is larger than every
named ordinal. ∎ **[paper]**

The named ordinals have gaps, so `σ*` is not "the least unnamed ordinal".
There are only countably many formulas, so only countably many ordinals are
named, yet ω₁ is named, and below it lie uncountably many ordinals. So the
least unnamed ordinal `σ` is countable, and `σ < ω₁ ≤ σ*`. **[paper]**

It is also above ω₁^CK. Every ordinal below ω₁^CK is the order type of the
`e`-th computable well-ordering for some number `e`, and "the order type of
the `e`-th computable well-ordering" is a formula once `e` is written out.
So every ordinal up to and including ω₁^CK is named, and
`ω₁^CK < σ < ω₁`. **[paper]**

Neither "`σ*`" nor "the least unnamed ordinal" can be written as a formula
of set theory. If it could, that formula would name it, which is a
contradiction. This is Kőnig's paradox of 1905 ("the least indefinable
ordinal"), and its resolution is the same as for Berry's paradox: "named
by a formula" needs truth for `V`, which set theory cannot define (Tarski).
**[classical]** It is Claim A of `THE-LADDER.md` §3, for ordinals.

## 4. It depends on the universe much more than Rayo's function does

Rayo's function depends on the universe of sets only through *which* finite
numbers its formulas pick out, and it's open whether the record itself ever
changes (`LARGE-CARDINALS-AND-THE-LADDER.md` §2.5). For ordinals the
dependence is visible at once.

- **Large cardinals.** "The least inaccessible cardinal" names an ordinal
  in a universe with an inaccessible and names nothing in one without.
  The same holds for the least measurable, the least Woodin, and so on. In a
  universe with many large cardinals, `ORayo(n)` is far larger at the same
  `n`. **[classical ingredients]**
- **The continuum hypothesis.** "The number of real numbers", as a cardinal,
  is a short formula. It names ℵ₁ if CH holds, ℵ₂ in some other universes,
  and in general can be almost any cardinal of uncountable cofinality
  (Easton, Solovay). **[classical]** So a fixed formula's named ordinal moves
  between universes.
- **Gödel's universe `L`.** In `L` there are no measurable cardinals, so
  every formula of the form "the least measurable …" names nothing.
  **[classical: Scott 1961]**

So `ORayo` is a measure of the universe as much as of the language. A
richer universe of sets has bigger nameable ordinals.

## 5. How it relates to the rest of the project

- **It is not a faster-growing function.** Growth compares finite outputs at
  each input. `ORayo` has infinite outputs, so it does not sit on the ladder
  of `THE-LADDER.md`. It is a different question: how far into the
  infinite a description of a given length reaches.
- **The two ladders meet in it.** Its values pass the ordinal ruler of rung 0
  (§3), then ω₁, then, universe permitting, the large cardinals of
  `LARGE-CARDINALS-AND-THE-LADDER.md` §3. In that sense it is "Rayo's
  function for the size ladder".
- **The same "no top" argument applies.** Add a symbol for "true formula of
  set theory" and the new language names `σ`-like ordinals the old one
  couldn't, exactly as Claim B of `THE-LADDER.md` §3 says for finite records.
  **[expected; same argument]**
- **Finite outputs from infinite records.** One can get finite numbers back,
  for example "the number of infinite cardinals below the least
  inaccessible that are …". Such formulas are among those Rayo's function
  already counts, which is part of why it grows so fast. There is no simple
  formula relating `Rayo(n)` and `ORayo(n)`. **[open]**

## 6. Is this known?

The ingredients are classical: ordinal definability and the class `OD` of
sets definable from ordinals (Gödel, Myhill–Scott 1971); parameter-free
definable ordinals; Kőnig's paradox; Tarski's undefinability theorem. The
googology community discusses the largest ordinals definable in various
systems. Not searched in this pass: whether this exact record function, the
ordinal analogue of Rayo's function, has been defined or named before.

## 7. Open items

1. Where the least unnamed ordinal `σ` (countable, §3) sits among the
   countable ordinals, for example relative to ω₁^CK and to the ordinals
   that are stable in `L`, and whether that depends on the universe.
2. Estimate the symbol counts `s₁, s₂, s₃` of §3 in Rayo's microlanguage.
3. Any non-trivial relation between `Rayo(n)` and `ORayo(n)`.
