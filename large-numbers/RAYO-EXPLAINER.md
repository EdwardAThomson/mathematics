# How much does it cost, in pure logic, to write down the number 6?

This is a plain-English walkthrough of one small result from the
`large-numbers` project: for first-order set theory (the family behind
Rayo's function, the "biggest number" construction that ends CodeParade's
two videos on this subject), we mechanically proved, in the Lean 4 proof
assistant, exactly how many symbols it takes to uniquely name each of the
numbers 0 through 6 — and how many symbols it costs just to state the rules
of the game in the first place. Full technical record: `FINDINGS.md`
(k=0-3, from the original run) and `rayo-notes/` + `rayo-lean/` (k=4-6 and
the aggregated table, from the follow-up run this note describes). Lean
source for every proof: `rayo-lean/Rayo/K0.lean` through `K6.lean`.

## The game

Fix a tiny formal language: the symbol `∈` ("is a member of"), the logical
connectives `¬` ("not"), `∧` ("and"), `∃` ("there exists"), `∀` ("for all"),
parentheses, and variable names. Nothing else — no numerals, no `+`, no
"empty set" symbol. Given a single free variable x, you write a formula
describing x, and if that formula is true of exactly one thing in the
universe of sets, that thing is the number your formula "names" (naturals
are encoded the standard way: 0 is the empty set, and each next number is
the set of all the numbers before it).

The question: how many symbols does the *cheapest formula you can find* for
each number cost? Call that n_k for the number k. This is deliberately the
same game Rayo's function plays at an astronomical scale (a googol symbols);
we're asking it at the smallest possible scale, where you can actually see
what's going on.

## Why 0 costs 10 symbols, not "0"

You can't just write "0" — there's no numeral in the language. You have to
*describe* the empty set using only membership and logic:

**∀y(¬(y∈x))** — "for every y, y is not a member of x" — i.e. nothing is
inside x — i.e. x is empty.

| # | symbol | |
|---|---|---|
| 1 | ∀ | for all |
| 2 | y | |
| 3 | ( | |
| 4 | ¬ | not |
| 5 | ( | |
| 6 | y | |
| 7 | ∈ | is a member of |
| 8 | x | |
| 9 | ) | |
| 10 | ) | |

Ten symbols, one for every token — nothing is free, and (per the actual
published Rayo formalism, confirmed in `rayo-notes/literature-notes.md`)
you're not allowed to drop a "redundant" paren the way a human would on
paper. That convention is why the counts below get big fast: every
connective and quantifier is contractually required to carry its own
parentheses.

Note what this formula does *not* say: it doesn't assert "the empty set
exists" (that would be a separate `∃` claim). It describes x directly —
"x has no members" — and because two sets with the same members are the
same set (a background fact we get for free; it isn't written into the
formula), that description pins x down to be *the* empty set, uniquely.

## Why 1 costs 30, not 11

1 = {0} = "the set whose only member is the empty set." The formula has to
say two things about x: it has *something* in it, and *everything* in it is
empty.

- **A** = "x has a member" = `∃y(y∈x)` — 7 symbols
- **B** = "every member of x is empty" = `∀z(∀w(¬(z∈x ∧ w∈z)))` — literally
  "for all z and w, it's not the case that z is in x and w is in z" — 20
  symbols
- Combine: **(A ∧ B)** — 30 symbols total

B costs almost three times A, even though it's expressing basically the
same idea as "is empty" (φ_0's whole content) — because now it has to talk
about *every member of x*, which needs an extra variable (z for the member,
w for something inside the member) instead of just one.

## The pattern: each number embeds all the ones before it

Because of how the numbers are encoded (k+1 = "the set of all of 0, 1, ...,
k"), naming k+1 means saying: "x's members are *exactly* the things
satisfying φ_0, or φ_1, ..., or φ_k" — and then adding a clause ruling out
anything else. So φ_{k+1} literally contains a (renamed) copy of every
earlier φ_i, embedded, plus a "nothing else qualifies" exclusion clause. You
can see this directly in how φ_3 was built (from `FINDINGS.md`):

```
E0 (embedded copy of "is 0")  = 20
E1 (embedded copy of "is 1")  = 40
E2 (embedded copy of "is 2")  = 138
U  (excludes anything else)   = 196
        + connective overhead  = 9
                          total = 403
```

That's the whole mechanism. Every step, you pay for a full copy of
everything that came before, plus a growing exclusion clause. The exclusion
clause (U) is usually the single most expensive part.

## The full table

All seven proved end-to-end in Lean 4, with **no shortcuts**: every proof's
axiom list checked to depend only on `propext` and `Quot.sound` (ordinary
logical bookkeeping) — never `sorryAx` (an unproved gap) or
`Classical.choice` (a nonconstructive escape hatch).

| k | n_k (symbols) | ratio to k-1 | Lean file |
|---|---|---|---|
| 0 | 10 | — | `rayo-lean/Rayo/K0.lean` |
| 1 | 30 | 3.0× | `K1.lean` |
| 2 | 128 | 4.3× | `K2.lean` |
| 3 | 403 | 3.1× | `K3.lean` |
| 4 | 1,228 | 3.0× | `K4.lean` |
| 5 | 3,703 | 3.0× | `K5.lean` |
| 6 | 11,128 | 3.0× | `K6.lean` |

The ratio settles down to almost exactly **3× per step** once you're past
the first couple of numbers — naming the next integer costs roughly triple
the previous one, essentially forever, because each step pays for a full
copy of every number before it plus a growing exclusion clause. That's a
genuinely brutal growth rate for something as modest as "count to 6": by
k=6 you need over eleven thousand symbols to say what "6" means from bare
membership and logic alone.

**Why the run stopped at 6, not because it got stuck.** This was run with
hard resource caps per step specifically so an open-ended search couldn't
run away (a design question the run's operator raised directly: bound by
wall-clock, by proof-attempt count, or by something else — the answer used
here was both, whichever bound first). k=6 was the planned ceiling; the
proof difficulty was rising the whole way but never actually stalled — the
run reached its intended stopping point on schedule, not a wall it hit.

## Is this an efficient way to write numbers? No — and that's revealing

The *alphabet* used never grows: `∈, =, ¬, ∧, ∃, ∀, (, )` — 8 fixed symbol
kinds, all already in play by k=1. Essentially all of n_k's growth (10 up
to 11,128) is *repetition* of that same tiny set, not new vocabulary.

Variables are a different story. The convention charges 1 symbol per
variable occurrence regardless of which variable it is — `v₁` and `v₁₁₅`
both cost exactly 1, a deliberate, stated choice (`rayo-notes/convention-
notes.md`: charging for variable identity "would penalize formulas that
happen to need many simultaneously-live variables"). But the actual index
needed climbs fast, straight from the Lean source:

| k | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| highest variable index used | 1 | 3 | 3 | 4 | 9 | 40 | 115 |

By k=6 the proof needs a variable literally called `v115`, because every
embedded copy of an earlier φ_i needs fresh bound variables to avoid
capturing an outer one, and the supply of "not yet used" names keeps
draining. The convention's "identity is free" rule is quietly absorbing a
real cost that grows right alongside n_k itself.

Putting a number on the inefficiency: converting n_k to bits the way
`BN-function.md` Section 5 already does for cross-system comparison
(bits ≈ symbols × log₂(alphabet size), generously using ~4 bits/symbol),
n_6 ≈ 11,128 × 4 ≈ **44,500 bits** to name the number **six**. From this
project's own leaderboard data (`phase0/c-pole-position.md`): BLC needs
just **1,850 bits** to construct a number that *exceeds Loader's number*,
and **331 bits** to reach Buchholz-ordinal territory via the Bashicu Matrix
System. So bare first-order logic spends roughly **24× more bits naming
six** than BLC needs to blow past Loader's number, and **~130× more** than
BMS needs to reach Buchholz's ordinal. BMS and BLC are specifically
engineered for compact recursion; bare first-order logic, under this
convention, has no such trick — every reference has to be fully respelled,
never reused.

## What if formulas could reuse each other?

**Now Lean-verified** (`rayo-lean/Rayo/Reuse.lean`, `Rayo/ReuseSix.lean`;
full record in `rayo-lean/REUSE-COMPRESSION-REPORT.md`) — this started as a
hand-derived estimate, flagged at the time as not yet checked, and has since
been built and mechanically confirmed.

Every φ_k embeds a full, freshly-renamed copy of every earlier φ_i (the "+10
wrapper overhead" pattern is exact and empirical: each embedded copy costs
n_i + 10). Allowing a short reference to an *already-defined* φ_i instead —
a named-predicate call (`ref`, costing a fixed 2 symbols, matching the
existing convention's own atom-cost rule) rather than a full respelling —
was built as a real extension of the `Formula` language, given proper
expansion semantics, and proven `Sat`-equivalent to the existing, independent
`K6.lean` construction (not just shorter-looking: mechanically confirmed to
name the same number, six).

| | estimated | real, machine-checked |
|---|---|---|
| φ_6 alone, 0-5 already defined | ~161 | **148** (75.2× shorter than 11,128) |
| Including defining 0-5 from scratch | ~616 | **550** (20.2× shorter) |

The original estimate held up directionally and was a little pessimistic —
the real numbers land 8-11% below the guess, not above it. One genuine bug
was caught and fixed along the way: existentials are encoded internally as
`¬∀¬` with no dedicated symbol, and a first pass at the cost function
overcounted every `∃` by 6 symbols before being corrected to match
`convention-notes.md`'s stated convention.

## Does the growth rate speed up eventually?

Look at the ratio column in the table above again: 3.0, 4.3, 3.1, 3.0, 3.0,
3.0. It is not accelerating — if anything it is *settling* to a flat ~3×
per step. Nothing in this data suggests naming k=100, or k=1000, gets any
*cheaper per step* than naming k=6 did. Taken at face value and
extrapolated blindly, that would be an alarming result: a googol
(10^100) symbols, spent at a fixed ~3× rate, only reaches k ≈ log₃(10^100)
≈ 210 — a distinctly unimpressive number for something with Rayo's number's
reputation.

That extrapolation is wrong, but *why* it's wrong is the important part,
not just the reassurance. Every φ_k built here uses one specific strategy:
"x's members are exactly 0, 1, ..., k-1" — an explicit, one-at-a-time list,
essentially a unary encoding dressed in first-order logic. The real Rayo's
number does not count up to a googol one integer at a time. It uses first-
order logic's ability to *quantify over the entire universe of formulas and
proofs* to build something self-referential — roughly, "the smallest number
that no formula shorter than N symbols can name" (a rigorous, non-paradoxical
version of the Berry paradox, made to work via a careful satisfaction
predicate). That move doesn't enumerate anything; it harnesses the full
proof-theoretic strength of ZFC in one shot — the same way Busy Beaver's
enormous values don't come from counting, they come from exploiting the
entire space of possible machine behaviors through a completely different
mechanism than incrementing.

Why didn't naming 0 through 6 find that trick on its own? Because it isn't
available yet at that scale. Quantifying over "all formulas of bounded
length and their satisfaction" needs its own real bootstrapping cost —
plausibly comparable to or larger than the 90-line κ(R) artifact measured
below, and likely much larger, since a full formula-and-proof quantifier is
a strictly bigger undertaking than a bare satisfaction relation for
concrete sets. At a target as small as "six," that bootstrap cost would
dominate everything, so the run was forced into the boring
enumerate-explicitly regime — exactly what got measured. This is the same
phenomenon `KAPPA-TABLE.md`'s Phase 4 already found comparing *different*
systems R to each other (a cheap system pays disproportionately at the
bottom before its real power appears) — showing up here *within* one
system's own strategy space instead of between systems.

So: the worry that Rayo's number might be smaller than advertised is
justified *for the enumerate-one-at-a-time strategy specifically* — that
strategy really is this bad, forever, as far as the data and the structural
argument both suggest. It's exactly why the real construction reaches for
diagonalization instead. One honest limit: pinning down *at what k the
crossover happens* — where diagonalization starts beating naive enumeration
— would need formalizing "quantify over formulas of bounded length and
their satisfaction" in Lean, a serious step up from what exists here, closer
to the "large undertaking" `METHODOLOGY.md` already flagged as infeasible
for a full Rayo evaluator. That's a real open question, not a quick
follow-up — worth knowing where the edge of what's cheaply checkable is,
rather than guessing past it.

## The rules themselves: 90 lines, 556 tokens

Separately from n_k (the cost of naming a *specific* number), there's
κ(R) — the cost of specifying the *rules of the game itself*: the grammar
of these formulas, plus the machinery that decides whether a formula is
true. This had been marked "infeasible to pin exactly" in the project's
main `KAPPA-TABLE.md`, because building a full evaluator for first-order
set-theoretic truth is a serious undertaking on its own.

This run built one anyway, as a real, exhibited artifact rather than an
estimate: a self-contained Lean formalization needing no external library
(`rayo-lean/Rayo/Syntax.lean`, the formula grammar, 30 lines; and
`Satisfaction.lean`, a model of finite sets plus the Tarski truth
definition, 60 lines) — **90 lines, 556 tokens total**. That's a different
unit from the BLC-bit estimates used for the other five systems in
`KAPPA-TABLE.md` (Turing machines, lambda calculus, the Bashicu Matrix
System, etc.), so it's recorded alongside that table rather than merged
into it — converting between "Lean source lines" and "BLC bits" honestly
isn't something either number licenses.

## One correction along the way

While researching background for this, the run caught an error in the
project's own prompt: it had said the real-world "Big Number Duel" (the
event that produced Rayo's function in the first place) happened in 2013.
It didn't — it was **26 January 2007**, Agustín Rayo versus Adam Elga at
MIT. The "2013" traces to an unrelated piece of commentary by a different
person. Caught and corrected with citations, not just asserted.

## What this does and doesn't tell you about Rayo's actual number

Nothing quantitative — Rayo's number itself uses a *googol*-symbol budget,
where this kind of "pay for everything before you" bootstrapping cost is a
rounding error. What it does confirm, concretely rather than by analogy, is
the same qualitative point the main project found for every other system in
`KAPPA-TABLE.md`: bootstrapping is expensive relative to a tiny budget, and
the *rules* (κ(R)) are comparatively cheap — 90 lines gets you the entire
apparatus of "what does a first-order sentence about sets mean," while just
*counting to six* inside that apparatus already costs over eleven thousand
symbols.
