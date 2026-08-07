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
