# Phase 0 evidence: Googology Wiki's FOOT / BIG FOOT comparison and ranking

**Reference system R.** FOOT = **First-Order Oodle Theory**, the oodle-theory
analogue of Rayo's first-order set theory. Where Rayo's function diagonalizes
over first-order formulas in the von Neumann universe V, the FOOT function
diagonalizes over "first-order oodle theory" = the language of set theory
augmented with two new symbols `[` and `]` ranging over a purported larger
domain of discourse, the *oodleverse*. **BIG FOOT** is the named number
`FOOT^10(10^100)` (ten-fold iterate of FOOT applied to a googol). Defined 2014 by
Googology Wiki user **LittlePeng9 (a.k.a. Wojowu)**. So as a candidate R for the
project's `(kappa(R), growth)` table, FOOT sits in the same family as Rayo's R
(first-order theory + a definability/satisfaction diagonalizer) but claims a
strictly larger interpretive universe.

**Source(s) fetched:** the canonical Googology Wiki pages
- `https://googology.fandom.com/wiki/BIG_FOOT`
- `https://googology.fandom.com/wiki/Largest_valid_googologism`
- `https://googology.fandom.com/wiki/User_blog:LittlePeng9/First_order_oodle_theory` (the FOOT/BIG FOOT definition)
- `https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Ill-definedness_of_BIG_FOOT,_Little_Bigeddon,_and_Sasquatch` (the refutation)
- mirror: `https://googology.miraheze.org/wiki/BIG_FOOT`, `.../Largest_valid_googologism`

**Fetched:** 2026-08-06 (during item i_a9c3a49ec138). **Important provenance
caveat:** direct page fetches were **NOT obtainable** from this environment.
`googology.fandom.com` returned HTTP 402; the `googology.miraheze.org` mirror,
`grokipedia.com`, `en.namu.wiki`, and `web.archive.org` all returned HTTP 403 or
were blocked. The wording quoted below is therefore transcribed from **WebSearch
result extractions of those pages** (a fast-model read of search-engine snippets
and summaries), **not from a verbatim page fetch**. Treat quoted phrases as
faithful-in-substance but not guaranteed word-for-word; spot-check against the
live wiki before using as exact quotations.

**Status: PARTIAL / search-derived.** The ordering claims and their sourcing
(below) are consistent across every source that surfaced, but were reconstructed
from search extractions rather than fetched page text (see caveat above). The
central mathematical fact used here (FOOT ill-defined because first-order oodle
theory is inconsistent) is a proof-style result, not live data, so it is stable.

## 1. The growth-rate ordering the wiki asserts

The **historically asserted** ordering, at the time BIG FOOT was defined (2014):

> "BIG FOOT was created by Wojowu and completely dethroned Rayo's number,
> diagonalizing over a generalization of nth-order set theory known as
> first-order oodle theory, and is **enormously larger than Rayo's number**."

i.e. the claimed chain was **BIG FOOT ≫ Rayo's number**, with FOOT's function
placed strictly above Rayo's function. Two adjacent claimed links:

- **Little Bigeddon ≫ BIG FOOT** — Little Bigeddon (user Emlightened, 2017-01-05)
  "was supposed to be larger than BIG FOOT" and briefly held the "largest valid
  googologism" title.
- **Fish number 7 vs Rayo** — Fish number 7 (2013, a high-order Rayo function)
  "upstaged" Rayo debatably; "never officially recognized" because of dispute
  over whether it is a good-enough extension.
- **Oblivion / Utter Oblivion vs BIG FOOT** — Jonathan Bowers claimed these
  (diagonalizing "over the fundamental concept of a mathematical system as a
  whole") are larger than both BIG FOOT and Rayo, but they are "generally not
  accepted."

## 2. The basis of each ordering (the point of this item)

The item asks whether each ranking rests on a **cited proof**, a **cited
external claim**, or **unsourced wiki consensus**. The answer is specific and it
matters for the project:

| ordering claim | basis on the wiki | verdict |
|---|---|---|
| BIG FOOT ≫ Rayo (2014) | the *definition author's* construction argument: FOOT's oodleverse generalizes nth-order set theory, which out-runs Rayo's first-order V. No independent proof. | **author assertion, construction-motivated; NOT a cited proof** |
| Little Bigeddon ≫ BIG FOOT (2017) | claimed by that number's author (Emlightened) | **author assertion; NOT a cited proof** |
| Fish 7 vs Rayo | community judgement, explicitly "debatable"/"controversy" | **unsourced wiki consensus (and contested)** |
| Oblivion/Utter Oblivion ≫ BIG FOOT | Bowers' own claim, "generally not accepted" | **author claim, rejected by consensus** |

The one place a real **cited proof** enters is the *refutation*, not the ordering:

> Googology Wiki user **P進大好きbot (p-adic)** posted the analysis blog
> "Ill-definedness of BIG FOOT, Little Bigeddon, and Sasquatch," showing that
> **first-order oodle theory is inconsistent**: "for any set theory T extending
> ZFC set theory, if FOOT is well-defined in T, then T is inconsistent."

Consequence, stated on the wiki: BIG FOOT (and FOOT) is **ill-defined**; the
"larger than Rayo's number" comparison "does not make sense," and the same
collapse voids the Little Bigeddon ≫ BIG FOOT link. Sasquatch is separately
ill-defined (circular definition of its `R`). So the growth-rate *ordering* was
never proof-backed; the only rigorous result in the area is a proof that the
whole comparison is vacuous.

## 3. Bearing on the (kappa(R), growth) table

FOOT / BIG FOOT **cannot supply a certified growth-rate data point.** Its
reference system (first-order oodle theory) is *inconsistent by a cited proof*,
so the "growth rate of BN(FOOT, .)" column is **undefined**, not merely unknown.
The entire selling point of FOOT for the project's thesis — that a Rayo-shaped,
low-`kappa(R)` specification could buy an *enormous* jump in growth over Rayo —
turns out to rest on an **author assertion that was formally refuted**, which is
exactly the "restated folklore" the project goal warns against pricing.

Net for the table: list FOOT/BIG FOOT as a **ruled-out / ill-defined candidate
R** with growth = undefined, alongside a note that its would-be neighbour Rayo's
number remains the well-defined ceiling in this family. Contrast with
`phase0/a-bbchallenge.md` and `phase0/c-pole-position.md`, whose entries (BB,
BLC) carry *proven or leaderboard-real* growth values; FOOT is the phase-0
example of a candidate that fails the "grounded in real proof data" bar outright.
