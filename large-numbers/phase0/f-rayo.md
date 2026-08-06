# Phase 0 evidence: Googology Wiki's ranking of Rayo's-function variants

**Reference system R.** Rayo's function is the R = first-order set theory
diagonalizer: `Rayo(n)` = the least integer above every integer nameable by a
formula of the language of first-order set theory in `n` symbols or fewer;
Rayo's number is `Rayo(10^100)`. The "variants" here are the family of named
googologisms that keep Rayo's shape (a definability/satisfaction diagonalizer
over a *language of set theory*) but swap in a richer language or a stronger
metatheory: Fish number 7, BIG FOOT / FOOT, Little Bigeddon, Sasquatch (Big
Bigeddon), and the Large Number Garden Number (LNGN). This item records the
*ordering* Googology Wiki asserts among them and, for each link, whether that
ordering rests on a cited proof, a cited external claim, or unsourced
consensus. It is the Rayo-family companion to `phase0/e-foot.md`, which handled
the FOOT/BIG FOOT-vs-Rayo comparison in isolation.

**Source(s) fetched:** the canonical Googology Wiki pages
- `https://googology.fandom.com/wiki/Largest_valid_googologism` (the ranking narrative)
- `https://googology.fandom.com/wiki/Rayo's_number`
- `https://googology.fandom.com/wiki/BIG_FOOT`
- `https://googology.fandom.com/wiki/Little_Bigeddon`
- `https://googology.fandom.com/wiki/Sasquatch`
- `https://googology.fandom.com/wiki/Large_Number_Garden_Number`
- `https://googology.fandom.com/wiki/Category:Numbers_based_off_of_Rayo's_number`
- mirrors: `https://googology.miraheze.org/wiki/Largest_valid_googologism`, `.../Little_Bigeddon`, `.../Sasquatch`

**Fetched:** 2026-08-06 (during item i_a8cc17d471c2). **Provenance caveat
(same as `phase0/e-foot.md`):** direct page fetches were **NOT obtainable** from
this environment. `googology.fandom.com` returns HTTP 402; the
`googology.miraheze.org` mirror returns HTTP 403. The wording quoted below is
transcribed from **WebSearch result extractions** of those pages (a fast-model
read of search-engine snippets/summaries), **not from a verbatim page fetch**.
Treat quoted phrases as faithful-in-substance but not guaranteed word-for-word;
spot-check against the live wiki before using as exact quotations.

**Status: PARTIAL / search-derived.** The ordering and its sourcing were
consistent across every source that surfaced (Fandom pages, Miraheze mirror,
NamuWiki, Quora restatements), but were reconstructed from search extractions,
not fetched page text (see caveat). The one *mathematical* fact leaned on here
(the ill-definedness refutation) is a cited proof-style result, so it is stable
independent of the fetch problem.

## 1. The ordering the wiki asserts

The "Largest valid googologism" page narrates a single succession of title
claims. Restricted to the Rayo-shaped variants, the **asserted growth chain** is:

> **Rayo's number  <  Fish number 7  <  BIG FOOT  <  Little Bigeddon  <  Sasquatch**

with the **Large Number Garden Number (LNGN)** presented as the *current*
well-defined title holder standing above Rayo's number (LNGN is not placed in a
proven relation to the ill-defined entries; it wins by being the largest one
**not shown ill-defined**).

Dates / authors as the wiki gives them:

| variant | author | date | language / metatheory move over Rayo |
|---|---|---|---|
| Rayo's number | Agustín Rayo | 2007 | baseline: first-order set theory |
| Fish number 7 | Fish (Kyodaisuu) | 2013 | "adds an oracle formula to the original microlanguage" |
| BIG FOOT = `FOOT^10(10^100)` | LittlePeng9 / Wojowu | 2014 | diagonalizes over "first-order oodle theory", a generalization of nth-order set theory |
| Little Bigeddon | Emlightened | 2017-01-05 | set theory + an extra "rank variable" |
| Sasquatch (Big Bigeddon) | Emlightened | 2017-03-27 | further-extended set theory; "too difficult for anyone else to understand" |
| LNGN | P進大好きbot | 2019-12 | large-cardinal / extended-theory diagonalizer; current well-defined ceiling |

## 2. The basis of each link (the point of this item)

| ordering link | basis on the wiki | verdict |
|---|---|---|
| Fish 7 > Rayo | author claim; "some controversy regarding whether it is significantly larger than Rayo's number", so "never officially recognized as the largest valid googologism" | **author assertion, contested; NOT a cited proof** |
| BIG FOOT ≫ Rayo | definition-author (Wojowu) construction argument; "completely dethroned Rayo's number ... enormously larger than Rayo's number" | **author assertion, construction-motivated; NOT a cited proof** (and later refuted, see §3) |
| Little Bigeddon > BIG FOOT | author (Emlightened) claim; "was supposed to be larger than BIG FOOT" | **author assertion; NOT a cited proof** (now moot: both ill-defined) |
| Sasquatch > Little Bigeddon | author (Emlightened) claim; not verified by the community, "not officially considered to be the title holder yet" | **author assertion, unverified consensus** |
| LNGN > Rayo | author (P進大好きbot) claim; accepted because "it hasn't been proven that it is ill-defined, and thereby it should be considered largest" | **community consensus by absence-of-refutation; NOT a cited domination proof** |

**Net finding:** *none* of the Rayo-variant ordering links is backed by a cited
proof that one function dominates the next. Every "bigger than" is a
construction-motivated **author assertion**, ratified or withheld by community
consensus. Rankings move by acclamation and by *dis*proof, not by proof.

## 3. The only cited proofs in the area are refutations, not orderings

The single class of rigorous, cited results in this family removes entries
rather than ordering them: Googology Wiki user **P進大好きbot (p-adic)**'s
analysis "Ill-definedness of BIG FOOT, Little Bigeddon, and Sasquatch" shows
**first-order oodle theory is inconsistent** ("for any set theory T extending
ZFC, if FOOT is well-defined in T, then T is inconsistent"), so **BIG FOOT,
Little Bigeddon, and Sasquatch are all ill-defined** (Sasquatch separately, via
a circular definition of its `R`). The wiki states the consequence directly: the
"larger than Rayo's number" comparisons for these "do not make sense." (See
`phase0/e-foot.md` §2 for the FOOT half in full.)

So of the six Rayo-family variants, **three (BIG FOOT, Little Bigeddon,
Sasquatch) are ill-defined by a cited proof**; their growth is **undefined**,
not merely uncertain. Two well-defined anchors survive — **Rayo's number** and
**LNGN** — plus **Fish 7**, which is well-defined but whose margin over Rayo is
contested. LNGN is the current well-defined ceiling of the family (no larger
valid non-salad googologism established as of early 2026).

## 4. Bearing on the (kappa(R), growth) table

The Rayo family **cannot supply a monotone (kappa(R), growth) curve** from the
wiki's ranking, for two independent reasons:

1. **Half the variants have undefined growth.** BIG FOOT / Little Bigeddon /
   Sasquatch are ill-defined by a cited proof, so their `growth of BN(R,.)`
   column is undefined. They are ruled-out candidates R, exactly like FOOT in
   `phase0/e-foot.md`.
2. **The surviving order is folklore, not proof.** Even among the well-defined
   entries (Rayo, Fish 7, LNGN), the wiki's "bigger than" links are author
   assertions plus consensus, never a cited domination proof. This is precisely
   the "restated folklore" the project goal warns against pricing.

Usable for the table: **Rayo's number** and **LNGN** as two well-defined
Rayo-shaped anchors (LNGN > Rayo asserted but not wiki-proven), with Fish 7 as a
well-defined-but-contested third. Contrast `phase0/a-bbchallenge.md` (BB(1..5)
proven exact) and `phase0/c-pole-position.md` (BLC bits→growth, leaderboard-real):
those carry certified or leaderboard-real growth values, whereas the Rayo family
delivers at most an *ordinal-analysis* growth story per well-defined R, and its
inter-variant ranking is not proof-grounded at all.
