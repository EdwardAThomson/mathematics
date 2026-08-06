# Phase 0 evidence: Googology Wiki's array-notation growth hierarchy

**Reference system R.** The **array notations** are a family of googological
notations whose R is "an array of numbers under a rewrite rule," generalizing
Conway's chained-arrow notation: **BEAF** (Bowers' Exploding Array Function,
Jonathan Bowers) and its rigorous cousin **Bird's Array Notation (BAN)** (Chris
Bird, 2010-2014, an extension of Bowers' Extended Array Notation). These are the
canonical "array notation" R's on Googology Wiki. This item records the
*growth-rate ordering* the wiki asserts across the array-notation hierarchy
(linear < multidimensional < tetrational < ... arrays) and, for each level,
whether the ordering rests on a **cited proof**, a **cited external claim**, or
**unsourced consensus**. It is the array-notation companion to the Rayo-family
files `phase0/e-foot.md` and `phase0/f-rayo.md` (the "oodle" half of the item's
"oodle / array-notation" scope is those two files; FOOT = First-Order **Oodle**
Theory is a Rayo-shaped diagonalizer, not an array notation, so it lives there).

**Source(s):**
- `https://googology.fandom.com/wiki/Array` (array-hierarchy overview)
- `https://googology.fandom.com/wiki/Array_notation`
- `https://googology.fandom.com/wiki/Bowers'_Exploding_Array_Function` (BEAF)
- `https://googology.fandom.com/wiki/Bird's_array_notation` (BAN)
- `https://googology.fandom.com/wiki/Introduction_to_BEAF`
- **`https://mrob.com/users/chrisb/Fast-Growing_Hierarchy.pdf`** — Chris Bird,
  "The Fast-Growing Hierarchy in Terms of Bird's Array Notations" (the primary
  cited-proof artifact; see §2)
- mirrors: `https://googology.miraheze.org/wiki/Array`, `.../Bird's_array_notation`

**Fetched:** 2026-08-06 (during item i_f1f60b2cc595). **Provenance — this file
differs from `e-foot.md`/`f-rayo.md`: the key proof artifact was fetched and read
directly, not search-derived.** The `googology.fandom.com` pages returned HTTP
402 (same block as the earlier items), so the *wiki's own wording* below is
transcribed from **WebSearch result extractions** of those pages (faithful in
substance, not guaranteed verbatim; spot-check before quoting). BUT the anchoring
mathematical evidence — Bird's PDF `Fast-Growing_Hierarchy.pdf` — **was fetched
successfully (mrob.com, HTTP 200) and its pages 1-3 were read directly** (PDF
extraction), so the FGH correspondences in §2 are quoted from the actual source
document, not from search snippets.

**Status: MIXED — wiki narrative search-derived; the load-bearing proof fetched
and read directly.** The ordering claims are consistent across every source that
surfaced (Fandom, Miraheze mirror). The lower-hierarchy FGH correspondences are
backed by Bird's read-in-full derivation (a cited proof). The upper hierarchy is
flagged ill-defined by wiki consensus.

## 1. The ordering the wiki asserts

The array notations climb a single hierarchy indexed by the "shape" of the array,
each level asserted strictly faster than the one below, with fast-growing
hierarchy (FGH) limit ordinals attached:

| array level | FGH limit ordinal (wiki) | well-defined? |
|---|---|---|
| linear arrays | **ω^ω** | yes |
| multidimensional arrays | **ω^(ω^ω)** | yes |
| tetrational arrays | **ε₀** | yes — the largest BEAF level with an agreed-upon definition |
| pentational arrays and above | (informally assigned) | **NO — no agreed-upon definition** |

Wiki wording (search-extracted): "In the fast-growing hierarchy, linear and
multidimensional array notations have limit ordinals ω^ω and ω^(ω^ω),
respectively." "Tetrational arrays are the largest arrays in BEAF that are fully
known how they work, and they have a growth rate of f_ε₀(n)." "There is no
agreed-upon definition for the notation above tetrational arrays. Therefore,
strictly speaking, BEAF beyond tetrational arrays is ill-defined, although BEAF
below that level is well-defined."

## 2. The basis of each level (the point of this item)

| ordering claim | basis | verdict |
|---|---|---|
| linear arrays ≈ f_{ω^ω} (and each linear step) | **Chris Bird's derivation** in `Fast-Growing_Hierarchy.pdf`, read directly (below) | **CITED PROOF (Bird's own derivation)** |
| multidimensional arrays ≈ f_{ω^(ω^ω)} | Bird's derivation continues into `[2]`-separator (multi-dimensional) notation, §3 of PDF | **CITED PROOF (Bird's derivation)** |
| tetrational arrays ≈ f_{ε₀} | community analysis; "the largest part of BEAF with an agreed-upon definition"; boundary of what is "fully known how they work" | **consensus + partial analysis; not a single cited theorem in-hand here** |
| pentational arrays and above (BEAF) | "Bowers didn't properly define pentational arrays, so his notation at this point and higher isn't well-defined"; growth rates for these are assigned by an informal "analysis of how powerful BEAF should be" that "does not use the climbing method" | **unsourced consensus / informal; NOT proof (level is ill-defined)** |

**The cited proof, quoted from the fetched PDF** (Chris Bird, *The Fast-Growing
Hierarchy in Terms of Bird's Array Notations*, mrob.com, pages 1-3, read
directly). Bird derives explicit FGH correspondences with worked inequalities:

- `f_ω(n) = {2, n, n-1}` (Bird's Linear Array Notation); "the lowest function in
  the fast-growing hierarchy that is not primitive recursive"; "the
  single-argument Ackermann function grows as rapidly as f_ω(n)."
- `f_{ω+1}(64) > {3,3,{3,3,{...{3,3,4}...}}}` (64 pairs of brackets) **=
  Graham's Number** — i.e. f_{ω+1} already passes Graham.
- `f_{ω²}(n) = f_{ωn}(n) > {n,n,n,n} ≥ n→n→...→n` (n entries) **= Conway's
  Chained Arrow Notation** — so Conway chained arrows sit at ≈ f_{ω²}.
- `f_{ω^k}(n) > {n,n,n,...,n}` (with k+2 n's) — so the full **linear** array
  notation spans up to ≈ **f_{ω^ω}**, matching the wiki's ω^ω claim.
- **Bird's Multi-Dimensional Array Notation** (a number in square brackets `[m]`
  denotes a separator) picks up at `f_{ω^ω}(n) > {n, n+2 [2] 2}` and climbs
  onward — matching the ω^(ω^ω) claim for multidimensional arrays.

So for the **linear and multidimensional** levels the growth-rate ordering is
backed by an actual, publicly posted **derivation** (Bird's), the strongest
sourcing in the whole phase-0 googology sweep. This is a real proof artifact, not
restated folklore. (BAN and BEAF agree on linear and multidimensional arrays;
`[m]` in Bird = an `(m-1)` separator in Bowers.)

## 3. Where it stops being defined

Above tetrational arrays (≈ ε₀) the notation **runs out of an agreed
definition.** Bowers never rigorously defined pentational arrays and beyond, so
BEAF at that level and higher is **ill-defined** by wiki consensus — the same
failure mode as FOOT/BIG FOOT in `phase0/e-foot.md`, but from under-specification
rather than a proven inconsistency. Growth rates people attach to those levels
come from an informal "how powerful it *should* be" analysis (explicitly "does
not use the climbing method"), which is a heuristic, not a proof. Bird's own
notation is more abstractly specified and his later documents push the analyzed
range far higher (his "Beyond Bird's Nested Arrays" work uses a θ ordinal
collapsing function reaching around the Bachmann-Howard ordinal), but that is
Bird's construction, distinct from Bowers' ill-defined upper BEAF.

## 4. Bearing on the (kappa(R), growth) table

The array notations give the phase-0 table its **best-sourced growth data point
in the sub-ε₀ range, and a clean well-defined/ill-defined cutoff**:

1. **Usable, proof-backed anchors.** Linear array notation ≈ **f_{ω^ω}** and
   multidimensional ≈ **f_{ω^(ω^ω)}** are backed by Bird's read-in-full
   derivation. Unlike the Rayo family (§ `f-rayo.md`), whose inter-variant order
   is pure author-assertion-plus-consensus, the array hierarchy's lower rungs
   carry a *cited proof of their FGH placement*. Tetrational arrays ≈ **f_{ε₀}**
   is well-defined but rests on consensus/partial analysis, not one cited theorem
   here.
2. **A ruled-out ceiling.** Pentational arrays and above (BEAF) are **ill-defined
   by consensus** (Bowers never defined them), so their growth column is
   **undefined**, like BIG FOOT — but for a different reason (under-specification,
   not proven inconsistency).

For the table: enter **linear / multidimensional / tetrational arrays** as
well-defined array-notation R's with FGH growth f_{ω^ω} / f_{ω^{ω^ω}} / f_{ε₀}
(the first two proof-cited via Bird), and mark **pentational+ BEAF** as a
ruled-out ill-defined candidate. This sits *below* the Rayo/BB tier in growth but
*above* it in sourcing quality at the linear/multidimensional levels — a useful
low-`kappa(R)`, mid-growth, high-confidence row against which the expensive
Rayo-shaped systems can be priced. Contrast `phase0/a-bbchallenge.md` (BB proven
exact) and `phase0/c-pole-position.md` (BLC leaderboard-real): the array
notations are the phase-0 example of a *cited-derivation* growth value (Bird's
PDF) rather than a certified-search or exact-proof value.
