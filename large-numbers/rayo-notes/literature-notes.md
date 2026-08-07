# Literature notes: prior published work on Rayo / FOST formula lengths

Purpose: record what prior published work says about (a) the Big Number Duel
and Rayo's construction, and (b) the specific quantities this run is trying to
pin down — kappa(R) for FOL-over-`in`, and the minimal symbol counts n_k of the
cheapest formula naming each small natural k. This is the Phase-A literature
sweep. It records sourced numbers where they exist and, where they do not, an
explicit "searched, found nothing citable" so later phases do not re-cover the
same ground expecting a citation to appear.

Method: web search (August 2026) over Wikipedia, Googology Wiki (Fandom and
Miraheze mirrors), OEIS, Rayo's MIT publication page, and general web search for
minimal-formula-length / symbol-count results for small naturals. Primary
sources fetched where reachable; two (OEIS A368006, Miraheze mirror) returned
402/403 and are cited from search-result summaries only, flagged below.

## 1. The Big Number Duel — provenance and a date correction

The contest was the **Big Number Duel**, Agustín Rayo (MIT) vs **Adam N. Elga**
(then/soon Princeton), held at MIT on **26 January 2007** — *not* 2013 as the
item's framing supposed. Multiple independent sources agree on 2007:

- Wikipedia, "Rayo's number": "defined it during a 'Big Number Duel' at the
  Massachusetts Institute of Technology (MIT) on 26 January 2007."
- Googology Wiki, "Big Number Duel": same event, Rayo vs Elga, Rayo won with
  what is now "Rayo's number".
- The Tech (MIT student newspaper), V126 N64, "Profs Duke It Out in Big Number
  Duel" — contemporaneous coverage.

The "2013" association is a separate event: in January 2013 Adam P. Goucher
discussed Rayo(n)'s growth rate versus his xi function. That is commentary on
the function, not the Duel, and is where the 2013 date in the item's premise
most plausibly came from. **Recorded as a correction to the item's premise.**

## 2. The microlanguage (published alphabet and Sat machinery)

Published descriptions of Rayo's construction fix the microlanguage alphabet as:

    ∈ , = , ¬ , ∧ , ∃ , ( , )   plus a countable supply of set variables.

(Sources: Googology Wiki "Rayo's number"; Wikipedia describes the same
construction rules — atomic formulas `x_i ∈ x_j` and `x_i = x_j`, negation,
conjunction, existential quantification, "It is not allowed to eliminate
parentheses.") Semantics is given by a Tarskian satisfaction predicate `Sat`,
and a number m is "named" by a formula φ(x₁) with x₁ its only free variable when
(a) some assignment sending x₁→m satisfies φ, and (b) every satisfying
assignment sends x₁→m (unique denotation).

**This matches `notes/convention-notes.md` exactly**: our primitive alphabet
`{ in, =, not, and, exists, forall, ( , ) }` + variables, with `∀` obtained as
`¬∃¬` and `∨/→/↔/∃!` as abbreviations, is the standard published microlanguage
(our extra listing of `forall` is a definitional convenience; published Rayo
takes ∀ as derived, which is consistent with our expansion rule). So the alphabet
side of our convention is externally corroborated, not idiosyncratic.

Primary source for the Sat construction: Agustín Rayo, "On Specifying
Truth-Conditions," Philosophical Review (MIT copy at web.mit.edu/arayo/www/fc.pdf).
The PDF is not machine-text-extractable via our fetch tool (binary/FlateDecode),
so it is cited by reference, not quoted.

## 3. What prior work does NOT provide (the core gap this run fills)

**No published source gives minimal FOST formula lengths n_k for specific small
naturals k = 0, 1, 2, ...**, nor a worked cheapest formula φ_k(x) with a symbol
count, under any fixed counting convention. Searched and **found nothing
citable** for question (2):

- Wikipedia "Rayo's number": gives the definition and construction rules but
  "provides no explicit example formulas naming specific numbers like 0, 1, 2,
  or 3, nor symbol counts for such examples" (confirmed by fetch).
- Googology Wiki (Fandom) "Rayo's number" and its Talk page: discuss the
  definition, the alphabet, and growth-rate/uncomputability, but do not tabulate
  per-k minimal formula lengths.
- General web search for minimal symbols to name small numbers in FOST / von
  Neumann formula length: returned only definitional and ordinal-background
  material, nothing on per-k minimal lengths (searched Aug 2026).
- OEIS **A368006** ("Rayo's function"): this is the *Rayo function* Rayo(n)
  (largest number nameable in ≤ n symbols) — an uncomputable output sequence, the
  *inverse-flavoured* quantity to ours. It is **not** a table of n_k (symbols to
  name k). So it does not answer question (2) either. (Cited from search summary;
  oeis.org/A368006 returned HTTP 403 to our fetcher, not directly read — flagged.)

Consequence for this run: the per-k counts n_k (Phase C) appear to be genuinely
new mechanized numbers, not a reproduction of a published table. That is
expected — the literature treats Rayo's construction as an existence/growth-rate
object (how large can n symbols reach), not as a golfing problem (how few symbols
to pin a *given* small k). This asymmetry is itself the finding.

## 4. On kappa(R) (question 1)

No prior published source pins kappa(R) — the size of "the rules" (FOL-over-`in`
grammar + satisfaction/evaluation machinery) — as a concrete number in any fixed
unit, let alone the BLC-bit unit `KAPPA-TABLE.md` uses. Rayo's paper gives the Sat
construction in prose/logic, not as a measured interpreter. So the existing
`KAPPA-TABLE.md` lower bound stands as the prior state of the art; **found
nothing citable** that supersedes or refines it. Refining it is this run's job,
not a matter of locating a citation.

## 5. Citable sources (bibliography)

- Agustín Rayo, "On Specifying Truth-Conditions," *The Philosophical Review*
  117(3), 2008. MIT copy: https://web.mit.edu/arayo/www/fc.pdf  (primary; Sat
  machinery / microlanguage). Not text-extracted here.
- Rayo's MIT publications page: https://philpeople.org/profiles/agustin-rayo
- "Rayo's number," Wikipedia: https://en.wikipedia.org/wiki/Rayo's_number
  (definition, construction rules, Duel date 26 Jan 2007). Fetched.
- "Rayo's number," Googology Wiki (Fandom):
  https://googology.fandom.com/wiki/Rayo's_number  (microlanguage alphabet, Sat).
- "Big Number Duel," Googology Wiki:
  https://googology.fandom.com/wiki/Big_Number_Duel  (Rayo vs Elga, 2007).
- "Profs Duke It Out in Big Number Duel," The Tech (MIT), V126 N64:
  http://tech.mit.edu/V126/N64/64largenumber.html  (contemporaneous coverage).
- OEIS A368006, "Rayo's function": https://oeis.org/A368006  (Rayo(n) values,
  not n_k; cited from search summary, not directly fetched — 403).

## 6. Summary

- The Duel was **2007 at MIT, Rayo vs Elga**; the item's "2013" is a misdating
  (2013 = Goucher's growth-rate commentary). Sourced correction.
- The published microlanguage alphabet **matches our frozen convention**, so the
  alphabet choice is externally corroborated.
- For the two quantities this run computes — kappa(R) (Q1) and per-k minimal
  formula lengths n_k (Q2) — the literature sweep **found nothing citable**:
  prior work defines the construction and the growth-rate function but never
  tabulates the cheapest formula for a *given* small k, nor a measured kappa(R).
  These are new mechanized results, not reproductions.
