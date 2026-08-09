# The ladder, audited: is each famous number actually well-defined?

Companion to [`KAPPA-TABLE.md`](KAPPA-TABLE.md). That table priced the
*systems*; this one walks the famous *numbers*, rung by rung, and asks the
question this project keeps finding is the real one: **what does it cost to
know the number exists at all?**

Each rung records four things:

1. **Defining system**: the notation or construction the number comes from.
2. **The well-definedness theorem**: the mathematical fact that guarantees
   the definition picks out one specific natural number.
3. **Metatheoretic strength**: how strong a theory you need to *prove* that
   fact. This is the interesting column: the project's throughline predicts
   it should climb with the ladder.
4. **Status**: one of
   - `project-audited`: verified by this project (mechanized or
     paper-verified here),
   - `literature-solid`: a celebrated published theorem we did not re-derive,
   - `disputed`: the field itself disagrees or the history contains patched
     counterexamples,
   - `ill-defined`: checked and found broken.

A standing caution inherited from the whole project: wiki claims are chased
to their actual cited sources before being repeated here. Where a rung's
entry rests on something we could not verify, the entry says so.

---

## The rungs

Audit date: August 2026.

| # | number | defining system | well-definedness rests on | strength needed | status |
|---|---|---|---|---|---|
| 1 | Graham's number | Knuth up-arrow recursion | totality of the up-arrow (Ackermann-type) recursion | IΣ₂, far below PA | **literature-solid** |
| 2 | Goodstein-type numbers | Goodstein sequences | Goodstein's theorem (descent below ε₀) | PA + TI(ε₀); unprovable in PA (Kirby-Paris 1982) | **literature-solid** |
| 3 | TREE(3) | labeled finite trees | Kruskal's tree theorem, Friedman's finite form | small Veblen level (~ACA₀ + Π¹₂-BI); already beyond ATR₀ unlabeled | **literature-solid** (theorem); magnitude claims are FOM folklore |
| 4 | SCG(13) | subcubic graph sequences | wqo of subcubic graphs (graph-minor machinery) | beyond Π¹₁-CA₀; GMT provable just above it (Krombholz-Rathjen) | **literature-solid** (theorem); number claims are FOM folklore |
| 5 | Bashicu matrix numbers | BMS expansion rules (BM4, the 4th ruleset; BM1-BM3 all refuted) | termination of BM4: one unrefereed 2023 preprint | the only proof uses Σₙ-stable ordinals in L, far beyond arithmetic | **unrefereed; core lemma line-verified by this project** ([`BMS-BM4-AUDIT.md`](BMS-BM4-AUDIT.md) addendum) |
| 6 | Loader's number | Calculus of Constructions (`loader.c`) | strong normalization of CoC | higher-order-arithmetic strength (unprovable there; ZFC proves it easily) | **literature-solid** |
| 7 | BB(n) (Busy Beaver) | k-state Turing machines | Radó: finitely many machines | trivial to define; specific values independent of ZFC | **literature-solid** |
| 8 | BoolosBig_PA | provability-naming over PA | B0 well-definedness proof | PA-strength | **project-audited** (mechanized, sorry-free) |
| 9 | Rayo's number | truth-naming over FOST | R0 analysis | **MK-strength**, and only granted that commitment | **project-audited** (paper; conditional) |
| 10 | BIG FOOT | "FOOT" (first-order oodle theory) | claimed, not delivered | n/a | **ill-defined** (project-audited: its own cited source disproves it) |
| 11 | Fish numbers 1-6 | Ackermann extensions, s/m maps; F4 adds a Busy-Beaver oracle | ordinary recursion theory; F4 via oracle machines in ZFC | low: ordinal induction below ζ₀; F4's oracle is ZFC-definable | **literature-solid** (print-published, undisputed) |
| 12 | Fish number 7 | Rayo's micro-language + function oracles, iterated transfinitely | Rayo's machinery, unchanged | the same MK-strength commitment as Rayo, inherited | **conditional**, exactly as Rayo (community-accepted as a genuine extension) |
| 13 | Little Bigeddon | FOST + rank variables + transfinitely iterated truth predicate | claimed; the posted text contains fatal errors | would exceed MK (iterated truth over V) if repaired | **ill-defined** (consensus; plausibly repairable, never repaired) |
| 14 | Sasquatch / Big Bigeddon | HOD/class-forcing language construction | the author's own unproven conjecture | unclear | **ill-defined** (consensus; circular definitions) |
| 15 | Oblivion / Utter Oblivion | "the largest number definable in any well-defined system of mathematics" | nothing: no fixed language for "system" | n/a | **ill-defined** (Berry-type regress; unformalizable as conceived) |
| 16 | Large Number Garden Number | FOST + a predicate U, over an explicitly declared theory T ⊇ MK | the declared theory itself; Con(T) from ZFC + a Grothendieck universe | explicitly declared, which is the whole point | **community-solid**: current "largest valid googolism", no published refutation |

---

## Per-rung notes

Each note states what the claim rests on, against which source, and what
could not be verified. Confidence tags: **[PP]** proven and published,
**[SF]** standard folklore (expert-asserted, unrefereed), **[CNV]** could
not verify.

### Graham's number (rung 1): literature-solid

Well-definedness is trivial: 64 nested applications of a total computable
recursion. Totality of the general up-arrow/Ackermann function is
unprovable in IΣ₁ (whose provably-total functions are exactly the primitive
recursive ones) but provable in IΣ₂, a small fragment of PA [SF, textbook
proof theory]. One documented wrinkle: the number in Graham-Rothschild's
actual 1971 paper is the much smaller "Little Graham" F⁷(12); the famous G
= g₆₄ comes from Gardner's 1977 Scientific American article, from an
unpublished argument of Graham's [PP for the 1971 bound; well-documented
for the provenance story].

### Goodstein numbers (rung 2): literature-solid

Well-defined by Goodstein's theorem (1944): each sequence maps to a strictly
descending ordinal sequence below ε₀ [PP]. Kirby-Paris (1982): unprovable
in PA [PP]. The Goodstein function is essentially the Hardy hierarchy at
ε₀ (Cichon 1983), so it dominates every PA-provably-total function, which
puts it in the same growth class our Boolos fork tops out at. Note ACA₀
does not help (conservative over PA); you need TI(ε₀) itself.

### TREE(3) (rung 3): literature-solid, with a garble warning

Well-defined by Kruskal's tree theorem with finite labels (1960) plus
Friedman's finite-form move [PP]. Strength, precisely, because popular
accounts garble it: the Γ₀/ATR₀ unprovability belongs to *unlabeled*
Kruskal (Friedman via Simpson 1985) [PP]; labeled Kruskal calibrates
exactly at the small Veblen ordinal ϑ(Ω^ω), the ordinal of (Π¹₂-BI)₀
(Rathjen-Weiermann 1993) [PP]. The famous magnitude claims for TREE(3)
itself (dominates ACA₀ + Π¹₂-BI provably-total functions, absurd proof
lengths) trace to Friedman's FOM postings, never refereed [SF]. Two common
garbles: "TREE(3) is at Γ₀/ATR₀ level" (wrong, that's unlabeled Kruskal)
and "TREE(3) needs the gap condition / Π¹₁-CA₀" (wrong, that machinery
belongs to SCG).

### SCG(13) (rung 4): theorem solid, number claims folklore

Defined by Friedman (FOM posts #274/#279, April 2006). Well-defined because
subcubic graphs are wqo under homeomorphic embedding, which follows from
graph-minor machinery [PP for the wqo input]. Strength: the graph minor
theorem, already for bounded tree-width, is unprovable in Π¹₁-CA₀
(Friedman-Robertson-Seymour 1987) [PP]; a recent two-sided calibration
puts GMT just above Π¹₁-CA₀ (Krombholz-Rathjen, arXiv:1907.00412) [PP].
Everything numeric about SCG(13) specifically is Friedman FOM folklore
[SF], and the primary FOM archive links 404'd during this audit, so even
the exact SCG-vs-SSCG attribution is [CNV] at the primary-source level.

### Bashicu matrix numbers (rung 5): unrefereed, core lemma line-verified here

The version history is exactly the cautionary tale it smelled like:

- **BM1 (2014), BM1.1, BM2 (2016), BM3 (2018): all refuted.** Each has an
  explicit non-terminating input, found by community members (Hyp cos,
  koteitan/Bubby3, Alemagno12), in BM3's case within days of release. A
  2016 claimed termination proof for BM1 (KurohaKafka) was disproved by
  counterexample. Numbers defined against these versions, including the
  original 2014 Bashicu's number, are not well-defined.
- **BM4 (2018), the current official version** (equivalent to the
  community fix BM2.3 by code analysis, itself an unproven equivalence):
  termination/well-ordering is proven only in an unrefereed arXiv preprint
  (arXiv:2307.04606, 2023; read structurally for this audit, see
  [`BMS-BM4-AUDIT.md`](BMS-BM4-AUDIT.md) for exactly what could and could
  not be line-verified). The proof is
  serious: it maps BMS order-preservingly into the ordinals using
  Σₙ-stable ordinals in the constructible hierarchy L, so even the
  *well-definedness proof* requires a strong set-theoretic metatheory, and
  the paper itself lists a self-contained combinatorial proof as open. It
  has stood three years with no identified error and a positive expert
  assessment (Goucher), but no peer review, no formalization, and its one
  public challenger admitted to not reading it. Scope caveat: the theorem
  covers matrices reachable from the standard seeds (which does cover
  Bashicu's number as currently defined), not arbitrary seed matrices.
  A dedicated lemma-by-lemma audit
  ([`BMS-BM4-AUDIT.md`](BMS-BM4-AUDIT.md)), in two passes, ends
  substantially in the paper's favor. First pass (structural, via ar5iv):
  the combinatorial half is sound, Theorem 2.7 is a valid
  ordinal-embedding deduction, the Kranakis 1982 citation is real and
  topically apt, no error found, but the load-bearing **Lemma 2.6** could
  not be line-verified. Second pass (full LaTeX source from arXiv):
  **Lemma 2.6 is now line-verified**. Its single reflected-formula
  construction discharges all five clauses at once, its complexity
  bookkeeping is exactly right (the `m < n` restriction is precisely the
  `Π_{m+1} ⊆ Σ_{n+1}` boundary, and the `α, β < σ` hypothesis is what
  makes the formula finite), and the one fact cited from Kranakis's
  unreachable text was independently re-proved in the audit's addendum, so
  nothing rests on its wording. Remaining residue: the paper's "Of course"
  seed-representation step (needs `n`-stable pairs below `σ`, asserted not
  proven), exhaustive checking of Lemma 2.5's tedious cases, and the
  asserted **Definition 1.1 ↔ basmat.c/BM2.3 faithfulness**. The audit
  also corrects the provenance: "Rachel Hunter" (current arXiv metadata)
  and "Samuel Vargovčík" (announcement-era mirrors) are one author and one
  paper under a name correction, so there is exactly one unrefereed
  preprint and no corroborating second proof.
- **The solid fragments**: 1-row (primitive sequences) is textbook, order
  type ε₀. 2-row (pair sequences) has a rigorous, detailed 2018 community
  proof (p進大好きbot, ~142 pages in translation) bounding the order type
  by Buchholz's ordinal ψ₀(Ω_ω) [SF: vetted but never journal-published].
- **Ordinal strength of the full system: unknown.** No proven value, no
  rigorously stated conjecture. The "PTO of Z₂" label attached to BMS in
  some sources (including the Tromp landmark our `KAPPA-TABLE.md` row
  cites) is community aspiration, not theorem; the wiki's own article
  says analyses past a certain point "should only be treated as lists of
  conjectures". Note for `KAPPA-TABLE.md`: the ψ(Ω_ω) figure it lists for
  multi-row BMS is actually the proven bound for the *2-row fragment*;
  the full system's ordinal is simply open.

Bottom line: Bashicu's number K = Bm¹⁰(9) against BM4 is well-defined
*conditional on one unrefereed preprint whose core lemma this project has
now line-verified*. Still no peer review, no formalization, and no second
proof, so it remains the weakest computable rung; but after the audit the
honest tag is "unrefereed, core lemma line-verified here" rather than
bare "disputed".

### Loader's number (rung 6): literature-solid

`loader.c` computes D⁵(99), bounded proof search over the Calculus of
Constructions; it halts because CoC is strongly normalizing. SN of CoC has
multiple independent published proofs (Coquand's thesis; Geuvers-Nederhof
1991; Geuvers 1994/95) [PP]. Strength: SN(CoC) ⟺ SN(Fω) (Geuvers-Nederhof)
[PP], and SN(Fω) implies consistency of full higher-order arithmetic, so
well-definedness is unprovable in higher-order arithmetic itself and needs
(a fragment of) set theory; ZFC proves it with room to spare [pieces PP,
packaged statement SF]. The magnitude analyses (D(99) > 2↑↑30419 etc.) are
Moews's contest-page estimates, explicitly without full proof [SF]. The
oft-repeated story that Coquand's original SN proof had an error later
repaired could not be verified in this audit [CNV].

### Busy Beaver (rung 7): literature-solid, the "unknowable" rung

Well-definedness is Radó 1962 and is trivial: finitely many n-state
machines, so the max over halting ones exists [PP]. The interesting
phenomenon is the opposite of the other rungs: definition is cheap, but
*values* are independent of strong theories. BB(7910) independent of ZFC
modulo a mild consistency hypothesis (Aaronson-Yedidia 2016) [PP]; BB(748)
via O'Rear's ZF-contradiction-searching machine [SF, code public,
unrefereed]; improved to BB(745) (Riebel, 2023 thesis) [SF]. A 2025
community claim pushes toward 432 states for ZF-minus-regularity but is
explicitly unverified [CNV]. Largest known value: BB(5) = 47,176,870,
machine-checked in Coq (bbchallenge, 2024) [PP]. This rung shows
well-defined and knowable come sharply apart.

### BoolosBig_PA (rung 8): project-audited

Well-definedness is the B0 result: finitely many formulas up to renaming at
each size, each provably naming at most one number, so the max exists
([`BOOLOS-B0-WELLDEFINEDNESS.md`](BOOLOS-B0-WELLDEFINEDNESS.md), mechanized
core in [`BoolosB0Core.lean`](rayo-lean/Rayo/BoolosB0Core.lean)). The
counting-up-to-renaming subtlety was a real catch: without it the
construction is infinite (`METHODOLOGY.md` C8). Growth: eventually dominates
every PA-provably-total monotone function, fully mechanized
([`BoolosBig.lean`](rayo-lean-boolos/RayoBoolos/BoolosBig.lean)).

### Rayo's number (rung 9): project-audited, conditional

The R0 finding ([`RAYO-R0-WELLDEFINEDNESS.md`](RAYO-R0-WELLDEFINEDNESS.md)):
consistent, and names a specific number, but only relative to an MK-strength
commitment (a truth predicate for V, which Tarski forbids first-order set
theory from supplying for itself). Grant the commitment and the number is
real; withhold it and the construction names nothing. The popular
description states no such condition.

**Precedent correction, found by this audit.** The MK-strength observation
is *not* absent from all prior literature, as this project earlier
believed. It is documented inside the googology community's technical wing,
essentially all of it authored by wiki user p進大好きbot from 2018 onward,
in one place naming MK exactly: "even (first order) MK set theory is
sufficient... ZFC set theory is not sufficient for this purpose, even if we
allow to use a Platonist universe" (user blog, "Whether Rayo's number is
well-defined or not"). The wiki's own Rayo article now concludes the number
is "well-defined for googologists who do not care about clarification of
axioms and is ill-defined for googologists who care", and Rayo's own 2020
note concedes the standard-interpretation dependence. What remains true:
the point is invisible in every mainstream account (Wikipedia included),
and R0 was derived independently and reaches the same verdict. But it is a
rediscovery of the community's best analysis, not a first: this file and
the project's other claims of novelty are corrected accordingly.

### BIG FOOT (rung 10): ill-defined

Checked during Part 1 against the proof its own wiki article cites; the
cited source disproves the claim. Recorded in `KAPPA-TABLE.md` and
`FINDINGS.md`. Kept on the ladder as the cautionary rung: climbing past
Rayo requires a rigorously specified stronger language, and this attempt's
language wasn't.

### Fish numbers (rungs 11-12): solid below Rayo, conditional at Rayo

Fish numbers 1-6 (Japanese googologist "Fish", 2002-2013) are the honest
workhorses of the ladder's middle: computable recursions (F1-F3, F5, F6,
growth from ~f_{ω²} up to ζ₀ level) plus one Busy-Beaver-oracle variant
(F4), all rigorously defined, several print-published, none disputed. Fish
number 7 extends Rayo's micro-language with function oracles and iterates
transfinitely; the community examined and *accepted* it as a genuine
(non-naive) extension that really beats Rayo. Its status is therefore
precisely Rayo's: well-defined modulo the same inherited MK-strength
commitment, no worse and no better. One honest caveat from the community's
own talk pages: since nobody can attach an ordinal to Rayo's function, all
"F7 ≈ R_{ζ₀}" strength claims are heuristic.

### Little Bigeddon and Sasquatch (rungs 13-14): ill-defined

Both by wiki user Emlightened (2017); both displaced BIG FOOT in community
esteem for a time; both now consensus-ill-defined after concrete errors
were found (p進大好きbot):

- **Little Bigeddon** (FOST + a rank sort + a transfinitely iterated truth
  predicate T): as literally written, T's defining condition is vacuously
  false (so the construction collapses rather than extends Rayo), two
  Gödel-code expressions are undefined or typos, and an evaluation map is
  never defined. The errors look repairable, and an independent strength
  analysis (Deedlit11) suggests the *intended* construction is coherent,
  but the author left the community and no repaired canonical version
  exists. If repaired, it would need strictly more than Rayo's commitment:
  iterated truth predicates over V through the ordinals.
- **Sasquatch** (a HOD/class-forcing construction): deeper defects. Its
  functions R and F are defined circularly (each conditioned on
  satisfaction in a structure that contains them), its formulas provably
  lack an interpretation in (V, ∈), and the author's own post *conjectures*
  rather than proves that the construction picks out unique objects. The
  post even opens "I'm not going to be quite as rigorous as my last post."
  Never accepted as a record holder even before the critique.

### Oblivion and Utter Oblivion (rung 15): ill-defined, unrepairable

Bowers's constructions quantify over "all complete and well-defined
systems of mathematics describable in n symbols" with no fixed language
for what a "system" is, no criterion for "well-defined", and no semantics
for "defined within a system". That is Berry's paradox territory: exactly
the informal totality Rayo's construction was engineered to avoid
quantifying over. Unlike the Bigeddons there is no formal core to repair;
formalizing "all systems" into one language would just reproduce a
Rayo-style construction and lose the intent. Community verdict: "amorphous
thought experiments", not numbers.

### Large Number Garden Number (rung 16): the ladder's current top

By p進大好きbot (2019), the same author whose critiques demolished the rest
of the post-Rayo tier, and it practices what those critiques preach: it
**declares its base theory explicitly** (FOST plus a predicate U, over a
stated theory T extending MK, with Con(T) provable from ZFC plus one
Grothendieck universe) instead of gesturing at "truth" or "all systems".
The community recognizes it as the current largest valid googolism; no
published refutation exists. Whatever one thinks of its size claims, its
*form* is the ladder's lesson distilled: past Rayo, a number is exactly as
well-defined as the theory it names out loud.

---

## What the ladder shows

1. **Strength buys existence, all the way up.** The metatheory needed just
   to *know each number exists* climbs monotonically: IΣ₂ (Graham), PA +
   TI(ε₀) (Goodstein), small Veblen (TREE(3)), beyond Π¹₁-CA₀ (SCG),
   higher-order arithmetic (Loader), stable ordinals in L (BMS, per its
   only proof), PA-as-metatheory (Boolos), MK (Rayo, Fish 7), a declared
   extension of MK (LNGN). This extends the project's throughline (the
   commitment axis from `KAPPA-TABLE.md`'s diagonalization family) across
   the whole canon: how sure you can be a number exists and how fast it
   grows are governed by the same variable.

2. **The theorems are refereed; the numbers are folklore.** On nearly
   every rung the underlying well-definedness theorem is published, solid
   mathematics, while the specific numeric and magnitude claims (TREE(3)'s
   size, everything about SCG(13), Loader's magnitude, the newest BB
   independence records, BMS's ordinal) trace to unrefereed sources: FOM
   mailing-list posts, contest pages, theses, wiki blogs, one arXiv
   preprint. Googology's famous numbers live almost entirely in the gray
   literature.

3. **Above Rayo, everything died of ill-definedness until someone
   declared their axioms.** BIG FOOT, Little Bigeddon, Sasquatch, and
   Oblivion all fell, each for a specifiable technical reason, and the
   sole surviving record holder (LNGN) is the one built on an explicitly
   stated theory. The failures and the fix agree with this project's
   R0/throughline analysis: past first-order set theory, "which
   metatheory?" *is* the definition.

4. **Busy Beaver is the deliberate inversion.** Everywhere else,
   definition is expensive and values are (in principle) computable; BB's
   definition is trivial while specific values are provably independent
   of ZFC. Well-defined and knowable come apart in both directions.

5. **Corrections this audit forced on the project itself:** the
   MK-strength observation about Rayo has community precedent
   (p進大好きbot, 2018 onward; see rung 9 note), so the project's novelty
   claim is downgraded to independent rediscovery; and `KAPPA-TABLE.md`'s
   multi-row-BMS row cites a ψ(Ω_ω) ordinal that is actually the proven
   bound for the 2-row fragment, with the full system's ordinal open (see
   rung 5 note).

## Sources

Load-bearing sources are cited inline in the per-rung notes. The audit was
run in August 2026 by three parallel research passes (combinatorial rungs;
BMS history; post-Rayo tier), each instructed to chase wiki claims to
their actual cited sources; claims that could not be so verified are
tagged [CNV] or flagged in place.
