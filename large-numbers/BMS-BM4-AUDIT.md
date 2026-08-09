# Auditing the BM4 well-ordering preprint (arXiv:2307.04606), lemma by lemma

Companion to [`LADDER.md`](LADDER.md) rung 5 (Bashicu matrix numbers) and
the multi-row-BMS row of [`KAPPA-TABLE.md`](KAPPA-TABLE.md). LADDER's rung 5
tags BM4's termination as **disputed** because it "rests on one unrefereed
2023 preprint." This file is the promised independent, on-paper audit of
that preprint, unit by unit, so the `disputed` tag is backed by an actual
reading rather than by reputation.

The paper: **"Well-Orderedness of the Bashicu Matrix System"**,
[arXiv:2307.04606](https://arxiv.org/abs/2307.04606), math.LO, MSC 03E10,
CC BY-SA 4.0. Submitted 2023-07-10 (v1), revised 2023-07-11 (v2) and
2024-10-11 (v3, current). Its single theorem is "BMS is well-ordered."

## Provenance first: it is one paper, one author, no second proof

Before the mathematics, a bookkeeping point that the secondary sources
routinely garble and that matters for the "one unrefereed preprint" framing:

- The current arXiv metadata lists the author as **Rachel Hunter**, with a
  note that "the author name was corrected in a subsequent revision."
- Adam P. Goucher's cp4space blog ("Miscellaneous discoveries",
  2023-07-23) and the official arXiv `math.LO` announcement both attribute
  the *same* arXiv id to **Samuel Vargovčík**.
- The ResearchGate copy (publication 372248920) carries DOI
  `10.48550/arXiv.2307.04606`, i.e. it is the arXiv paper, not a second
  work.

So "Hunter" and "Vargovčík" are the same author under a name correction,
and the arXiv and ResearchGate items are the same paper. Automated search
summaries that report "an independent proof appeared the following day"
(Vargovčík vs Hunter) or a separate proof "by Kosuke Miyoshi" are
conflating these copies; there is **no** corroborating second proof. The
epistemic position is exactly one unrefereed preprint, as LADDER rung 5
already states. (Confirming a genuine second independent proof *would* be a
material update; none exists.)

Expert reception, for the record and consistent with LADDER: Goucher calls
it "A very exciting paper... [that] proves the well-orderedness of a
conjectured system of ordinal notations" and treats it as credible. That is
a positive informal assessment by a competent reader, not peer review.

## How this audit was conducted, and its honest ceiling

The paper was read through arXiv's experimental HTML rendering
(ar5iv). The access tool returns faithful *structural* content: it gave the
statements of Definition 1.1, Lemmas 2.1–2.6 and Theorem 2.7, the
definition of the stability relation `<_n`, the ordinal `σ`, the notion of
"stable representation," and the order function `o`. It **declined to
reproduce the full expansion rule and the full proof text verbatim**
(copyright), so I do **not** hold a character-for-character copy of every
formula and every proof line.

The consequence, stated plainly so no verdict below is over-read: I can
assess **the logical shape of each argument** (what is being claimed, what
it is reduced to, whether the reduction is valid, whether the cited
external results are real and say what is needed). I **cannot** certify
every index computation inside the expansion rule, nor every line of the
Lemma 2.6 reflection construction, because certifying those requires the
verbatim symbols I could not extract. Where a verdict turns on symbols I
could not see, it is recorded as **could not verify**, with the exact
reason, never as a pass. A global rubber-stamp is explicitly refused.

Verdict vocabulary, per the item's instruction:
- **verified**: the argument's logic is sound as extracted and I can see
  why it holds;
- **gap found**: a step is missing, wrong, or unjustified as extracted;
- **could not verify**: the step may well be correct, but confirming it
  needs detail I could not obtain, and I say exactly what detail.

---

## Definition 1.1: is this a faithful BM4 formalization?

**What the paper defines.** An *array* is a sequence of equal-length
sequences of natural numbers, i.e. an element of `(ℕⁿ)ᵐ` (m columns, each of
height n). It defines, by comparing element values down columns, the
notions *m-parent* and *m-ancestor* of a column, and an *expansion*
operation `A[n]` that decomposes `A` as `G + B₀ + (C)` (a good part, a
bad-root block, and the final column `C`), then emits
`G + B₀ + B₁ + … + Bₙ`, where the copies `B₁,…,Bₙ` are the bad part
repeated with the ascending elements increased by `i·(differences of the
m-th elements)`. BMS is the closure of the seeds
`X₀ = {((0,…,0)_n,(1,…,1)_n) : n ∈ ℕ}` under expansion at every `n ∈ ℕ`,
partially ordered by `A[n] ≤ A`.

**Assessment: could not verify (faithfulness), with the structure
matching.** The extracted skeleton is the right shape for BM4: BM4's
defining behaviour is exactly "find the bad part relative to the last
column, copy it `n+1` times, and increment the ascending (non-zero-parent)
entries by a multiple of the pointwise difference," and the parent/ancestor
relation by descending element comparison is the standard BMS device.
Nothing in the extracted definition contradicts BM4.

But *faithfulness to BM4 specifically* is a claim about the exact
increment/copy arithmetic, and BM4's whole reason for existing is that the
three previous rulesets (BM1–BM3) got that arithmetic subtly wrong and
admitted non-terminating inputs (LADDER rung 5). BM4 is pinned down by a C
program (`basmat.c`, the community fix BM2.3). Certifying that Definition
1.1's `i·(differences of the m-th elements)` rule reproduces `basmat.c`
input-for-input is precisely the symbol-level check the access tool
prevented (it would not emit the verbatim expansion rule), and it is also a
check the paper itself does not perform against the C source. So:

- The formalization is *structurally* a BM4 formalization, not a BM1–BM3
  one, and covers the standard seeds (hence covers Bashicu's number as
  currently defined). **verified at the structural level.**
- Bit-for-bit equivalence of Definition 1.1's expansion arithmetic with
  `basmat.c` / BM2.3 is **could not verify**: the paper asserts rather than
  proves this equivalence (LADDER already flags "equivalent to BM2.3 by
  code analysis, itself an unproven equivalence"), and I could not read the
  verbatim rule to independently check it. This is the first and most
  load-bearing "could not verify," because a well-ordering proof of a
  *different* system than BM4 would be a faithful theorem about the wrong
  object.

---

## Lemmas 2.1–2.4: the lexicographic-order argument

### Lemma 2.1: `A[n] <_lex A`

**Statement (as extracted).** For all `A ∈ BMS` and `n ∈ ℕ`, `A[n]` is
lexicographically smaller than `A`, where columns are themselves compared
lexicographically.

**Proof (as extracted).** With `A = G + B₀ + (C)` and
`A[n] = G + B₀ + B₁ + … + Bₙ`, the two arrays agree on the prefix
`G + B₀`; at the first place they differ, the `m₀`-th element of `R₁` (the
first column of `B₁`) is shown strictly smaller than the `m₀`-th element of
`C`.

**Assessment: verified (logic), modulo the increment arithmetic.** The
argument shape is exactly right and is the correct crux: lexicographic
comparison is decided at the first differing column, `A[n]` shares the
prefix `G + B₀` with `A`, and the first genuinely new column `R₁` is a
copy of the bad root, whose pivot (`m₀`-th) entry sits strictly below the
corresponding entry of the deleted final column `C`. If that single strict
inequality holds, the lemma follows immediately, and the reduction to that
one inequality is valid. The strict inequality itself is a fact about the
increment arithmetic of Definition 1.1 (the copies start *below* `C` and
climb toward it), which is the same verbatim rule I could not extract; that
one inequality is therefore **could not verify** at the symbol level,
though it is the expected and standard behaviour of a BMS expansion. Net:
the lemma's *architecture* is verified; it rests on one arithmetic
inequality I could confirm structurally but not symbol-by-symbol.

### Lemma 2.2: `A′ < A ⇒ A′ <_lex A`

**Assessment: verified.** `<` on BMS is the transitive closure of single
expansion steps `A[n] ≤ A`. Lemma 2.1 makes each step strictly
`<_lex`-decreasing, and `<_lex` is a transitive order, so any finite chain
of steps is `<_lex`-decreasing end to end. This is a clean corollary and
the deduction is valid as stated.

### Lemma 2.3: BMS is totally ordered

**Statement/Proof (as extracted).** BMS is totally ordered; proved by first
showing `X₀` is totally ordered, then induction showing that closing under
expansion preserves totality, using e.g.
`((0,…,0)_n,(1,…,1)_n) = ((0,…,0)_m,(1,…,1)_m)[1]…[1] < ((0,…,0)_m,(1,…,1)_m)`
for `n < m`.

**Assessment: verified (structure); one inductive step could not be fully
verified.** Totality of `X₀` is clear (the seeds are linearly ordered by
height, and the displayed identity exhibits each shorter seed as an
iterated `[1]`-expansion of a taller one, hence `<` it: consistent with
Lemma 2.1). The induction "closure under expansion preserves totality" is
the right proof structure. What I cannot fully verify is the trichotomy
bookkeeping in the inductive step: that *any two* arrays produced anywhere
in the closure are comparable requires comparing expansions of possibly
different parents at possibly different indices, and that case analysis
depends on the verbatim expansion rule. The skeleton is sound; the
exhaustiveness of the internal case split is **could not verify**.

### Lemma 2.4: the BMS order coincides with the lexicographic order

**Assessment: verified (as a deduction).** Given Lemma 2.2 (`A′ < A ⇒
A′ <_lex A`) and Lemma 2.3 (`<` is total), coincidence follows by a
standard argument: two total orders on the same set, one refining the other
in one direction, must agree (if `A′ <_lex A` but not `A′ < A`, totality
gives `A < A′`, so by 2.2 `A <_lex A′`, contradicting antisymmetry of
`<_lex`). The inference is valid; it inherits the "could not verify"
residue of 2.1/2.3 but adds no new gap.

**Why this block is not yet well-ordering.** Correctly noted by the paper's
overall structure: `<_lex` on finite arrays is *not* well-founded on its
own (lexicographic order can descend forever by lowering an early column).
Lemmas 2.1–2.4 only establish that BMS's order *is* the lexicographic one;
the actual well-ordering must come from the ordinal embedding in Theorem
2.7. So this block is a faithful reduction, not a smuggled conclusion. That
the paper does not mistake 2.4 for the theorem is itself a good sign.

---

## Lemma 2.5: invariance of the ancestor structure under expansion

**Statement (as extracted).** Five properties saying the m-ancestor
relations are copied consistently by expansion: ancestor relations between
`G` and `B₀` match those between `G` and `Bₙ`; internal relations within
`B₀` match those within each `Bₙ`; and cross-copy relations between
successive `Bᵢ` are consistent.

**Assessment: could not verify, plausibly routine.** This is a structural
bookkeeping lemma: expansion copies the bad part, so the ancestor graph of
each copy should mirror the original, with the declared cross-copy links.
That is exactly what one expects and needs for Theorem 2.7 (the ordinal
assignment must see a repeating, well-controlled ancestor pattern). But it
is entirely a claim about how the verbatim expansion rule relabels
ancestors, so I cannot confirm the five clauses individually without the
rule. Recorded as **could not verify (bookkeeping)**; no reason to suspect
it is false, and it is the natural bridge from the combinatorial half
(2.1–2.4) to the set-theoretic half (2.6–2.7).

---

## Lemma 2.6: the Σ-reflection heart, cross-checked against Kranakis

This is the load-bearing lemma and the paper's real content: everything
combinatorial above is standard, and Theorem 2.7 is a routine consequence
*given* 2.6. So the credibility of the whole proof concentrates here.

**Set-up (as extracted).** For `L_α` the α-th level of the constructible
hierarchy, write `α ≤_n β` for
`⟨L_α, ∈⟩ ⪯_{Σ_{n+1}} ⟨L_β, ∈⟩` ("`L_α` is a `Σ_{n+1}`-elementary
substructure of `L_β`"), with `<_n` the strict version. Let `σ` be the
least ordinal `α` such that there is a `β` with `∀ n ∈ ℕ (α <_n β)`.

**Statement (as extracted).** For all `α, β ∈ σ` and `n ∈ ℕ`, if
`ω < α <_n β`, then for all finite `X, Y ⊆ Ord` with `γ < α ≤ δ < β` for
all `γ ∈ X`, `δ ∈ Y`, there is a finite `Y′ ⊆ Ord` and a bijection
`f : Y → Y′` such that (roughly): (1) `γ < f(δ₀) < α`; (2)
`γ <_k δ₀ ⇒ γ <_k f(δ₀)`; (3) `δ₀ < δ₁ ⇒ f(δ₀) < f(δ₁)`; (4)
`δ₀ <_k δ₁ ⇒ f(δ₀) <_k f(δ₁)`; (5) for `m < n`,
`δ₀ <_m β ⇒ f(δ₀) <_m α`.

**Proof (as extracted).** Constructs `Σ_{n+1}` formulas expressing the
relevant `<_k` facts and reflects them from `L_β` down into `L_α` using the
`Σ_{n+1}`-elementarity `α <_n β`; the definability of the `<_k` relations
at the right level of the arithmetical/analytical-over-`L` hierarchy is
supplied by **Kranakis, Theorem 1.8**, cited as giving that the `<_k`
relations are `Π_{k+1}`.

**Cross-check against Kranakis 1982: the citation is real and apt.** The
reference is E. Kranakis, *"Reflection and partition properties of
admissible ordinals,"* Annals of Mathematical Logic **22** (1982) 213–242.
That paper is squarely about `Σ_n`/`Π_n` reflection and the definability
complexity of stability relations among ordinals in `L`, and results of the
form "the `n`-stability relation is `Π_{n+1}` (and complete at that level)"
belong to exactly this circle of ideas (the same material the googology
"stable ordinal" literature draws on). So the *external input exists, is
correctly attributed, and states the kind of complexity fact the proof
needs*: this dependency is not vaporware. **verified: the Kranakis citation
resolves to a real, relevant theorem of the right form.**

**Assessment: could not verify (the construction), citation sound.** The
strategy is the correct and standard one for this genre of well-ordering
proof: use `Σ_{n+1}`-elementarity between two levels of `L` to pull a
finite configuration of ordinals down below `α` while preserving the
stability relations, so that arbitrarily tall arrays get order-preserving
ordinal images. The five conditions are the natural closure conditions such
a pull-down must satisfy (order, strict stability up and down, and the
`m < n` downward transfer that drives the induction in 2.7). None of the
five looks wrong or redundant.

What I cannot verify is the *actual construction of the reflecting
`Σ_{n+1}` formulas and the verification that `α <_n β` transfers each
clause*, in particular:
- that each `<_k` condition needed inside the proof genuinely sits at
  `Σ_{n+1}` (not higher) for the relevant `k ≤ n`, so that `Σ_{n+1}`-
  elementarity actually applies: this is where an off-by-one in the
  complexity bookkeeping would break the proof, and it is exactly the point
  the Kranakis `Π_{k+1}` bound is invoked to control;
- that the bijection `f` can be chosen to satisfy *all five* clauses
  simultaneously (clauses (2)/(4)/(5) are stability constraints that can
  compete with the mere order constraint (3)).

Confirming these needs the verbatim formula construction, which I could not
extract, and honestly also needs a careful line reading against Kranakis's
actual Theorem 1.8 statement (I confirmed the paper *exists* and is *on
point*, not its Theorem 1.8's exact hypotheses). This is the audit's
central **could not verify**, and it is where any real error in the paper
would most plausibly hide. It is also, note, the step that forces the
metatheory up to `Σ_n`-stable ordinals in `L`: far beyond arithmetic:
which is why even *well-definedness* of BM4 is epistemically expensive.

---

## Theorem 2.7: BMS is well-ordered

**Statement/Proof (as extracted).** Define `o : BMS → Ord`. A *stable
representation* of an array `A` of length `n` is a function `f : n → Ord`
with `i < j ⇒ f(i) < f(j)` and, whenever the `i`-th column is an
`m`-ancestor of the `j`-th column, `f(i) <_m f(j)`. Set `o(A)` = the least
`α` bounding the outputs of some stable representation of `A`. One shows `o`
is total and strictly order-preserving on `X₀` by induction, then extends
across expansions using Lemma 2.6's reflection, so `o` embeds `(BMS, <)`
order-preservingly into `(Ord, <)`; since `Ord` is well-ordered, so is BMS.

**Assessment: verified (top-level logic), contingent on 2.5/2.6.** The
top-level implication is impeccable and is the standard route to
well-ordering: *any* strictly order-preserving map from a linear order into
the ordinals proves that order is well-ordered (a descending chain would
map to a descending ordinal chain, impossible). So if `o` is (a) total:
every array has at least one stable representation: and (b) strictly
order-preserving, the theorem follows. Both (a) and (b) are discharged by
the induction, whose inductive step is exactly Lemma 2.6 (reflection lets a
stable representation of `A` be converted into one for `A[n]` with smaller
bound, giving `o(A[n]) < o(A)` and matching Lemma 2.4's `<_lex`). The
architecture is correct and the reduction of the theorem to 2.6 is valid.

Therefore Theorem 2.7 is **verified as a deduction from Lemmas 2.4–2.6**,
and its soundness is *exactly as strong as Lemma 2.6*, which I could not
line-verify. There is no independent weakness in 2.7 itself; it neither
over-claims nor hides a second gap. It simply inherits the 2.6 ceiling.

---

## Overall verdict

**No error found; not independently certified; verdict unchanged at
`disputed`.**

Assembling the per-unit results:

- The combinatorial half (Def 1.1, Lemmas 2.1–2.4) is structurally sound
  and is a faithful *reduction* (BMS order = lexicographic order), correctly
  *not* mistaken for well-ordering. Its only residual gaps are symbol-level:
  the exact BM4 expansion arithmetic and its equivalence to `basmat.c`,
  which the paper asserts and I could not read verbatim.
- The set-theoretic half rests entirely on **Lemma 2.6**, whose *strategy*
  is the correct standard one and whose *external citation* (Kranakis 1982)
  is real and apt, but whose *actual `Σ_{n+1}` reflection construction* I
  could not verify line by line: and that is the single place a genuine
  error would most likely live.
- **Theorem 2.7** is a valid deduction from 2.4–2.6; it adds no new risk and
  is exactly as sound as 2.6.

So the audit finds the proof **coherent, correctly structured, and free of
any error I could detect**, while being unable to independently certify its
load-bearing lemma. Combined with the standing facts that the paper is
**unrefereed, unmechanized, depends on `Σ_n`-stable ordinals in `L`**
(a strong set-theoretic metatheory, far beyond arithmetic), asserts rather
than proves its BM4/`basmat.c` faithfulness, and has exactly one (favorable
but informal) expert reading and no corroborating second proof, the honest
tag is unchanged: **disputed**.

This is not a downgrade or an upgrade of LADDER rung 5's verdict: it is the
same verdict, now *earned by a unit-by-unit reading* rather than asserted
from reputation. What the audit specifically adds to rung 5:

1. The "one public challenger admitted to not reading it" framing stands,
   but the more useful fact is positive: on a genuine structural reading the
   proof holds together and its only cited external dependency checks out.
2. The precise location of the irreducible uncertainty is now named: it is
   **Lemma 2.6's `Σ_{n+1}` reflection construction** and the
   **Definition 1.1 ↔ `basmat.c` faithfulness**, not the (routine)
   combinatorics or the (routine) final deduction. A future formalization
   or referee should spend its effort there.
3. Provenance corrected: "Hunter" and "Vargovčík" are one author/one paper;
   there is no independent second proof to lean on.

## Sources

- Paper: [arXiv:2307.04606](https://arxiv.org/abs/2307.04606),
  "Well-Orderedness of the Bashicu Matrix System" (read via ar5iv HTML;
  the full expansion rule and full proof text could not be extracted
  verbatim, which bounds this audit as stated above).
- Kranakis: E. Kranakis, "Reflection and partition properties of admissible
  ordinals," *Annals of Mathematical Logic* 22 (1982) 213–242 (citation
  confirmed real and topically correct; its Theorem 1.8 not read verbatim).
- Expert reception: A. P. Goucher, cp4space, "Miscellaneous discoveries,"
  2023-07-23.
- Prior project context: [`LADDER.md`](LADDER.md) rung 5,
  [`KAPPA-TABLE.md`](KAPPA-TABLE.md) multi-row-BMS row.
