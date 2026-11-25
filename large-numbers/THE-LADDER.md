# The ladder: where every big-number scheme sits, and why there is no top

**Status: synthesis note, 2026-11-24.** It assembles results of very
different standing. Each claim is tagged:

- **[Lean]** machine-checked in this repository;
- **[paper]** argued on paper in this repository, not machine-checked;
- **[classical]** standard textbook mathematics, cited from memory and not
  re-derived or checked here;
- **[expected]** what I believe is true and standard, but have neither
  proved here nor checked against a source.

Nothing in this note is claimed as new mathematics. What it offers is the
arrangement, and an answer to the question this project started with.

## 0. The conclusion

> **For any fixed rulebook there is a largest number nameable in N symbols.
> No rulebook is final.** Past the point where rules can describe
> computations, the way to get a faster-growing rulebook is always the same:
> take the notion of *truth* for the rulebook you have, which that rulebook
> cannot express, and add it as a new primitive. This costs a constant number
> of extra symbols and can be repeated without end. What it really costs is
> belief: each step asks you to accept a larger body of facts as definite
> that you have no means of checking.

So the question "what is the largest number you can write in N symbols?" has
no answer, and the question "how does the largest number grow, for a given
rulebook?" has an answer that is almost entirely determined by one thing:
how much truth the rulebook takes as given.

One refinement, from the work above Rayo (`ABOVE-RAYO.md` §5): once you
accept *all* truth about a domain, iterating the truth predicate adds no new
belief, only proof strength. The next real cost comes from enlarging the
domain: from the numbers to sets of numbers, or from the universe of sets to
all collections of sets (one more powerset level).

## 1. What a rulebook is

A **naming scheme** `R` consists of:

- a set of formulas, each with a size, with only finitely many of each size;
- a relation "`φ` names `k`" under which each formula names at most one
  number.

Then `BN_R(n) :=` the largest `k` named by some formula of size `≤ n` is a
well-defined, non-decreasing function (`BN-function.md`). **[paper; the
finiteness core is [Lean], `Rayo/BoolosB0Core.lean`]**

"Definite but not absolute": the value `BN_R(n)` depends on `R`. Nothing
stops anyone adding a symbol that abbreviates a huge number. The honest
comparison therefore charges for the rulebook as well, which is this
project's `κ(R)` (`METHODOLOGY.md`). What is robust is the *growth rate*:
two rulebooks that can each describe the other differ only by a fixed
overhead in the argument, the cost of that description.

## 2. The rungs

Each rung is described by what "names" is allowed to mean. Growth is given
relative to the rung below.

### Rung 0: computable schemes

*Names means:* the expression evaluates, by a terminating procedure, to the
number.

Decimal digits, power towers, Graham-style arrows, ordinal notations such as
the Bashicu Matrix System, typed lambda calculi such as System F and the
Calculus of Constructions. Each has a ceiling given by a specific ordinal,
and within this rung a longer rulebook does buy a higher ceiling
(`KAPPA-TABLE.md`: single-row BMS, multi-row BMS, System F / CoC). There are
infinitely many sub-rungs here, and it is where almost all of recreational
googology lives. **[classical for the ordinal assignments; the table itself is
this project's, with the caveats recorded there]**

*The wall above it:* computability. No scheme of this kind can outgrow every
computable function, since it is one.

### Rung 1: halting, or equivalently provability

*Names means:* "the run of this program halts and outputs the number", or
"some fixed theory proves this formula holds of the number and nothing else".

- Turing machines (Busy Beaver) and Binary Lambda Calculus. They eventually
  dominate every computable function. **[classical, Radó 1962]**
- Provable naming over PA. `BoolosBig_PA` is well defined and monotone
  **[Lean]** and eventually dominates every monotone PA-provably-total
  function **[Lean, `BoolosBig_PA_dominates`]**.
- `BoolosBig_PA` eventually dominates *every computable function*, with no
  provable-totality or monotonicity assumption, and so is not computable.
  **[Lean, `BoolosBig_PA_dominates_computable` and
  `BoolosBig_PA_not_computable` in `RayoBoolos/Minimization.lean`]**
- The same holds over *any* consistent, computably axiomatized theory
  containing a little arithmetic, and the function is sandwiched between
  Busy Beaver functions up to a rescaling of the argument. So all of these,
  whatever the theory, are the same rung. **[paper,
  `BOOLOS-IS-BUSY-BEAVER-CLASS.md`]**

*What you must accept:* that "this program halts" has a definite answer for
every program, including those where no proof either way exists. Equivalently
that "a proof exists" is definite. Almost every mathematician accepts this.

*Why stronger axioms do not climb out:* a weak theory can name the halting
time of any halting program, including the program that searches through a
strong theory's proofs.

### Rung k (k = 2, 3, 4, …): halting with oracles, or bounded arithmetic truth

*Names means:* "this program halts", for programs equipped with a box that
answers halting questions about rung `k − 1` programs. Equivalently: the
formula is a statement of arithmetic with `k − 1` blocks of "for all" (a `Π_{k−1}`
formula, or a `Σ_k` formula, which may put one more "there exists" block in
front), and it is *true* of the number and nothing else.

The two descriptions give the same growth class: naming by truth of `Π_{k−1}`
or `Σ_k` formulas, and Busy Beaver with the `(k−1)`-th halting oracle, bound
one another after a rescaling of the argument by at most `n log n`. A leading
"there exists" is free, because what it asserts exists can be packed into the
named number; each "for all" block costs one oracle level. The same holds for
provable naming in any theory that contains every true `Π_{k−1}` sentence,
which proves Aaronson's 2010 guess that this grows like `BB_{k+c}`.
**[paper, `MIDDLE-RUNGS.md`, every level; [Lean] for the bottom two levels and
the step between them, `RayoBoolos/TruthNaming.lean`]**

Rung 1 fits the same description with no "for all" at all: a provable
existential statement and a true existential statement are the same thing for
a theory that can check computations, which is why provability lands exactly
there. Truth of *bounded* formulas already reaches rung 1: a bounded formula
can say "`x` is the complete record of a halting run of program `e`".
**[paper, `MIDDLE-RUNGS.md` Theorem 1 at `k = 0`]**

### Rung ω: all of arithmetic truth

*Names means:* the formula is any statement of first-order arithmetic, and it
is true of the number and nothing else.

Dominates every finite rung, and is still beaten by Busy Beaver with the
full arithmetic-truth oracle `0^(ω)`, so it is a limit of the finite rungs
rather than an oracle Busy Beaver of its own. **[paper,
`GENERAL-NAMING-THEOREM.md` Theorem 8]**

*What you must accept:* that every statement about the whole numbers,
however many quantifiers it has, is definitely true or false. Equivalently,
that the whole numbers form a completed totality.

*The wall:* arithmetic cannot define its own truth (Tarski). **[classical]**

### Beyond: truth for richer and richer languages

The same step continues: truth for statements about sets of whole numbers
(second-order arithmetic), about sets of those, and so on up.

The first of these steps is now worked out (`SECOND-ORDER-RUNGS.md`, all
**[paper]**). Allow "for every set" or "there is a set" in the naming
formula. With one block of set quantifiers (`Π¹₁` or `Σ¹₁`, which give the
same rung, because number quantifiers become free) naming strictly outgrows
all of arithmetic truth, by more than any computable rescaling. Its growth
class is the Busy Beaver function for machines that may consult any
hyperarithmetic set (the halting problem iterated along any computable
well-ordering), paying for the oracle's description; so it beats every one of
those Busy Beavers and is their limit. Busy Beaver with oracle Kleene's `O`
is one jump too high: it beats this rung and is beaten by the next (`Σ¹₂`).
For every `k` the `Σ¹_k`/`Π¹_k` rung is the Busy Beaver over `Δ¹_k` oracles,
and each beats the one before. The Busy Beaver for infinite-time Turing
machines sits strictly between the `Π¹₁` and `Σ¹₂` rungs.

*What you must accept:* for `Π¹₁` only that well-foundedness of computable
trees is definite; for `Σ¹₂` nothing that differs between universes of sets
(Shoenfield). From `Σ¹₃` on, truth can differ between universes, so one must
accept a single intended collection of all sets of whole numbers.
**[classical]**

Large cardinals do not move any of these rungs, but from `Σ¹₃` on they
make the named numbers the same in every forcing extension (Woodin
cardinals), which lowers the price in the last sentence; see
`LARGE-CARDINALS-AND-THE-LADDER.md`. **[classical ingredients]**

Truth for arithmetic with a truth predicate, iterated, sits inside the `Π¹₁`
rung (each finite iteration is hyperarithmetic). **[expected]**

### The Rayo rung: truth for set theory

*Names means:* the formula is a statement of first-order set theory, true of
the number and nothing else.

Every rung below is describable by one formula of set theory, so Rayo's
function eventually dominates all of them. **[paper,
`RAYO-GROWTH-RATE.md`, for provably total functions and ordinal notations;
[expected] for the oracle rungs, by the same argument]**

*What you must accept:* that every statement about the entire universe of
sets is definitely true or false. Proving the function well defined for
every `n` at once needs a truth class for the universe. Morse–Kelley class
theory gives one, but a much weaker recursion principle (`ETR_ω` over GBC)
is enough. It does not matter which classes exist, provided the definition
only asks for truth up to the size in hand. **[paper,
`RAYO-R0-WELLDEFINEDNESS.md`, refined in `SECOND-ORDER-RAYO-II.md` §2–§3]**

### Above Rayo

Worked out on paper in `SECOND-ORDER-RAYO.md`, `SECOND-ORDER-RAYO-II.md` and
`ABOVE-RAYO.md` (all **[paper]**, not machine-checked). Every step above Rayo
is one of three kinds.

- **Parameter steps.** Give Rayo's language a symbol for one particular set
  or function, even Rayo's own function, and feed the result back in, as
  often as you like along a countable ordinal. This is how Fish number 7 is
  built. In arithmetic this kind of oracle climbs a rung, but in set theory
  every function on the numbers is already a set. So all of it sits strictly
  between Rayo and the next truth step (`ABOVE-RAYO.md` §1–§2).
- **Truth steps: the fine ladder.** Add a predicate for truth of the current
  language, and repeat, transfinitely ("Rayo+"). The same rungs appear if
  you allow "for every class" but restrict the classes to those definable
  after `β` rounds of truth: that gives exactly Rayo+ stage `β + 1`. With
  only the first-order definable classes it gives the first Rayo+ step. In
  set-theory terms these are the levels of the constructible hierarchy
  built over the universe. *What you must accept:* nothing new. Each stage
  is fixed once first-order truth about sets is fixed. Only the strength of
  the theory needed to *prove* the functions well defined goes up
  (`SECOND-ORDER-RAYO-II.md` §2–§3, `ABOVE-RAYO.md` §3).
- **Height steps.** Full second-order Rayo, where "for every class" means
  every sub-collection of the universe, beats every Rayo+ stage, even one
  iterated along all the ordinals. It is the same function as ordinary Rayo
  in a universe one powerset level taller. Third-order Rayo is two levels
  taller, and so on. So the higher-order ladder is the ladder of universe
  heights continued past the top of the universe (`SECOND-ORDER-RAYO-II.md`
  Theorem C). Rayo in a still taller universe beats all of these, but only
  if the smaller universe can be described from inside it. A small universe
  whose height cannot be described can even name faster than the real one
  (`ABOVE-RAYO.md` §4). *What you must accept:* now something new: a
  definite answer to which collections of sets exist, or a definite taller
  universe.

Above each height step a new fine ladder of truth steps starts, then the next
height step. If the height of the universe is very tall in the reflecting
("indescribable") sense, short formulas cannot tell it from a shorter
universe, and the extra height gives no naming advantage at any fixed size
(`SECOND-ORDER-RAYO-II.md` §5). BIG FOOT tried to take a height step by
positing a taller universe without describing it. It is ill-defined
(`phase0/e-foot.md`): at this height a definition can fail to define
anything.

## 3. Why there is no top

The step from each rung to the next is one argument, a form of Berry's
paradox turned into a theorem.

**Setting.** Let `R` be a naming scheme whose language can write a number
`n` in about `6·log₂ n` symbols (`bin(n)` in the Busy Beaver note).

**Claim A (a rulebook cannot name its own record).** There is no constant
`c` and family of formulas `βₙ` of `R`, with `|βₙ| ≤ c + 6·log₂(n+2)`, such
that `βₙ` names `BN_R(n) + 1`.

*Proof.* Choose `n` with `c + 6·log₂(n+2) ≤ n`. Then `βₙ` has size `≤ n` and
names `BN_R(n) + 1`, so `BN_R(n) ≥ BN_R(n) + 1`. ∎ **[Lean,
`size_gt_of_names_succ_record` and `no_short_self_record` in
`rayo-lean/Rayo/NoTop.lean`]**

**Claim B (the next rulebook can).** Let `R⁺` extend `R` (every `R`-formula
is an `R⁺`-formula naming the same number) and suppose `R⁺` can express
"`φ` is an `R`-formula of size `≤ u` naming `k`" by a single formula. Then
"`x` is one more than the largest such `k`, for `u = n`" is a family of
`R⁺`-formulas of size `c + 6·log₂(n+2)`, so

```
BN_R⁺( c + 6·log₂(n+2) )  >  BN_R(n)      for every n,
```

and `BN_R⁺` outgrows `BN_R` by more than an exponential stretch of the
argument. **[Lean, `Extends.record_le`, `record_lt_of_names_succ_record` and
`record_lt_at_log_budget` in `rayo-lean/Rayo/NoTop.lean`]**

**What the Lean file does and does not cover.** It proves Claims A and B for
an arbitrary naming scheme, together with existence and uniqueness of the
record `BN_R(n)` when the formulas of each size form a finite list, using
Lean core only. It includes a toy pair of schemes meeting every hypothesis
of Claim B, so the hypotheses are not vacuous. It does not itself show that any
particular rung supplies the short formulas "one more than the record below".
One instance is checked separately: `sigma2_record_gt_sigma1` in
`rayo-lean-boolos/RayoBoolos/TruthNaming.lean` shows that a `Σ₂` formula of
size `C + 6·log₂(h n)` names a number above everything `Σ₁` truth naming
reaches with `n` symbols (`MIDDLE-RUNGS.md` §8). The other instances, in
particular those involving a truth predicate, are argued on paper in §2 and
`MIDDLE-RUNGS.md`.

Together: the relation "names" for `R` is never expressible in `R` in a way
that `R` itself counts as naming, and adding it always gives a strictly
faster scheme. Since Claim A applies to *every* scheme, including `R⁺`, the
process does not end.

Two ways the expressibility in Claim A fails, both visible in this project:

- **Truth-based rungs.** The naming relation is not definable in the
  language at all. This is Tarski's theorem.
- **The provability rung.** The naming relation *is* definable (it only says
  a proof exists), and the formula "one more than the largest provably named
  number" can be written down, in few symbols. What fails is that the theory
  cannot *prove* which number that formula picks out, so it does not count
  as a name. This is Boolos's 1989 proof of Gödel's incompleteness theorem.

## 4. What this does to the project's original question

The project asked whether growth scales with the cost `κ(R)` of stating the
rulebook, and found no clean law (`KAPPA-TABLE.md`, Phase 4). The ladder
explains why, and says what to measure instead.

- **Within rung 0**, bits do buy growth: a longer rulebook reaches a higher
  ordinal.
- **Crossing to rung 1** costs a few hundred bits, once (a universal
  machine), and every further bit spent at this rung buys nothing.
- **Every later rung** costs a constant number of extra symbols: one new
  predicate and the clauses saying how it behaves. Measured in bits, the
  whole infinite ladder above rung 1 is nearly flat.

So description length is the wrong currency above rung 0. What rises
steadily up the ladder is the strength of the assumptions needed to believe
the rulebook defines anything: nothing beyond arithmetic at rung 1, a
completed set of whole numbers at rung ω, and a completed universe of sets
with its own truth at Rayo's rung. **A meaningful version of the `κ`
question would price that**, for instance by the weakest standard theory
that proves the scheme well defined. **Tested 2026-11-24 in
`ASSUMPTION-COST-SCALE.md`: as a single scale it fails, inverted at the
rung 0 / rung 1 boundary (TREE costs more than arithmetic-truth naming).
What works is two coordinates read in order: how much truth the scheme
consults, then the termination ordinal.**

## 4a. Each rung's Omega: how far it reaches, and how well it compresses

`OMEGA-FOR-NAMING.md` (2026-11-24) adds a second measurement to the ladder.
For a rulebook, pick a formula at random by flipping coins for its symbols.
Let `Ω_R` be the probability that the formula names a number. That one real
number holds all of the rulebook's naming facts.

- **The height of `Ω_R` is the height of the rung.** For a consistent
  listable theory (rung 1), `Ω_T` is exactly as hard as the halting problem.
  For the `Π_k` truth rungs it is exactly as hard as the `(k+1)`-th jump. For
  arithmetic truth it is exactly as hard as arithmetic truth. So the ladder
  can be read off the Omegas. **[paper; the halting reduction at rung 1 is in
  Lean, `RayoBoolos/OmegaHalting.lean`]**
- **How well `Ω_R` compresses is set by the notation, not the theory.** The
  first `n` digits of `Ω_R` can be squeezed into `γ*·n` bits, where `γ*` is
  the information rate of the coin process. For fair coins over the project's
  16-symbol formula alphabet, `γ* ≈ 0.70`. If the coins only ever choose
  among grammatical symbols, `γ* ≈ 0.99`. The same bound holds for PA, ZFC,
  or any consistent theory. **[paper + numeric]**
- **No formula notation reaches Chaitin's `Ω`.** Under any context-free
  notation with fixed symbol probabilities, `Ω_R` is never Martin-Löf
  random. Even the weighting that wastes no coin flips leaves a saving of
  about half of `log₂ n` bits, and the Miller–Yu theorem says that is
  already too much for a random sequence. **[paper]**

The reason is the difference between programs and formulas. A program is
read from an endless tape and the machine decides when to stop, so a random
halting program's length has no well-behaved average. A formula's end is
fixed by its grammar, so its length does have one, and that leaks
information. This is why formulas match programs on *reach* (rung 1 for
both) but always carry a little overhead as *compressors*. The `6·log₂ n` and
`n log n` factors in the Busy Beaver sandwich are overheads of the same
kind: costs of writing program information into formulas.

## 5. Summary table

| rung | "names" means | examples | outgrows | must accept as definite | its Omega (§4a) is as hard as |
|---|---|---|---|---|---|
| 0 | evaluates by a terminating rule | digits, towers, BMS, System F | (sub-rungs by ordinal) | nothing beyond calculation | computable, when naming is decidable [expected] |
| 1 | program halts / theory proves | Busy Beaver, BLC, `BoolosBig_T` for any `T` | every computable function | whether each program halts | the halting problem, `0′` [paper; reduction in Lean] |
| k | halts, with a box for rung k−1 / true `Π_{k−1}` or `Σ_k` formula | oracle Busy Beavers, bounded-truth naming | rung k−1 | arithmetic statements with k−1 "for all" blocks | the matching jump [paper, sketch] |
| ω | true statement of arithmetic | arithmetic-truth naming | every finite rung | all statements about whole numbers | arithmetic truth, `0^(ω)` [paper] |
| Π¹₁ | true statement with one block of set quantifiers (`Π¹₁` or `Σ¹₁`) | Busy Beaver over hyperarithmetic oracles | rung ω, every hyperarithmetic Busy Beaver | that computable trees are well-founded or not | not worked out |
| Σ¹₂, Π¹₂, Σ¹₃, … | true statements of second-order arithmetic, by set-quantifier blocks | `BB` with oracle `O`, ITTM Busy Beaver (both between Π¹₁ and Σ¹₂) | the rung before | from Σ¹₃ on, a single intended collection of all sets of numbers | not worked out |
| … | truth for higher-order languages | third-order arithmetic and up | everything below | sets of sets of numbers, … | not worked out |
| Rayo | true statement of set theory | Rayo's function | everything below | all statements about the universe of sets | not worked out |
| Rayo + parameters | set theory with a symbol for one set or function, fed back in | Fish number 7 | Rayo | nothing beyond Rayo | not worked out |
| Rayo+ stage β (fine ladder) | truth for set theory plus its truth predicate, iterated `β` times; equivalently second-order with only classes definable after `β` rounds | second-order Rayo with definable classes (= stage 1) | every parameter extension below it | nothing beyond Rayo [paper] | not worked out |
| second-order Rayo (height `Ord + 1`) | true statement about sets and all collections of sets | | every Rayo+ stage, even along all the ordinals | which collections of sets exist | not worked out |
| `k`-th order, taller universes | higher orders = more powerset levels; Rayo in a taller universe that describes ours | third-order Rayo | the level below | more height; no last step | not worked out |

## 5a. Where the famous numbers sit

Added 2026-11-24. Placements are from the literature unless marked. The
question of whether each of these numbers is well defined at all, and
what it takes to prove so, is a different one; it is audited number by
number in [`LADDER.md`](LADDER.md). The two documents are meant to
be read together: this one says how fast each scheme grows, that one says
what must be assumed for the number to exist.

**Inside rung 0: the fast-growing hierarchy.** Everything computable sits
on rung 0. Within it, growth is measured by the fast-growing hierarchy
`f_α`, indexed by ordinals. This is a ruler inside the bottom rung, not a
set of further rungs: Busy Beaver beats every level of it.

| level `α` | what grows about this fast | famous numbers | status |
|---|---|---|---|
| 0, 1 | adding one, doubling | | [classical] |
| 2 | exponentials | googol, googolplex | [classical] |
| 3 | power towers | | [classical] |
| ω | Ackermann's function, Knuth's up-arrows | | [classical] |
| ω + 1 | iterating the up-arrow construction | Graham's number, about `f_{ω+1}(64)` | [classical] |
| ω² | Conway's chained arrows | | [classical] |
| ε₀ | Goodstein sequences, the Kirby and Paris hydra; also the limit of what PA proves total | Goodstein numbers | [classical] |
| Γ₀ | the limit of predicative mathematics | | [classical] |
| small Veblen ordinal, at least | Kruskal's tree sequences | TREE(3) | theorem [classical]; the level is a lower bound |
| about ψ(Ω_ω) | subcubic graph sequences; two-row Bashicu matrices | SCG(13) | theorem [classical]; the level is a lower bound |
| ψ(ε_{Ω_ω+1}) | Buchholz hydras | | [classical] |
| above the measured levels | the Bashicu matrix system; programs in the calculus of constructions. Both are on the ruler, above everything listed, at a level nobody has pinned down, and which of the two is higher is not settled | Bashicu matrix numbers; Loader's number | Loader's number is computable for certain; termination of Bashicu matrices rests on one unrefereed proof |
| off the scale | Busy Beaver: this is rung 1 | `BB(n)` | [classical] |

**On the upper rungs.**

| rung | famous residents | status |
|---|---|---|
| 1, Busy Beaver | `BB(n)`, Radó's `Σ(n)`, binary lambda calculus; the largest number provably nameable in `n` symbols, for any reasonable theory | [classical]; provable naming [Lean] |
| k, higher Busy Beavers | `BB₂`, `BB₃`, … (halting oracles) | [classical]; the match with "for all" blocks is [paper] (`MIDDLE-RUNGS.md`) |
| ω, arithmetic truth | Goucher's Ξ function sits near here | not audited by this project |
| second-order arithmetic | Busy Beaver with oracle Kleene's `O`, and Busy Beaver for infinite-time Turing machines: both strictly between the `Π¹₁` and `Σ¹₂` rungs | [paper] (`SECOND-ORDER-RUNGS.md` Thm 4, Prop 6) |
| Rayo | Rayo's number | well defined only given a strong extra assumption (`RAYO-R0-WELLDEFINEDNESS.md`) |
| above Rayo | Fish number 7: strictly between Rayo and the first Rayo+ step, since its oracles are only parameters. The Arias function (2026 preprint, abstract only) iterates second-order Rayo, so it should sit just above that. BIG FOOT aimed higher, but its definition does not determine a number | community constructions; placements [paper] (`ABOVE-RAYO.md` §2), Arias [expected] |

## 6. What would make this solid

In rough order of value for effort:

1. ~~Machine-check Theorem 1 of the Busy Beaver note.~~ **Done,
   2026-11-24**, in its domination form, with non-computability:
   `rayo-lean-boolos/RayoBoolos/Minimization.lean`, and the logarithmic
   bound in `RayoBoolos/Binary.lean`. Also done, 2026-11-24: the Busy Beaver lower
   bound and the theory-independent lower bound (`RayoBoolos/BusyBeaver.lean`,
   `RayoBoolos/AnyTheory.lean`). The upper bound is done too, in a non-quantitative
   form (`RayoBoolos/UpperBound.lean`), and with the explicit `n log n`
   rescaling (`RayoBoolos/CompactCode.lean`, 2026-11-24), including the
   full sandwich against Busy Beaver of Mathlib program code numbers,
   `Big_T(n) ≤ BB(2^(C·(n+1)·(log₂(n+1)+6)))` (`RayoBoolos/HardWire.lean`).
   Also in Lean: a
   theory proves no exact value, and no upper bound, of its own naming
   function (`RayoBoolos/NoExactValue.lean`).
2. ~~Machine-check Claims A and B of §3 in the abstract setting.~~ **Done,
   2026-11-24:** `rayo-lean/Rayo/NoTop.lean`, sorry-free, Lean core only.
   The natural follow-up is one concrete instance: exhibit a real pair of
   languages (for example bare arithmetic and arithmetic with a halting
   predicate) and prove the short "one more than the record" formulas exist.
3. ~~Write out the rung-k sandwich (oracle Busy Beaver against bounded-truth
   naming) on paper.~~ **Done, 2026-11-24:** `MIDDLE-RUNGS.md`, with the
   bottom two levels and one concrete instance of Claim B (`Σ₁` against `Σ₂`
   truth naming) in Lean, `RayoBoolos/TruthNaming.lean`.
4. Check the tagged **[classical]** and **[expected]** statements against
   sources, and look for prior statements of the "provable naming is Busy
   Beaver class for every theory" result. **First pass done, 2026-11-24:** `LITERATURE-SURVEY.md`.
5. ~~Try the §4 proposal.~~ **Done, 2026-11-24:** `ASSUMPTION-COST-SCALE.md`
   (negative for a single scale; a two-coordinate law survives).
6. ~~Work out the first rungs above arithmetic truth.~~ **Done on paper,
   2026-11-24:** `SECOND-ORDER-RUNGS.md` (second-order rungs, `BB^O` and ITTM
   placement). Not yet re-read; no Lean.

7. ~~Ask whether a rung's naming probability behaves like Chaitin's `Ω`.~~
   **Done, 2026-11-24:** `OMEGA-FOR-NAMING.md` (§4a above). It is as hard as
   the rung but never Martin-Löf random under a context-free notation. The
   halting reduction is in Lean (`RayoBoolos/OmegaHalting.lean`). Open: the
   exact compression rate, between `0.149` and `0.70` for fair coins.

8. ~~Work out what lies above Rayo.~~ **Done on paper, 2026-11-25:**
   `SECOND-ORDER-RAYO.md`, `SECOND-ORDER-RAYO-II.md`, `ABOVE-RAYO.md`
   (parameter, truth and height steps; Fish number 7 placed below the first
   Rayo+ step). Open: exact indexing of the fine ladder; the Arias function.

See also `COMPLEXITY-AND-ENTROPY.md` (2026-11-24), which reads the same
ladder as a hierarchy of description-complexity measures and connects it to
Kolmogorov complexity, Chaitin's theorem, Shannon entropy and complexity
classes.
