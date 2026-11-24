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
formula is a statement of arithmetic with at most `k` alternations of "there
exists" and "for all", and it is *true* of the number and nothing else.

The Busy Beaver function of rung `k` eventually dominates every function
computable with the rung `k − 1` box, in particular the rung `k − 1` Busy
Beaver function, by the same argument as at rung 1. **[classical: relativized
Busy Beaver and the arithmetical hierarchy]** The match between "oracle
level `k`" and "`k` quantifier alternations, by truth" is Post's theorem
**[classical]**; that the two resulting naming functions bound each other up
to argument rescaling is **[expected]** and would be proved like Theorems 2
and 3 of the Busy Beaver note.

Rung 1 fits the same description: a provable existential statement and a
true existential statement are the same thing for a theory that can check
computations, which is why provability lands exactly there.

### Rung ω: all of arithmetic truth

*Names means:* the formula is any statement of first-order arithmetic, and it
is true of the number and nothing else.

Dominates every finite rung. **[expected; immediate from the previous rung]**

*What you must accept:* that every statement about the whole numbers,
however many quantifiers it has, is definitely true or false. Equivalently,
that the whole numbers form a completed totality.

*The wall:* arithmetic cannot define its own truth (Tarski). **[classical]**

### Beyond: truth for richer and richer languages

The same step continues: truth for arithmetic with a truth predicate, and
iterations of that; truth for statements about sets of whole numbers; about
sets of those; and so on up. **[classical in outline; details and the exact
ordering of these rungs are not worked out here]**

### The Rayo rung: truth for set theory

*Names means:* the formula is a statement of first-order set theory, true of
the number and nothing else.

Every rung below is describable by one formula of set theory, so Rayo's
function eventually dominates all of them. **[paper,
`RAYO-GROWTH-RATE.md`, for provably total functions and ordinal notations;
[expected] for the oracle rungs, by the same argument]**

*What you must accept:* that every statement about the entire universe of
sets is definitely true or false. Making this precise needs roughly
Morse-Kelley strength. **[paper, `RAYO-R0-WELLDEFINEDNESS.md`]**

### Above Rayo

Add a symbol for "true formula of set theory" and take formulas of the
enlarged language; repeat. Fish number 7 is a version of this. BIG FOOT was
a more ambitious attempt and is ill-defined (`phase0/e-foot.md`), a reminder
that at this height a definition can fail to define anything.

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
of Claim B, so the hypotheses are not vacuous. It does **not** show that any
particular rung supplies the short formulas "one more than the record below":
that a truth predicate or an oracle really lets you write that formula in
`c + 6·log₂(n+2)` symbols is a fact about the specific language, argued on
paper in §2. The abstract step is checked; each instance of it is not.

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
that proves the scheme well defined. **[proposal, not carried out]**

## 5. Summary table

| rung | "names" means | examples | outgrows | must accept as definite |
|---|---|---|---|---|
| 0 | evaluates by a terminating rule | digits, towers, BMS, System F | (sub-rungs by ordinal) | nothing beyond calculation |
| 1 | program halts / theory proves | Busy Beaver, BLC, `BoolosBig_T` for any `T` | every computable function | whether each program halts |
| k | halts, with a box for rung k−1 | oracle Busy Beavers | rung k−1 | arithmetic statements with k quantifier alternations |
| ω | true statement of arithmetic | arithmetic-truth naming | every finite rung | all statements about whole numbers |
| … | truth for richer languages | higher-order arithmetic | everything below | sets of numbers, sets of those, … |
| Rayo | true statement of set theory | Rayo's function | everything below | all statements about the universe of sets |
| Rayo+ | truth for set theory plus its truth predicate, iterated | Fish number 7 | Rayo | more again; no last step |

## 6. What would make this solid

In rough order of value for effort:

1. ~~Machine-check Theorem 1 of the Busy Beaver note.~~ **Done,
   2026-11-24**, in its domination form, with non-computability:
   `rayo-lean-boolos/RayoBoolos/Minimization.lean`, and the logarithmic
   bound in `RayoBoolos/Binary.lean`. Also done, 2026-11-24: the Busy Beaver lower
   bound and the theory-independent lower bound (`RayoBoolos/BusyBeaver.lean`,
   `RayoBoolos/AnyTheory.lean`). The upper bound is done too, in a non-quantitative
   form (`RayoBoolos/UpperBound.lean`). Remaining there: the explicit
   `n log n` rescaling.
2. ~~Machine-check Claims A and B of §3 in the abstract setting.~~ **Done,
   2026-11-24:** `rayo-lean/Rayo/NoTop.lean`, sorry-free, Lean core only.
   The natural follow-up is one concrete instance: exhibit a real pair of
   languages (for example bare arithmetic and arithmetic with a halting
   predicate) and prove the short "one more than the record" formulas exist.
3. Write out the rung-k sandwich (oracle Busy Beaver against bounded-truth
   naming) on paper.
4. Check the tagged **[classical]** and **[expected]** statements against
   sources, and look for prior statements of the "provable naming is Busy
   Beaver class for every theory" result. **First pass done, 2026-11-24:** `LITERATURE-SURVEY.md`.
5. Try the §4 proposal: redo the table with "weakest theory proving the
   scheme well defined" in place of bits.

See also `COMPLEXITY-AND-ENTROPY.md` (2026-11-24), which reads the same
ladder as a hierarchy of description-complexity measures and connects it to
Kolmogorov complexity, Chaitin's theorem, Shannon entropy and complexity
classes.
