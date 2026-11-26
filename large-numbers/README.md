# Large numbers: what does it cost to name one?

I've been interested in big numbers for a long time. The immediate spark for
this project was two CodeParade videos on the game of "biggest number you
can write in a fixed message length": digits, power towers, Graham's number,
Binary Lambda Calculus, the Bashicu Matrix System, Loader's number, and at
the top of the ladder, Rayo's function. What the videos sparked wasn't the
interest itself but a specific curiosity: how do you specify a big number
*rigorously*, in the smallest amount of space? The bigger numbers in the
game aren't written in digits, they're written in ever more powerful
*notation systems*, and the notation system itself has to be specified
somewhere. So what does that specification cost, and does paying more for it
reliably buy faster growth?

Made precise: fix a rulebook R (a grammar plus a meaning for "this formula
names that number") and a symbol budget n. How big a number can you name,
and what does the rulebook itself cost? The formal setup is in
[`BN-function.md`](BN-function.md).

---

## Where it ended up

**For any fixed rulebook there is a largest number nameable in n symbols.
No rulebook is final.** How fast that largest number grows is decided
almost entirely by one thing: how much *truth* the rulebook takes as given.
Spending more symbols on the rulebook, or choosing stronger axioms, buys
very little by comparison.

In more detail:

1. **Provable naming is Busy Beaver class, for any reasonable theory.**
   Say a formula names `k` in a theory T when T proves "this formula holds
   of `k` and nothing else" (Boolos's notion, 1989). The largest number T
   names in `n` symbols eventually beats every computable function, is not
   computable, and is squeezed between two Busy Beaver functions, the upper
   one after rescaling `n` by about `n log n`. This holds for every
   consistent, computably axiomatized theory containing a weak base theory
   with no induction. So PA, much weaker fragments, and ZFC all give the
   same growth class: changing the axioms only rescales `n`, by at most a
   constant times `log n`. A theory also
   cannot prove any exact value of its own function. **Machine-checked**
   ([`PROVABLE-NAMING-REPORT.md`](PROVABLE-NAMING-REPORT.md) Theorems 1, 2,
   3, 5, 6 and 8, Corollary 7).
2. **Above that, the rungs are notions of truth.** Naming by the *truth* of
   arithmetic formulas with `k` blocks of "for all" matches the Busy Beaver
   function for machines with `k` levels of halting oracle. This proves a
   2010 guess of Aaronson. **Paper proof** for every `k`
   ([`MIDDLE-RUNGS.md`](MIDDLE-RUNGS.md)); the first two levels are
   **machine-checked**. A general form for any consistent theory, computably
   axiomatized or not, is also on paper
   ([`GENERAL-NAMING-THEOREM.md`](GENERAL-NAMING-THEOREM.md)).
3. **The ladder.** Arithmetic truth, then second-order arithmetic, then
   Rayo's function (truth for set theory), then three kinds of step above
   Rayo: parameters, iterated truth, and a taller universe. Every famous big
   number is placed on it ([`THE-LADDER.md`](THE-LADDER.md)). The rungs
   above arithmetic truth are **paper** arguments.
4. **No top.** Adding the truth predicate of the current rulebook always
   gives a strictly faster one, for a few more symbols. This is Berry's
   paradox and Tarski's theorem in a new setting; an abstract form is
   **machine-checked** (report Theorem 9, `rayo-lean/Rayo/NoTop.lean`).
5. **Rayo's number needs an assumption the usual description leaves out:**
   a truth predicate for the whole universe of sets, of roughly
   Morse–Kelley strength
   ([`RAYO-R0-WELLDEFINEDNESS.md`](RAYO-R0-WELLDEFINEDNESS.md); the
   googology community's technical literature reached the same verdict
   first, see [`LADDER.md`](LADDER.md) rung 9).

**What is and is not claimed.** The notion of naming is Boolos's, and the
results above are classical in substance or, as far as the literature
survey found, unstated folklore that specialists probably know
([`LITERATURE-SURVEY.md`](LITERATURE-SURVEY.md)). Report Theorems 1 to 9
are **not** claimed as new theorems. What this project adds is the Lean
mechanization (we know of no earlier formalization of a Boolos-style naming
function or its growth), the correction below, a written proof of
Aaronson's guess (report Theorem 10), and a general statement we did not
find elsewhere (Theorem 11). The fact that the same pattern repeats from
rung to rung is classical (Aaronson, "The Busy Beaver Frontier", 2020, §3,
resting on Post and Kleene) and is not claimed. **None of the paper proofs
has had an outside reader.**

### A correction worth keeping visible

Until 2026-11-24 this project described the provability function over PA
as reaching only the ε₀ level of the fast-growing hierarchy, the level of
the functions PA can prove total. That was wrong. ε₀ was a lower bound we
had proved, read as if it were the size of the function. Naming asks the
theory to confirm *one value at a time*, and for that a finished
computation is enough; no proof that the function always halts is needed.
So the function is Busy Beaver class. The earlier notes keep dated
correction notes rather than silent edits: `KAPPA-TABLE.md`,
`RAYO-GROWTH-RATE.md`, `BOOLOS-B0-WELLDEFINEDNESS.md` §6, and `LADDER.md`.

### How the labels work

Every results note tags its claims:

- **[Lean]**: machine-checked in Lean 4 against Mathlib and
  FormalizedFormalLogic/Foundation, no `sorry`, no axioms beyond
  `propext`, `Classical.choice`, `Quot.sound`;
- **[paper]**: argued in the note, not machine-checked, and not yet read
  by anyone outside this project;
- **[classical]**: standard mathematics cited from the literature, not
  re-derived;
- **[expected]**: believed and plausibly standard, but neither proved here
  nor checked against a source.

Report §9 lists each machine-checked statement beside its Lean name and
says where the formal statement is narrower than the prose.

---

## Reading order

1. [`BIG-NUMBERS-AS-COMPRESSION.md`](BIG-NUMBERS-AS-COMPRESSION.md): a
   plain-language essay on the whole subject. Start here if you want the
   ideas without the proofs.
2. [`THE-LADDER.md`](THE-LADDER.md): every rung, what it asks you to
   accept, and where the famous numbers sit.
3. [`PROVABLE-NAMING-REPORT.md`](PROVABLE-NAMING-REPORT.md): the main
   results with proofs, the table of Lean statements, related work.
4. [`LADDER.md`](LADDER.md): the companion audit. It asks a different
   question of sixteen famous numbers: what must be assumed for each to
   exist at all? (It uses "rung" for one number; `THE-LADDER.md` uses it
   for one meaning of "names".)
5. [`FUTURE-WORK.md`](FUTURE-WORK.md): everything not yet done, in one
   place.

Then, by topic:

- **First-order story:**
  [`BOOLOS-IS-BUSY-BEAVER-CLASS.md`](BOOLOS-IS-BUSY-BEAVER-CLASS.md),
  [`MIDDLE-RUNGS.md`](MIDDLE-RUNGS.md),
  [`GENERAL-NAMING-THEOREM.md`](GENERAL-NAMING-THEOREM.md),
  [`COMPLEXITY-AND-ENTROPY.md`](COMPLEXITY-AND-ENTROPY.md) (the results read
  as description complexity),
  [`OMEGA-FOR-NAMING.md`](OMEGA-FOR-NAMING.md) (a Chaitin Ω for each rung).
- **Above arithmetic truth and above Rayo** (all paper):
  [`SECOND-ORDER-RUNGS.md`](SECOND-ORDER-RUNGS.md),
  [`SECOND-ORDER-RAYO.md`](SECOND-ORDER-RAYO.md),
  [`SECOND-ORDER-RAYO-II.md`](SECOND-ORDER-RAYO-II.md),
  [`ABOVE-RAYO.md`](ABOVE-RAYO.md),
  [`ORDINAL-RAYO.md`](ORDINAL-RAYO.md),
  [`LARGE-CARDINALS-AND-THE-LADDER.md`](LARGE-CARDINALS-AND-THE-LADDER.md),
  [`ASSUMPTION-COST-SCALE.md`](ASSUMPTION-COST-SCALE.md) (whether one cost
  scale orders the whole ladder: it does not).
- **Bounded resources** (proof-length budgets and complexity classes):
  [`PROOF-BUDGETS-AND-COMPLEXITY.md`](PROOF-BUDGETS-AND-COMPLEXITY.md),
  [`P-VS-NP-LIMITS.md`](P-VS-NP-LIMITS.md),
  [`POLYLOG-NAMING-LADDER.md`](POLYLOG-NAMING-LADDER.md),
  [`CALCNAME2-HARDNESS.md`](CALCNAME2-HARDNESS.md),
  [`NAMING-DEPTH.md`](NAMING-DEPTH.md),
  [`NAMING-RECORDS-SMALL-SYSTEM.md`](NAMING-RECORDS-SMALL-SYSTEM.md),
  [`VP-VNP-CLAIM.md`](VP-VNP-CLAIM.md) (an assessment of a claimed result,
  not a result of this project).

---

## How the project got there

The notes below are the earlier stages, kept as they were written, with
dated corrections where later work overturned them.

### Part 1: measuring six real systems, no clean law

The first run ([`PLAN.md`](PLAN.md) → [`METHODOLOGY.md`](METHODOLOGY.md) →
[`KAPPA-TABLE.md`](KAPPA-TABLE.md)) priced the rulebook, κ(R), in Binary
Lambda Calculus bits for six systems: Turing machines, BLC itself, single-
and multi-row BMS, System F/CoC, and first-order set theory (Rayo's family).
The question was whether growth rate scales predictably with that price.

It doesn't. Turing-complete systems (Busy Beaver, BLC) hit uncomputable
growth within a few hundred bits, and past that point paying more κ buys
nothing faster. Only the sub-Turing ordinal ladder (single-row BMS <
multi-row BMS < System F/CoC) shows a gradient, and even that may just be
the sequence googology happened to formalize. The later results explain
why: within one rung, changing the rulebook shifts the budget by a
constant, and a step up costs about `log n` symbols. Bits are the wrong
currency; what a faster function costs is what it assumes.

One side finding: the wiki claim that BIG FOOT "beats Rayo's number" is
its definer's assertion with no proof, and a community refutation shows
its underlying theory is inconsistent, so BIG FOOT is ill-defined. (The
refutation was read through search extracts and not re-derived here; see
`LADDER.md` rung 10.)

### Part 2: naming small numbers in bare set theory

Lean proofs ([`rayo-lean/Rayo/K0.lean`](rayo-lean/Rayo/K0.lean) to
[`K6.lean`](rayo-lean/Rayo/K6.lean); walkthrough in
[`RAYO-EXPLAINER.md`](RAYO-EXPLAINER.md)) of how many symbols first-order
set theory, with only membership and logic, needs to name 0 to 6 by
enumerating every predecessor: **10, 30, 128, 403, 1228, 3703, 11128**,
about 3× per step. That is the cost of one bad strategy, not the minimum:
a successor chain names 6 in **388 symbols**
([`K6Chain.lean`](rayo-lean/Rayo/K6Chain.lean)), and letting formulas
reuse each other cuts it further ([`Reuse.lean`](rayo-lean/Rayo/Reuse.lean)).
One correction from this stage: `K2.lean` to `K6.lean` and `K6Chain.lean`
do use `Classical.choice`, contrary to an earlier statement;
`RAYO-EXPLAINER.md` gives the lines.

### Part 3: building numbers up is the wrong strategy

No build-it-up strategy gets anywhere near Rayo's number. Rayo's
construction instead uses self-reference: a formula about *other formulas*
("the smallest number no shorter formula names"). Evaluating that needs a
truth predicate for set theory, which by Tarski set theory cannot supply
for itself ([`DIAGONALIZATION-PLAN.md`](DIAGONALIZATION-PLAN.md),
[`DIAGONALIZATION-STAGE0-FINDINGS.md`](DIAGONALIZATION-STAGE0-FINDINGS.md)).

### Part 4: two ways to make self-reference rigorous

Both run the same naming machine on different fuel.

- **Provability (the Boolos fork).** Replace "true" by "provable in PA",
  which the theory can express about itself. Well-definedness, B0
  ([`BOOLOS-B0-WELLDEFINEDNESS.md`](BOOLOS-B0-WELLDEFINEDNESS.md)), needs
  only that PA is consistent, plus one subtlety: formulas must be counted up
  to renaming of variables, or there are infinitely many of each size
  (`METHODOLOGY.md` C8). The first growth result, `BoolosBig_PA_dominates`
  for PA-provably-total functions
  ([`BoolosBig.lean`](rayo-lean-boolos/RayoBoolos/BoolosBig.lean);
  [`BOOLOS-B3-PAPER-VERIFICATION.md`](BOOLOS-B3-PAPER-VERIFICATION.md)),
  was then read as an ε₀ ceiling; see the correction above. The full story
  is the report.
- **Truth (the Rayo fork).** Rayo's own route. It names a definite number
  only given a truth predicate for the universe of sets, roughly MK
  strength ([`RAYO-R0-WELLDEFINEDNESS.md`](RAYO-R0-WELLDEFINEDNESS.md)).
  Given that, it eventually beats every function ZFC proves total and
  climbs past every fixed ordinal notation
  ([`RAYO-GROWTH-RATE.md`](RAYO-GROWTH-RATE.md), paper). The domination
  argument is machine-checked *relative to* that commitment, which enters
  as an explicit hypothesis because Tarski forbids constructing it
  ([`RayoBig.lean`](rayo-lean-boolos/RayoBoolos/RayoBig.lean)).

The gap between the two forks turned out to be not one step but a whole
ladder of intermediate notions of truth, which is where the project ended
up (top of this file).

### The Bashicu Matrix System

Bashicu's number is well-defined only by one unrefereed 2023 preprint
(arXiv:2307.04606). A two-pass audit ([`BMS-BM4-AUDIT.md`](BMS-BM4-AUDIT.md))
line-verified its key reflection lemma and found no error; what remains is
listed in the audit and in `FUTURE-WORK.md` §1.

---

## Map

| what | where |
|---|---|
| plain-language essay | [`BIG-NUMBERS-AS-COMPRESSION.md`](BIG-NUMBERS-AS-COMPRESSION.md) |
| the ladder of rungs, famous numbers placed by growth | [`THE-LADDER.md`](THE-LADDER.md) |
| main results with proofs, Lean table | [`PROVABLE-NAMING-REPORT.md`](PROVABLE-NAMING-REPORT.md) |
| famous numbers audited for well-definedness | [`LADDER.md`](LADDER.md) |
| prior art | [`LITERATURE-SURVEY.md`](LITERATURE-SURVEY.md) |
| open items | [`FUTURE-WORK.md`](FUTURE-WORK.md) |
| the formal question, conventions | [`BN-function.md`](BN-function.md), [`METHODOLOGY.md`](METHODOLOGY.md) |
| six-system price comparison | [`KAPPA-TABLE.md`](KAPPA-TABLE.md), [`FINDINGS.md`](FINDINGS.md), [`phase0/`](phase0/) |
| naming 0–6 in bare set theory | [`RAYO-EXPLAINER.md`](RAYO-EXPLAINER.md), [`rayo-lean/Rayo/`](rayo-lean/Rayo/) (`K0`–`K6`, `K6Chain`, `Reuse`, `ReuseSix`, `Encoding`) |
| no top, abstract form | [`rayo-lean/Rayo/NoTop.lean`](rayo-lean/Rayo/NoTop.lean) |
| Boolos fork, early notes | [`BOOLOS-FUNCTION-PLAN.md`](BOOLOS-FUNCTION-PLAN.md), [`BOOLOS-B0-WELLDEFINEDNESS.md`](BOOLOS-B0-WELLDEFINEDNESS.md), [`BOOLOS-B3-PAPER-VERIFICATION.md`](BOOLOS-B3-PAPER-VERIFICATION.md), [`BOOLOS-B1-B3-REPORT.md`](rayo-lean-boolos/BOOLOS-B1-B3-REPORT.md) |
| provable-naming Lean (Busy Beaver sandwich, any theory, no provable values, truth naming) | [`rayo-lean-boolos/RayoBoolos/`](rayo-lean-boolos/RayoBoolos/); report §9 maps each theorem to its file |
| Rayo fork | [`RAYO-RIGOR-PLAN.md`](RAYO-RIGOR-PLAN.md), [`RAYO-R0-WELLDEFINEDNESS.md`](RAYO-R0-WELLDEFINEDNESS.md), [`RAYO-GROWTH-RATE.md`](RAYO-GROWTH-RATE.md), [`RayoBig.lean`](rayo-lean-boolos/RayoBoolos/RayoBig.lean) |
| Bashicu matrices | [`BMS-BM4-AUDIT.md`](BMS-BM4-AUDIT.md) |
| older hand-off notes | [`LAPTOP-HANDOFF.md`](LAPTOP-HANDOFF.md) |
| dated narrative | [`../DEVLOG.md`](../DEVLOG.md) |

## Checking the Lean

Toolchain Lean 4 `v4.32.2`; Mathlib and Foundation are pinned by each
project's `lake-manifest.json`. Run `lake build` in
`rayo-lean-boolos/` and in `rayo-lean/`. Each file ends with
`#print axioms` for its headline theorems.
