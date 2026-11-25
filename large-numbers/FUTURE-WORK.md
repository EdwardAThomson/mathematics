# Future work

*Compiled 2026-11-25 from the open-item sections of every note in this
directory. Each entry points to the note that states it precisely. Nothing
here is new mathematics; it is an index of what is not yet done.*

The entries are grouped by kind of work, and within each group the most
valuable come first. "Valuable" is a judgement: it means the item would
most change how much the project's claims can be trusted, or how far they
reach.

## 1. Raising confidence in what is already written

These need no new ideas. They are the difference between "we believe it"
and "it has been checked".

1. **An outside reader for the paper proofs.** The following have been
   read only by the sessions that wrote them:
   - the middle rungs for every level (`MIDDLE-RUNGS.md`; re-read once,
     three repairs, §7a);
   - the general naming theorem (`GENERAL-NAMING-THEOREM.md`);
   - the rungs above arithmetic truth (`SECOND-ORDER-RUNGS.md`, one pass;
     §9 lists the steps most worth a second read);
   - the assumption-cost note (`ASSUMPTION-COST-SCALE.md`, one pass, with
     two sketches tagged expected);
   - the notes above Rayo (`SECOND-ORDER-RAYO.md`,
     `SECOND-ORDER-RAYO-II.md`, `ABOVE-RAYO.md`).

   The natural public test for the first is to post it as an answer to
   Aaronson's MathOverflow question 34710, where the guess it proves was
   made.
2. **Proof-budget bookkeeping.** `PROOF-BUDGETS-AND-COMPLEXITY.md` rests
   on a cited lemma about polynomial-size proofs of correct runs, and
   `NAMING-DEPTH.md` on an unwritten standard assumption about proof
   checkers; both notes say exactly where.
3. **Bashicu matrices.** The termination proof (arXiv:2307.04606) is
   still unrefereed. `BMS-BM4-AUDIT.md`: Lemma 2.6, the
   unbounded-array case, and a proof that no reachable array has a zero
   above a nonzero in its last column.

## 2. Machine-checking

The headline result (the Busy Beaver sandwich, independence of the
axioms, no provable upper bound) is fully in Lean. What is not:

1. **Oracle machines tied to the arithmetical hierarchy.** This is the
   one missing piece of infrastructure. With it, the middle rungs
   (`MIDDLE-RUNGS.md` Theorems 1 to 3), the lower bound of the general
   theorem (`GENERAL-NAMING-THEOREM.md` Theorem 2) and the first-order
   case of `SECOND-ORDER-RUNGS.md` Theorem 1 all become realistic
   targets. Mathlib has `RecursiveIn` but no oracle Busy Beaver and no
   link to formula classes.
2. **Sharp level-one statements.** That bounded formulas alone reach Busy
   Beaver, and that one "for all" block already exceeds it. Needs a
   bounded formula for a complete computation record
   (`MIDDLE-RUNGS.md` §8).
3. **Sharper constants.** The `6` in the logarithmic bound comes from the
   encoding of binary numerals and is not optimal
   (`PROVABLE-NAMING-REPORT.md` §12).
4. **The assumption-cost sketches** as Lean statements over the library's
   induction fragments (`ASSUMPTION-COST-SCALE.md` §7, item 1).

## 3. Open mathematics

### 3.1 The ladder itself

- **Is there one measure combining the two costs?** A scheme's growth is
  ordered first by how much truth it consults and then by its termination
  ordinal. Whether one natural quantity captures both is open
  (`ASSUMPTION-COST-SCALE.md`). Related, same note §7: can rungs of
  incomparable Turing degree have comparable growth?
- **Which theories give a clean rung?** Three questions about the sets a
  theory decides (`GENERAL-NAMING-THEOREM.md` §11).
- **A single oracle for the first second-order rung**, and whether that
  rung's naming function computes Kleene's `O`
  (`SECOND-ORDER-RUNGS.md` §5).
- **Limit stages.** The repetition of the pattern from rung to rung is
  classical (`LITERATURE-SURVEY.md` §9). What may have content is what
  "n symbols" should mean at limit stages, where the answer depends on
  the ordinal notation.

### 3.2 Above Rayo

- The exact indexing of the fine ladder between heights, including
  limits; removing the `V = L` assumption; where the minimal models of
  the standard class theories sit (`ABOVE-RAYO.md` §7).
- Whether Fish number 7's hierarchy reaches the first truth step from
  below, and the remaining items of `SECOND-ORDER-RAYO-II.md` §8.
- Whether Rayo's function, or the third-level second-order naming
  function, actually takes different values in different universes, and
  the determinacy analogue of the one-jump overshoot
  (`LARGE-CARDINALS-AND-THE-LADDER.md` §5).
- Naming infinite numbers: where the least unnamed ordinal sits
  (`ORDINAL-RAYO.md` §7).

### 3.3 Bounded resources and complexity

- **Is short naming hard?** Deciding whether a number has a short name
  with a short proof is in NP; whether it is NP-hard is open and behaves
  like the minimum circuit size problem (`P-VS-NP-LIMITS.md` §4).
- **Calculation names.** Is the small-budget calculation-naming problem
  in P or hard for its class? A barrier is proved; the question is open
  (`POLYLOG-NAMING-LADDER.md` §4.2, `CALCNAME2-HARDNESS.md` §4).
- **Naming depth.** Whether the loss terms in the slow-growth law are
  necessary, and whether the records `Big_T(n)` are deep relative to
  their length (`NAMING-DEPTH.md`, closing list of open questions).
- **Naming probability.** The exact compression rate of the naming
  analogue of Chaitin's `Ω`, known only to lie between two bounds
  (`OMEGA-FOR-NAMING.md`).
- **Small systems.** The computed record growth matches the exponents of
  the proof-budget note; this is an observation, not a theorem
  (`NAMING-RECORDS-SMALL-SYSTEM.md`).

## 4. Literature still to check

- Kikuchi, Kurahashi and Sakai (2012) in full; a library copy would
  settle whether they state a growth rate (`LITERATURE-SURVEY.md` §6).
- The Googology Wiki pages on Rayo's number and First Order Oodle
  Theory, which refuse automated access. They are the likeliest place
  for prior statements about iterated truth over set theory.
- The Arias function paper (`ABOVE-RAYO.md` §7, item 3).
- Whether "second-order Rayo" has been defined in googology sources, and
  whether the link between large-cardinal absoluteness and naming
  functions is folklore.

## 5. Presentation

- The report (`PROVABLE-NAMING-REPORT.md`) covers the first-order story.
  The notes on second-order rungs, the region above Rayo, large
  cardinals and bounded resources are cited from it or stand alone. A
  short overview that walks the whole ladder once, pointing into each
  note, would help a new reader.
- The picture of the ladder exists only as a private web page. A static
  figure in the repository would let the report show it.
