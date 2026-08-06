# Methodology: how kappa(R) is measured

This note fixes the operational convention Phase 2 uses to put an actual
number (in bits) on kappa(R) for each reference system R in
`BN-function.md` Section 7. `BN-function.md` (condition A5) defines kappa(R)
only conceptually, as "the length, in some fixed reference meta-language, of
a full specification of Sigma, L's grammar, and the evaluation/proof rules."
It deliberately does not fix that meta-language or say what counts as "a full
specification." This note does, and flags every place where the answer is a
definitional decision rather than a discovered fact. All of Phase 2's and
Phase 4's conclusions are conditional on the choices made here; a different
convention would shift the numbers, so the choices are stated first and their
consequences bounded.

Read `BN-function.md` first. This note does not re-derive BN(R, n), the
admissibility conditions A1-A5, or the conceptual definition of kappa(R); it
only makes A5 operational.

## 1. The chosen reference meta-language: Binary Lambda Calculus (BLC)

**The fixed reference meta-language for measuring kappa(R) is John Tromp's
Binary Lambda Calculus (BLC).** kappa(R) is defined operationally as:

> kappa(R) = the length in bits of a BLC program that implements R's
> machinery, i.e. a BLC term that decodes an expression e in L and applies
> R's evaluation/reduction/proof rules to it (the interpreter for R written
> in BLC), NOT the length of computing any particular BN value.

Four reasons this meta-language is chosen over the other natural candidates
(a minimal universal Turing machine, SKI/combinator calculus, Iota/Jot):

1. **Commensurability with the budget axis.** The n-axis of BN(R, n) is
   already measured in BLC bits for the leaderboard-real systems (Tromp's
   fixed-bit leaderboard, `phase0/c-pole-position.md`). Measuring kappa(R) in
   the same unit, BLC bits, is what makes the sentence "specification cost
   versus reachable growth" a comparison in one currency instead of two. If
   kappa were in TM states and n in BLC bits, the table's two axes would not
   be addable or comparable.

2. **BLC is itself admissible and minimal.** BLC has a 2-symbol alphabet, a
   fixed decidable grammar, and a fixed beta-reduction rule (A1-A3 hold for
   the meta-language itself), so the meta-language does not smuggle in
   unbounded machinery of its own. Its per-symbol overhead is the smallest
   among practical universal encodings, which is exactly why it is the base
   of the existing bignum-bakeoff records.

3. **Concrete existing artifacts to measure against.** Phase 2 does not have
   to invent interpreters. Tromp's BLC self-interpreter / universal term,
   Pat Kale's BLC port of the Bashicu Matrix System, and the Loader's-number
   ports (`loader.c` and eaglgenes101's 569-byte Julia port,
   `phase0/c-pole-position.md`) are real, sized artifacts that anchor the
   kappa estimates in exhibited code rather than folklore. This matches the
   project's standing rule of grounding numbers in leaderboard/proof data.

4. **A known invariance story.** `BN-function.md` Section 6 already develops
   the invariance-up-to-a-constant theorem for BLC-style systems, so the
   sense in which kappa is only defined up to an additive constant (Section 4
   below) is already on record and quantified.

**kappa counts the interpreter, not the computation.** R's denotation
function is partial and, for Turing-complete R, uncomputable in the halting
sense. We never charge for running e to a value (that can fail to halt).
kappa charges only for the *finite* program that steps/reduces/checks e:
the transition function, the reduction relation, or the proof-checking loop.
That program is finite even when BN(R, .) is uncomputable.

**The line between kappa and n.** kappa(R) is the part of the specification
*shared by every expression e in L*: the parser and the rules. The budget n
is the part that *varies with the individual expression*: the specific
Turing-machine table, the specific lambda term, the specific matrix sequence,
the specific formula. A TM's state and symbol counts are therefore n, not
kappa; kappa(TM) is only the fixed simulator that steps any table.

## 2. What counts toward kappa(R), per family

For each family, kappa(R) is the BLC bit-length of the smallest BLC
interpreter that (a) decodes the family's expression format and (b) applies
the family's evaluation/reduction/proof rules. Below, "counts" means folded
into that interpreter; "does not count" means charged to the budget n or
excluded by convention.

### 2.1 Turing machines (Busy Beaver family)

- **Counts:** the encoding convention for an n-state, 2-symbol transition
  table; the single-step function (read the scanned symbol, write a symbol,
  move left/right, change state); the halting condition; and the output
  readout convention (e.g. the count of 1s left on the tape, or the step
  count for the S variant). Together this is a universal-TM simulator written
  in BLC.
- **Does not count:** any particular machine's table. The state count that
  Busy Beaver treats as its budget is n, so it is excluded from kappa. (See
  Section 4, choice C7: an alternative convention that treats TM stepping as
  the meta-language's own primitive would set this row to kappa ~ 0; we do
  not adopt it, because our meta-language is BLC, not a UTM.)

### 2.2 Lambda calculus / BLC

- **Counts:** the parser for the binary lambda encoding, the
  beta-reduction / normalization rule, and the Church/binary-numeral readout
  convention. This is essentially a BLC self-interpreter (Tromp's universal
  lambda term is the concrete artifact Phase 2 measures).
- **Does not count:** the particular closed term being evaluated (that is n).
- **Definitional wrinkle:** because the meta-language *is* BLC, one can argue
  R = BLC interprets itself "for free," giving kappa(BLC) = 0, or that it
  still costs one self-interpreter, giving kappa(BLC) = the self-interpreter
  length. This choice is flagged in Section 4 (C2).

### 2.3 Bashicu Matrix System (BMS)

- **Counts:** the decoder for the matrix/vector sequence format; the BMS
  expansion rule (locating the "bad root" / part, and the copy-and-increment
  step); and the evaluation that maps a terminating sequence to its value via
  the associated fundamental-sequence / fast-growing-hierarchy readout. Pat
  Kale's BLC port of BMS is the concrete artifact.
- **Single-row vs multi-row:** single-row BMS is a strictly smaller rule set
  (fewer cases in the expansion) than multi-row BMS, so kappa(single-row BMS)
  < kappa(multi-row BMS) by convention; Phase 2 reports both, since
  `BN-function.md` Section 7 lists them as separate rows with different growth
  (epsilon_0 region for single-row, Buchholz's ordinal for the multi-row /
  Pi^1_1-CA_0 rung).
- **Does not count:** the particular starting matrix sequence (that is n).

### 2.4 Proof-theoretic / type-theory systems (Loader's number; System F / CoC; theories up to Pi^1_1-CA_0)

Two sub-cases share one counting rule (kappa = the checker, not any proof):

- **Type-theory sub-case (Loader's number, System F / Calculus of
  Constructions):** counts the term/type parser and the typing rules
  (abstraction, application, type abstraction, and for CoC the dependent
  product), i.e. a type-checker; plus the normalization/readout that turns a
  strongly-normalizing typed term into its numeral. `loader.c` and its ports
  are the concrete artifacts.
- **Formal-theory sub-case (a system whose strength is fixed by a theory T
  such as Pi^1_1-CA_0):** counts the axioms of T, the inference rules of
  first-order logic, and the proof-verification loop (check that a purported
  proof is a valid derivation of "phi(x) = y" and read off y), i.e. a
  proof-checker for T.
- **Does not count:** the particular typed term or the particular proof (that
  is n).
- **Definitional wrinkle (axiom schemas):** theories like this are given by
  *axiom schemas*, infinite families generated by a finite template. We count
  the finite template's BLC length, not the infinitely many instances;
  without this rule kappa would be infinite for every first-order theory. See
  Section 4 (C4).

### 2.5 First-order set theory (Rayo's function)

- **Counts:** the parser for first-order formulas over the single relation
  symbol `in` (membership); the Tarskian satisfaction clauses (the recursive
  truth definition that Rayo's own construction quantifies over); and the
  "names a unique natural number" readout (the formula has exactly one free
  variable and pins down exactly one value).
- **Does not count:** the particular formula (that is n, the symbol budget
  Rayo's function ranges over).
- **Feasibility caveat:** a full BLC satisfaction-relation evaluator for
  first-order set theory is a large undertaking, and Rayo's function is
  defined through a metalinguistic second-order satisfaction predicate.
  Phase 2 may therefore report this row as an explicit estimate with stated
  assumptions, or as "infeasible to pin exactly, lower-bounded by the FOL
  parser + satisfaction skeleton," per the repo rule against reporting a
  guess as a settled value. It is not left as a bare placeholder.

## 3. kappa is an upper bound, never a proven minimum

"The smallest BLC interpreter for R" invokes Kolmogorov complexity, which is
uncomputable: there is no algorithm that certifies a given BLC term is the
shortest interpreter for R. Every kappa(R) reported in Phase 2 is therefore
the length of a concrete, exhibited BLC interpreter (an **upper bound** on the
true description complexity), never a proven minimum. Phase 2 states, per row,
which artifact the bound comes from. A later, shorter interpreter would lower
the estimate; it would never invalidate the ordering unless the gap between
two rows is smaller than the slack in the bounds, which Phase 4 must check
before reading any monotonicity into the table.

## 4. The arbitrary / definitional choices, flagged

Everything in this list is a definitional choice, not a fact about the
systems. The table's conclusions are **conditional** on them. Where a choice
has a bounded effect, the bound is given.

- **C1 (choice of meta-language).** Picking BLC rather than a minimal UTM,
  SKI combinators, or Iota/Jot is arbitrary. By the invariance theorem
  (`BN-function.md` Section 6), changing the meta-language shifts *every*
  kappa(R) by at most an additive constant: the bit-length of a translator
  between the two meta-languages. Consequence: **absolute kappa values are
  convention-dependent; only differences and the induced ordering are
  robust, and even those are robust only up to that additive slack.** This is
  the single most important caveat carried into Phase 4: a "compactness law"
  read off these numbers is a statement about this choice of meta-language,
  not a meta-language-independent theorem.

- **C2 (self-reference charge for BLC).** Whether kappa(BLC) = 0 (the
  meta-language interprets itself for free) or kappa(BLC) = the
  self-interpreter length is arbitrary. Phase 2 reports the self-interpreter
  length and notes the 0 alternative, because charging every family a real
  interpreter and BLC nothing would bias the one row that happens to coincide
  with the meta-language.

- **C3 (parser folded into kappa).** We charge the decoder for L's expression
  format to kappa. One could instead treat the parser as part of e's own
  encoding and charge it to n. This choice moves a fixed number of bits
  between the two axes for every family; it does not change within-family
  budget curves but does shift the kappa column uniformly for families with
  heavy input formats.

- **C4 (axiom schemas as finite templates).** For first-order theories we
  count the finite schema template, not its infinitely many instances.
  Without this the kappa of any first-order theory is infinite. This choice
  is forced (any other choice makes the set-theory and proof-theory rows
  undefined) but it is still a convention, and it is the reason kappa(Rayo)
  is finite at all.

- **C5 (interpreter, not computation).** kappa charges for the rules that
  step e, never for running e to a value. This is what keeps kappa finite for
  Turing-complete R where BN itself is uncomputable. An alternative that tried
  to charge "cost to actually produce BN(R, n)" would be uncomputable and is
  rejected.

- **C6 (upper bound, not minimum).** Per Section 3, each kappa is the length
  of an exhibited interpreter, an upper bound. Treating it as the true
  minimum would be unsound.

- **C7 (the TM ~ 0 alternative).** `PLAN.md` Phase 1 floats the convention
  that TM computation is "the meta-language's own primitive," giving
  kappa(TM) ~ 0. Under this note's choice of BLC as meta-language that is
  **not** adopted: kappa(TM) is the BLC length of a universal-TM simulator,
  which is not zero. We flag this as a genuine definitional fork: a
  UTM-based meta-language would zero out the Turing row and renormalize the
  others, changing the shape of the kappa column. This choice, like C1, is
  part of what Phase 4's conclusion is conditional on.

## 5. Summary of the convention

| Family | Meta-language | What counts toward kappa(R) | Excluded (charged to n) |
|---|---|---|---|
| Turing machines | BLC | universal-TM simulator: table decoder + step function + halt + output readout | the specific machine's table (= n, the state count) |
| lambda / BLC | BLC | self-interpreter: binary-lambda parser + beta-reduction + numeral readout | the specific closed term |
| BMS (single / multi-row) | BLC | matrix-format decoder + expansion rule + FGH readout (Kale's BLC port) | the specific starting sequence |
| proof-theory / type-theory (Loader, System F/CoC, Pi^1_1-CA_0) | BLC | type-checker or proof-checker: parser + typing/inference rules + normalization/verification loop | the specific term or proof |
| first-order set theory (Rayo) | BLC | FOL-over-`in` parser + Tarskian satisfaction clauses + unique-denotation readout | the specific formula |

Every kappa(R) produced under this convention is a BLC-bit upper bound,
defined up to the additive translation constant of C1, conditional on the
definitional choices C1-C7 above. Phase 2 fills in the numbers; Phase 4 reads
the resulting kappa-versus-growth pairs subject to exactly these caveats.
