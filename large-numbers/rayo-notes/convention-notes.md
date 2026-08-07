# The symbol-counting convention (Phase A(a))

This note fixes, once, the convention under which every per-k formula cost
n_k in this run is counted. It is the *n-axis* convention for the Rayo /
first-order-set-theory row: the number of symbols in the cheapest known
formula phi_k(x) that uniquely names the natural number k. It is deliberately
separate from `KAPPA-TABLE.md`'s kappa(R) axis, which is measured in Binary
Lambda Calculus (BLC) bits; the two units are not interconvertible and no
conversion between them is asserted here (see "Relation to kappa(R)" below).

Everything in this note is a **definitional choice, flagged as arbitrary** in
the spirit of `METHODOLOGY.md` Section 4, choices C1 (choice of measuring
convention is arbitrary and shifts every number) and C3 (where the parser /
grammar boundary is drawn moves a fixed count between axes). A different but
equally defensible convention would change the absolute counts; only the
*ordering* of the n_k and the *differences* between them are robust, and even
those only up to the slack these choices introduce. The convention is fixed
here so that all Phase C counts are commensurable with one another, not
because it is the uniquely correct one.

## 1. The object being counted

For each natural k we count the symbols of a first-order formula phi_k(x) with
exactly one free variable x, over the language of set theory with the single
binary relation symbol `in` (membership) and equality `=`, such that phi_k(x)
is satisfied by exactly one set, and that set is the natural number k under the
von Neumann encoding (Section 3). The count n_k is the total number of symbol
**occurrences** in phi_k(x) under the alphabet and per-occurrence rule below.

## 2. The alphabet (primitive symbols)

The adopted primitive alphabet is the minimal set

    { in, =, not, and, exists, forall, ( , ) }  plus a countable supply of variables.

Each of these is one symbol:

- `in`   the membership relation symbol (one symbol, not two).
- `=`    equality.
- `not`  negation (unary connective).
- `and`  conjunction (binary connective).
- `exists`  the existential quantifier.
- `forall`  the universal quantifier.
- `(` and `)`  the two grouping parentheses, counted individually.
- each **variable** (x, y, z, y_0, y_1, ...): see the per-occurrence rule in
  Section 4.

### Connectives and quantifiers NOT in the primitive set

`or`, `implies` (->), `iff` (<->), and the unique-existential `exists!`
(unique-exists, "there is exactly one") are **not** primitives. They are
treated as **abbreviations that expand** into the primitive alphabet, and a
formula that uses them is counted at the cost of its fully expanded primitive
form, using the standard classical expansions:

- `A or B`        :=  `not ((not A) and (not B))`
- `A implies B`   :=  `not (A and (not B))`
- `A iff B`       :=  `(A implies B) and (B implies A)`
- `exists! x. P(x)`  :=  `exists x. ( P(x) and forall y. ( P(y) implies y = x ) )`
  (with `implies` further expanded as above; `y` a fresh variable).

Rationale: this keeps the baseline minimal and comparable to a
minimal-primitive first-order grammar, and it prevents a formula from looking
cheaper merely because it was written with a richer connective set. Rejected
alternative: counting or/implies/iff/unique-exists as free primitives, which
would systematically lower counts and break comparability against the minimal
baseline. (`ASSUMPTIONS.md`: "Whether the recommended minimal primitive
alphabet ... is adopted".) The run may override this with a stated reason, but
this expansion convention is the default and is what Phase C uses unless a
per-k finding explicitly flags a departure.

Note (C3 boundary): whether the two parentheses are counted at all, or folded
into the connective/quantifier that induces them, is itself a convention. We
count parentheses as explicit symbols. A polish/prefix notation that dropped
them would lower every count by a fixed amount per binary node; this is exactly
the kind of fixed inter-axis shift C3 describes and is flagged, not hidden.

## 3. Number encoding: von Neumann ordinals

Naturals are encoded as **von Neumann ordinals**:

    0 = empty set
    1 = { 0 }            = { {} }
    2 = { 0, 1 }         = { {}, {{}} }
    n+1 = n union { n }   (each natural is the set of all smaller naturals)

So "phi_k(x) names k" means the unique x satisfying phi_k(x) is the von
Neumann k: for k = 0, x is the empty set; for k = 1, x is the set whose sole
element is the empty set; and so on. This is the encoding Rayo's construction
and the standard set-theoretic development of arithmetic use, and it is what
lets a pure `in`/`=` formula pin a number down with no arithmetic primitives.
Rejected alternatives (Zermelo naturals {{{...}}}, or any tagged encoding)
would change which formulas are cheapest and are not used.

## 4. The per-occurrence counting rule

**Each symbol occurrence counts as one, and each variable occurrence counts as
exactly one symbol regardless of which variable it is.** Concretely:

- Total cost n_k = the number of symbol occurrences in the fully
  expanded primitive-alphabet form of phi_k(x).
- A variable is charged **per occurrence**, not per distinct name: if the
  variable `y` appears four times, that is four symbols. Reusing a name versus
  introducing a fresh one costs the same per appearance.
- The *identity* of a variable is free: `x`, `y`, `z`, `y_0`, `y_17` each cost
  one per occurrence. We do **not** charge per distinct variable name and do
  **not** charge index bits (e.g. the subscript in `y_17`). Variables are
  freely renameable, so charging for their names would penalize formulas that
  happen to need many simultaneously-live variables, which is not the standard
  length measure. (`ASSUMPTIONS.md`: "Whether each variable occurrence counts
  as one symbol regardless of which variable is used.")

Rejected alternative: charging per distinct variable name, or per index bit of
a variable's subscript. Rejected because it is non-standard and penalizes
variable-heavy formulas without changing what they express.

## 5. Worked illustration (k = 0)

The empty set is named by "x has no members":

    phi_0(x)  :=  forall y ( not ( y in x ) )

Counting occurrences under Sections 2 and 4:
`forall`(1) `y`(1) `(`(1) `not`(1) `(`(1) `y`(1) `in`(1) `x`(1) `)`(1) `)`(1)
= **10 symbols**. (The exact k=0 count and its mechanized uniqueness proof are
Phase A(c)/Phase C deliverables and are recorded there; this is only an
illustration of how the rule applies, not the pinned n_0.)

## 6. Relation to kappa(R)

n_k (this note) and kappa(R) (`KAPPA-TABLE.md`) are different axes in
different units:

- n_k is a **first-order-symbol** count of one formula phi_k(x) under the
  convention above.
- kappa(R) is a **BLC-bit** length of the fixed interpreter (FOL-over-`in`
  parser + Tarskian satisfaction clauses + unique-denotation readout), per
  `METHODOLOGY.md` Section 2.5.

They are combined only in the Phase D table as a labelled pair
`kappa(R) + n_k`, exactly as `BN-function.md` frames every other system, with
the two units kept explicitly distinct. No numeric conversion between FOL
symbols and BLC bits is asserted; doing so would be a false precision the
invariance argument (`BN-function.md` Section 6, `METHODOLOGY.md` C1) does not
license.

## 7. Summary

| Item | Fixed choice |
|---|---|
| Primitive alphabet | `{ in, =, not, and, exists, forall, ( , ) }` + variables |
| or / implies / iff / unique-exists | abbreviations; counted at their expanded primitive cost |
| Number encoding | von Neumann ordinals (0 = empty set, n+1 = n union {n}) |
| Variable charge | one symbol per **occurrence**, identity and index free |
| Parentheses | counted individually as explicit symbols |
| Unit | FOL symbol occurrences (n-axis), distinct from kappa's BLC bits |
| Status | arbitrary/definitional, flagged per `METHODOLOGY.md` C1/C3 |

This convention is frozen for the run. Any per-k formula in Phase C is counted
under exactly these rules; a departure, if ever needed, is recorded as a
flagged exception in that k's finding, not by silently re-reading this note.
