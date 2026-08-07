# The kappa(R) table

Phase 2 of `PLAN.md`. One row per reference system in `BN-function.md`
Section 7. Each row gives an estimate of kappa(R) in **Binary Lambda Calculus
(BLC) bits** (the meta-language fixed in `METHODOLOGY.md` Section 1), or an
explicit **infeasible** with reason, alongside the growth rate of BN(R, .).

Read `METHODOLOGY.md` before this table. It fixes what kappa(R) counts (the
BLC interpreter for R: parser + evaluation/reduction/proof rules, **not** the
cost of computing any BN value) and flags the definitional choices C1-C7 that
every number here is conditional on. Read `BN-function.md` Section 7 for the
growth column and the admissibility conditions A1-A5.

## How to read every number in the kappa column

Three caveats from `METHODOLOGY.md` apply to the whole column and are not
repeated per row:

1. **Upper bounds, never minima** (`METHODOLOGY.md` Section 3, choice C6).
   "Smallest BLC interpreter for R" is a Kolmogorov-complexity quantity and is
   uncomputable, so every entry is the size of a *concrete exhibited artifact*,
   an upper bound on the true description complexity. A shorter interpreter
   found later would lower an entry; it would not overturn the ordering unless
   the gap between two rows is smaller than the slack in the bounds.
2. **Convention-dependent** (choice C1). Absolute values depend on choosing
   BLC over a UTM / SKI / Iota. Changing meta-language shifts *every* entry by
   at most an additive translation constant (`BN-function.md` Section 6
   invariance). Only the **ordering and the differences** are robust, and even
   those only up to that slack.
3. **The leaderboard anchors over-count kappa, on the safe side.** For the
   ordinal and type-theory rows the anchor is a Tromp fixed-bit leaderboard
   figure from `phase0/c-pole-position.md`: the bit budget at which a BLC term
   *reaches* that growth class. Such a record term must embed the system's own
   evaluator plus a small seed argument, so
   `leaderboard bits >= kappa(R) + (seed n)`. Using the leaderboard figure as
   kappa(R) is therefore a **conservative upper bound** (it includes the seed),
   which is exactly the direction Section 3 already licenses.

## The table

| R | growth rate of BN(R, .) | kappa(R) estimate (BLC bits) | traceable to |
|---|---|---|---|
| Turing machines (Busy Beaver), k-state 2-symbol | uncomputable; grows faster than every computable function (Radó 1962) | **~200-600 bits (estimate)**: BLC universal-TM simulator | `METHODOLOGY.md` 2.1 + C7; anchored to the self-interpreter (Row 2) |
| lambda calculus / BLC (Tromp) | uncomputable | **~206-232 bits**, or **0 bits** under choice C2: Tromp's universal lambda term (BLC self-interpreter) | `METHODOLOGY.md` 2.2 + C2; Tromp self-interpreter (Phase 0, `phase0/c-pole-position.md`) |
| single-row BMS (Bashicu Matrix System, one row) | epsilon_0 (`BN-function.md` Section 7) | **<~111 bits (estimate)**: strictly below multi-row; anchored to the epsilon_0 / Goodstein landmark | Phase 0 `phase0/c-pole-position.md` (epsilon_0 = 111 bits) + `METHODOLOGY.md` 2.3 |
| multi-row BMS (up to Pi^1_1-CA_0) | psi(Omega_omega), Buchholz's ordinal (`BN-function.md` Section 7) | **<~331 bits**: Tromp's "BMS = 331 bits / PTO(Z_2)" record term embeds the BMS evaluator | Phase 0 `phase0/c-pole-position.md` (BMS = 331 bits) + `METHODOLOGY.md` 2.3 |
| System F / Calculus of Constructions (Loader's number) | the proof-theoretic ordinal of System F / CoC (`BN-function.md` Section 7) | **<~1850 bits**: Tromp's Loader landmark; the record term embeds Loader's `D` type-checker/normalizer | Phase 0 `phase0/c-pole-position.md` (Loader = 1850 bits; `loader.c` / eaglgenes101 569-byte Julia port) + `METHODOLOGY.md` 2.4 |
| first-order set theory (Rayo's function) | uncomputable; provably dominates every function whose totality the theory can prove (`BN-function.md` Section 7) | **infeasible** to pin exactly; finite only via choice C4; lower-bounded by the FOL-over-`in` parser + Tarskian-satisfaction skeleton | `METHODOLOGY.md` 2.5 + C4 |

## Row derivations

### Turing machines (Busy Beaver)

kappa charges for a **universal-TM simulator** written in BLC: the decoder for
a k-state 2-symbol transition table, the single-step function (read / write /
move / change state), the halt test, and the output readout (count of 1s, or
step count for the S variant). The specific machine's table, and the state
count k that Busy Beaver treats as its budget, are **n, not kappa**
(`METHODOLOGY.md` 2.1). Growth is uncomputable by the Radó (1962) diagonal
argument recorded in `BN-function.md` Section 6.

No single canonical BLC universal-TM artifact is recorded in Phase 0, so this
entry is an **order-of-magnitude estimate**, not a measured artifact: a UTM
simulator is the same kind of object as the BLC self-interpreter (Row 2, ~232
bits) and modestly larger, because it must additionally carry tape and
table-lookup machinery. Hence ~200-600 bits. Choice **C7** matters here: under
this note's BLC meta-language the row is emphatically **not** kappa ~ 0. The
"TM computation is the meta-language's own primitive" convention floated in
`PLAN.md` Phase 1 would zero this row out, but that convention is only valid
for a UTM meta-language, which was rejected in Phase 1 (`METHODOLOGY.md` C7).

### lambda calculus / BLC

kappa charges for a **self-interpreter**: the binary-lambda parser, the
beta-reduction / normalization rule, and the Church/binary-numeral readout
(`METHODOLOGY.md` 2.2). The concrete artifact is Tromp's universal lambda term
(~232 bits in the classic form; ~206 bits in later optimized form), the
best-grounded entry in the table because it is a real, exhibited, sized object
rather than an estimate. Choice **C2**: because the meta-language *is* BLC, one
can argue R = BLC interprets itself for free (kappa = 0). Both readings are
reported; the self-interpreter length is the primary figure, so that BLC is not
handed a free pass that every other family pays a real interpreter for.

### single-row BMS

kappa charges for the matrix-sequence decoder, the single-row expansion rule
(a strictly smaller case set than multi-row), and the FGH readout
(`METHODOLOGY.md` 2.3). By that same rule kappa(single-row) < kappa(multi-row),
so 331 bits (Row 4) is a hard upper bound. No separately measured
single-row-BMS BLC artifact exists in Phase 0; the tighter ~111-bit anchor is
an **inference**, not a measurement: single-row BMS has epsilon_0 growth
(`BN-function.md` Section 7), and Phase 0's `phase0/c-pole-position.md` records
that the epsilon_0 region (Goodstein) is reached at 111 BLC bits, so a
single-row-BMS interpreter-plus-seed sits in that region. Flagged as an
estimate accordingly.

### multi-row BMS

kappa charges for the full multi-row decoder, expansion rule, and FGH readout;
Pat Kale's BLC port of BMS is the named concrete artifact (`METHODOLOGY.md`
2.3). The <~331-bit figure is Tromp's "Bashicu Matrix System = 331 bits, growth
PTO(Z_2)" landmark from `phase0/c-pole-position.md`, read as an upper bound via
the embed-the-evaluator argument above. Note the field's own ordinal looseness:
`BN-function.md` Section 7 assigns multi-row BMS the Buchholz ordinal
psi(Omega_omega), while Tromp labels the 331-bit landmark PTO(Z_2) (full
second-order arithmetic, a stronger ceiling); the 331-bit anchor is retained as
the conservative upper bound regardless of which of those two ordinals is the
exact growth rate.

### System F / Calculus of Constructions (Loader's number)

kappa charges for a **type-checker**: the term/type parser, the typing rules
(abstraction, application, type abstraction, and the dependent product for CoC),
and the normalization/readout that turns a strongly-normalizing typed term into
its numeral (`METHODOLOGY.md` 2.4). Concrete artifacts: `loader.c` and its ports,
including the 569-byte Julia port by eaglgenes101 recorded in
`phase0/c-pole-position.md` (that 569 is ASCII bytes in a different language, a
real exhibited size but not directly a BLC-bit figure). The BLC-native anchor is
Tromp's Loader landmark, 1850 bits in `phase0/c-pole-position.md`; the
record-holding Loader term embeds Loader's `D` function, so 1850 bits upper-bounds
kappa(System F / CoC) + seed.

### first-order set theory (Rayo's function)

Reported **infeasible** to pin exactly, per the explicit feasibility caveat in
`METHODOLOGY.md` 2.5 and the repo rule against reporting a guess as a settled
value. kappa would charge for the parser of first-order formulas over the single
membership relation `in`, the Tarskian satisfaction clauses (the recursive truth
definition Rayo's own construction quantifies over), and the "names a unique
natural number" readout. Two things block an honest point estimate: a full BLC
satisfaction-relation evaluator for first-order set theory is a large
undertaking with no exhibited sized artifact in Phase 0, and Rayo's function is
defined through a metalinguistic *second-order* satisfaction predicate rather
than an ordinary evaluator. The value is **finite at all only via choice C4**
(axiom schemas counted as their finite template, not their infinitely many
instances; without C4 kappa is infinite for any first-order theory). What can be
stated is a **lower bound**: kappa(Rayo) exceeds the size of the bare
FOL-over-`in` parser plus the satisfaction skeleton, hence larger than the BLC
self-interpreter of Row 2, i.e. at least several hundred BLC bits. Growth is
uncomputable and dominates every function whose totality the theory proves
(`BN-function.md` Section 7).

**R0 refinement (`RAYO-R0-WELLDEFINEDNESS.md`).** The "second-order satisfaction
predicate" above is not just a bigger interpreter — R0 shows it is a truth
predicate for the *whole universe V*, whose very existence is an **MK-strength**
set-theoretic commitment (impredicative comprehension; `Con(ZFC)`-grade), which
Tarski's theorem forbids at first order. So this row's real cost is
under-described by any BLC-bit interpreter figure: it is not the length of an
evaluator but the *strength of a metatheory*, a different axis. See "The
diagonalization family: a second axis" below, where this row is paired against
the Boolos/PA row that reaches `ε₀`-class growth from a merely first-order,
PA-strength commitment.

## What the column does and does not support

Ordering (robust up to the C1/C6 slack, small n seed included in the anchors):

  BLC (~206-232, or 0)  <  single-row BMS (<~111)  <  multi-row BMS (<~331)
  <  System F / CoC (<~1850)  <  Rayo (infeasible, > a few hundred and unbounded
  above by any measured artifact)

with Turing machines (~200-600, estimate) overlapping the low end of that range
because kappa prices only the fixed simulator, not the uncomputable growth it
unlocks. That last point is the table's single most important qualitative
reading and the input to Phase 4: **a small, cheap-to-specify R (a ~few-hundred-
bit universal-TM simulator, or a ~232-bit BLC self-interpreter) already buys
uncomputable, faster-than-every-computable-function growth.** Growth rate does
**not** scale smoothly or expensively with kappa across the Turing-complete rows;
the jump to uncomputable growth is paid for almost entirely at the bottom of the
kappa column. The genuine kappa-buys-growth gradient appears only among the
*sub-Turing-complete, ordinal-indexed* rows (single-row BMS < multi-row BMS <
System F / CoC), where a larger rule set does track a strictly higher
proof-theoretic ordinal. Whether that gradient is a "compactness law" or just
the sequence the googology community happened to formalize is the Phase 4
question (`BN-function.md` Section 8); six points, three of them estimates and
one infeasible, is a sketch, not a theorem.

## The diagonalization family: a second axis (proof-theoretic commitment)

Added after the B0/B1/B3 (Boolos fork) and R0 (Rayo fork) work — see
`BOOLOS-B0-WELLDEFINEDNESS.md`, `BOOLOS-B3-PAPER-VERIFICATION.md`,
`rayo-lean-boolos/BOOLOS-B1-B3-REPORT.md`, and `RAYO-R0-WELLDEFINEDNESS.md`.

**Unit warning.** The rows below are **not** BLC-bit measurements and do not
belong in the table above; merging them would be a category error, the same one
`RAYO-EXPLAINER.md` already flags for its 90-line Lean κ artifact. Their natural
unit is the **proof-theoretic strength of the metatheory a system's naming
predicate requires** — a different axis from BLC interpreter length. They are
recorded here because that axis turns out to be the one that moves within the
self-reference/diagonalization family, and it speaks directly to the Phase 4
question.

Both systems define naming by *diagonalization/self-reference over a
satisfaction-or-provability predicate*, not by ordinal notation or raw TM/BLC
power. What separates them is **which predicate, and how strong a background it
needs to exist**:

| R (diagonalization family) | naming predicate | metatheory it requires | growth of BN(R,·) | status |
|---|---|---|---|---|
| PA + provable-naming (Boolos) | `Prov_PA(⌜∀x(φ↔x=k̄)⌝)` — **first-order expressible** (Σ₁), Tarski-safe | just **PA-strength** (consistency of PA + an arithmetized proof predicate) | eventually dominates every PA-provably-total function, i.e. FGH `≈ ε₀` (PTO of PA) | B0 well-def. proved (paper) + Lean core; B1 `TNames` Lean-verified; **B3 domination paper-verified** (`BOOLOS-B3-PAPER-VERIFICATION.md`), mechanization open |
| FO set theory (Rayo) | truth-naming via `Sat` — **not** first-order expressible (Tarski) | **MK-strength**: an impredicative second-order background / a truth predicate for V (`Con(ZFC)`-grade) | uncomputable; dominates every function whose totality the theory proves | R0 verdict (paper): well-defined **only** relative to that commitment; trivializes without it |

**What this adds to Phase 4.** The table above found a κ-buys-growth gradient
only among the *ordinal-notation* rows (BMS < BMS < System F/CoC) and flagged it
as possibly just selection bias. The diagonalization family gives an
**independent** data point on the *same* underlying question, and it points the
same way: to climb from `ε₀`-class growth (Boolos/PA) to Rayo-class growth
(dominates everything a set theory can prove total) you must climb from a
**first-order, PA-strength** commitment (an arithmetized provability predicate,
which Tarski permits) to an **MK-strength** commitment (a truth predicate for the
whole universe, which Tarski forbids at first order). That is a genuine,
qualitative increase in specification strength tracking a genuine increase in
growth — a κ-buys-growth step that is *not* one of the googology-ladder systems,
so it is **not** the same selection-bias confound as the ordinal rows.

Two cautions keep this honest, both already standing project rules. **(i)** It is
still only two points, and the axis (proof-theoretic strength of the required
metatheory) is not commensurable with the BLC-bit column — so this supports the
*existence* of a commitment-buys-growth gradient in the diagonalization family,
not a unified law across both axes. **(ii)** The Tarski boundary between the two
rows (first-order provability is internal, truth-in-V is not) is a **sharp
qualitative jump**, not a smooth dial — which cuts against, not for, any smooth
"compactness law": it is a second instance (after the Turing-complete rows'
step-to-uncomputable) of growth increasing by a *discrete jump in kind* rather
than a graded price. The overall Phase 4 read is unchanged and slightly
reinforced: **no single smooth law; growth moves in qualitative steps (internal
provability → truth-for-V; computable → uncomputable), with a genuine but
step-shaped commitment-vs-growth gradient inside each family.**
