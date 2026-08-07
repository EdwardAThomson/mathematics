# The combined-cost table (Phase D)

R = first-order set theory over the single relation symbol `in` (the Rayo /
first-order-set-theory row of `BN-function.md` Section 7 and `KAPPA-TABLE.md`).

This note **aggregates** the two axes the run measured into one combined-cost
table, in the `kappa(R) + n` framing `BN-function.md` uses for every other
system. It is the Phase D deliverable; every number it cites is established and
recorded in `FINDINGS.md` and derived in `notes/kappa-notes.md`,
`notes/convention-notes.md`, and the per-k `rayo-lean/Rayo/K*.lean` proofs.

## Two axes, two units, no false conversion

The combined cost for naming a natural k is the labelled pair

    total cost(k)  =  kappa(R)  +  n_k

with the two summands kept in their **own units** and **not numerically added**
(they are not interconvertible; see `notes/convention-notes.md` §6 and
`notes/kappa-notes.md`). This is exactly how `BN-function.md` frames the
kappa-plus-n cost everywhere else.

- **kappa(R) = the fixed cost of "the rules"** (the FOL-over-`in` grammar plus
  the Tarskian satisfaction / evaluation machinery), paid once, independent of
  k. Measured two ways:
  - **BLC bits (`KAPPA-TABLE.md`):** infeasible to pin exactly; lower bound
    **at least several hundred BLC bits** (the FOL-over-`in` parser plus the
    satisfaction skeleton, above the ~206-232-bit Row-2 BLC self-interpreter).
  - **Lean source (`notes/kappa-notes.md`):** an exhibited, type-checked
    artifact of **90 lines / 556 Lean tokens** (`Rayo/Syntax.lean` +
    `Rayo/Satisfaction.lean`; the HF finite-set model lives inside the latter).
- **n_k = the per-k cost of "naming k"**: the number of FOL symbol occurrences
  in the cheapest known formula phi_k(x) that uniquely names the von Neumann
  ordinal k, under the frozen convention in `notes/convention-notes.md`
  (alphabet `{in, =, not, and, exists, forall, (, )}` + variables;
  or/implies/iff/unique-exists counted at expanded primitive cost; per-occurrence
  variable charge). Each n_k is an **upper bound on the minimum** (cheapest
  *known* formula, not proven-minimal), and each phi_k has a machine-checked
  Lean uniqueness proof (no sorry/admit).

## The combined-cost table

For each k reached, `total cost = kappa(R) + n_k`:

| k | von Neumann k | n_k (FOL symbols) | kappa(R) (fixed) | total cost = kappa(R) + n_k | Lean proof |
|---|---|---|---|---|---|
| 0 | {} | 10 | >= several hundred BLC bits / 90 Lean lines / 556 tokens | kappa(R) + 10 | `Rayo/K0.lean` |
| 1 | {0} | 30 | " (same fixed kappa) | kappa(R) + 30 | `Rayo/K1.lean` |
| 2 | {0,1} | 128 | " | kappa(R) + 128 | `Rayo/K2.lean` |
| 3 | {0,1,2} | 403 | " | kappa(R) + 403 | `Rayo/K3.lean` |
| 4 | {0,1,2,3} | 1228 | " | kappa(R) + 1228 | `Rayo/K4.lean` |
| 5 | {0,1,2,3,4} | 3703 | " | kappa(R) + 3703 | `Rayo/K5.lean` |
| 6 | {0,1,2,3,4,5} | 11128 | " | kappa(R) + 11128 | `Rayo/K6.lean` |

kappa(R) is the **same fixed cost in every row** (it prices the rules, not any
particular k); only n_k varies with k. The two columns stay in distinct units,
so the "total cost" column is a labelled pair, not an arithmetic sum.

### What the n_k column shows

The per-k naming cost grows fast and settles onto a clean ratio: successive
ratios n_{k+1}/n_k are 3.00, 4.27, 3.15, 3.05, 3.02, 3.00, converging to about
**3x per additional natural** (each phi_{k+1} rebuilds phi_0..phi_k plus a
De Morgan "no other members" clause, so the formula roughly triples in size each
step). Naming k under this construction therefore costs on the order of 3^k
symbols. This is the *cheapest known* construction, not a proven lower bound: a
cleverer phi_k could be smaller, which would only lower the n_k column.

## Largest k reached, and why the run stopped

**Largest k reached: k = 6** (n_6 = 11128 symbols), with a complete
machine-checked uniqueness proof. Every phi_k for k = 0..6 was constructed,
symbol-counted under the frozen convention, and proved in Lean 4 (v4.32.2,
self-contained no-Mathlib HF-set route) to name exactly the von Neumann k up to
extensional equality, with no proof holes.

**Why the run stopped at k = 6** (the checklist's stated stop rules, in order of
what actually bound):

- **Planned per-k ceiling, not a hard failure.** The checklist enumerated the
  per-k chain up to k = 6 as the planned ceiling ("extends the small-n table to
  k=6 if the budget allows before the 3-hour hard stop") and all six per-k items
  plus k=0 were reached and committed. The run stopped because it **completed the
  planned chain**, then ran this aggregation item, not because a k=7 proof failed.
- **Per-k budget / proof difficulty was the real gradient.** Each step roughly
  triples the formula (n_k: 10, 30, 128, 403, 1228, 3703, 11128) and enlarges
  the Lean uniqueness proof (more member-class disjointness lemmas, a longer
  De Morgan clause), so each additional k costs materially more prover effort
  than the last. The per-k chain was designed to stall gracefully at whatever k
  it reached under the 3-hour hard stop; k = 6 is where the planned enumeration
  ended.
- **Toolchain was not the limit.** Lean 4 installed inside the 40-minute cap and
  every K*.lean built clean; the toolchain did not block progress.

So the binding reason is **the planned per-k ceiling (k=6) reached within the
per-k budget under the 3-hour hard stop**, with rising per-k proof difficulty as
the underlying gradient, not toolchain limits.

## What this does and does not say about Rayo's number

This run confirms one qualitative thing and **nothing quantitative about Rayo's
actual googol-scale number**:

- It shows that **bootstrapping first-order set theory is expensive relative to
  a tiny symbol budget**: even naming the number 6 already costs ~11k symbols
  under this cheapest-known construction (~3x per step), and this is the *naming*
  side, entirely separate from the ~few-hundred-BLC-bit / 90-Lean-line fixed cost
  of the rules themselves.
- It says **nothing** about Rayo(10^100). Rayo's number is the **inverse**
  quantity: the largest number nameable in a googol symbols, not the symbol cost
  of naming a chosen number. Our n_k table (symbols needed to name a fixed small
  k) does not bound Rayo(n) (largest k nameable in n symbols). The ~3^k growth of
  our *specific, naive* phi_k construction is an artifact of that construction,
  not of optimal FOST naming; Rayo's function ranges over *all* formulas of a
  given length, including ones that exploit arithmetic-in-set-theory tricks our
  von-Neumann-membership formulas never touch. Nothing here refines, bounds, or
  even gestures at the value of Rayo's number; the only transferable point is
  that the fixed rules cost is small (a few hundred bits) while a naive per-k
  naming cost climbs steeply, consistent with `KAPPA-TABLE.md`'s reading that a
  cheap-to-specify R already unlocks growth far out of proportion to kappa.

## Provenance

- kappa(R): `notes/kappa-notes.md`; `FINDINGS.md` (Lean artifact 90 lines / 556
  tokens; BLC-bit lower bound from `KAPPA-TABLE.md`).
- n_k and the counting convention: `notes/convention-notes.md`; `FINDINGS.md`
  per-k entries; `rayo-lean/Rayo/K0.lean`..`K6.lean` (machine-checked).
- Framing (`kappa(R) + n`, two units kept distinct): `BN-function.md`;
  `METHODOLOGY.md` C1/C3/C6.
