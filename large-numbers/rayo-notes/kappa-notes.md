# kappa(R) for Rayo's R, measured two ways

R = first-order set theory over the single relation symbol `in`
(`BN-function.md` Section 7's last row; `KAPPA-TABLE.md`'s Rayo row).

`KAPPA-TABLE.md` reports kappa(R) for this row as **infeasible to pin exactly**
in BLC bits, giving only a lower bound: kappa(Rayo) exceeds the FOL-over-`in`
parser plus the Tarskian satisfaction skeleton, hence larger than the Row-2 BLC
self-interpreter, i.e. **at least several hundred BLC bits**. That figure is in
**Binary Lambda Calculus (BLC) bits**, the meta-language fixed in
`METHODOLOGY.md` Section 1.

This note records a second, independent measurement in a **different unit**: the
real size of the Lean 4 artifact that formalizes R's syntax and satisfaction
relation. **Lean source size and BLC bits are not interconvertible** and no
conversion factor is asserted here; they are kept as two distinct rows.

## The measured Lean artifact size (Lean tokens, not BLC bits)

The self-contained (no-Mathlib) Lean formalization lives in `rayo-lean/Rayo/`.
Measured with `wc` on the files that carry the syntax datatype, the satisfaction
relation, and the finite-set model:

| file | role | lines | words (Lean tokens) |
|---|---|---|---|
| `Rayo/Syntax.lean` | `Formula` inductive datatype (FOL over `in` + `=`) | 30 | 162 |
| `Rayo/Satisfaction.lean` | `HF` finite-set model + `Sat` Tarski relation | 60 | 394 |
| `Rayo/Model.lean` | (absent: the HF model is inside `Satisfaction.lean`) | 0 | 0 |
| **total (kappa artifact)** | | **90** | **556** |

So the measured **Lean-artifact size of kappa(R) is 90 lines / 556 Lean tokens**
(comments and blank lines included, as `wc` counts them). "Lean tokens" here
means whitespace-delimited words as counted by `wc -w`; it is a Lean source
measure and is explicitly **not** a BLC-bit count.

Notes on scope of the count:

- The count follows the frozen verify convention exactly:
  `cat Rayo/Syntax.lean Rayo/Satisfaction.lean Rayo/Model.lean | wc -l`. There
  is no separate `Model.lean`; the hereditarily-finite-set (HF) model is defined
  inside `Satisfaction.lean` (the `HF` inductive, `HF.Mem`, `HF.empty`, `Env`),
  so its `2>/dev/null` contribution is 0 lines and the total is 90.
- `Rayo/K0.lean` (65 lines / 403 words) is **excluded** from the kappa figure.
  It is the k = 0 naming spike (the formula phi_0 and its uniqueness proof), i.e.
  part of the "name n" side of the kappa(R)+n framing, not part of "the rules".
  Charging it to kappa would double-count the per-k naming cost.

## Two units, two figures, no false conversion

- **BLC bits (KAPPA-TABLE.md):** kappa(Rayo) is infeasible to pin exactly;
  lower bound "at least several hundred BLC bits" (FOL parser + satisfaction
  skeleton, above the ~206-232-bit Row-2 self-interpreter).
- **Lean source (this note):** 90 lines / 556 Lean tokens for the exhibited,
  type-checked syntax + satisfaction + finite-set-model artifact.

Both are **upper-bounds-on / concrete-exhibits-of** the same object (the rules of
R) rather than minima, matching `METHODOLOGY.md` choice C6. They are recorded
side by side as distinct units; the Lean line count does **not** refine the
BLC-bit lower bound and no ratio between the two is claimed.
