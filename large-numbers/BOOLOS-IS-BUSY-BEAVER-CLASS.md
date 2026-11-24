# `BoolosBig_T` is Busy-Beaver class, not `ε₀` class

**Status, 2026-11-24: partly machine-checked.**

- **Machine-checked** (`rayo-lean-boolos/RayoBoolos/Minimization.lean`,
  sorry-free, axioms `propext`, `Classical.choice`, `Quot.sound`):
  the minimization-naming lemma (`minGraph_names`); Theorem 1 in its
  domination form, `BoolosBig_PA_dominates_computable : Computable f → ∃ N,
  ∀ m > N, BoolosBig_PA m ≥ f m`; and `BoolosBig_PA_not_computable`.
- **Machine-checked** (`rayo-lean-boolos/RayoBoolos/Binary.lean`, same
  bar): the logarithmic bound of Theorem 1, `BoolosBig_PA_log_bound :
  Computable f → ∃ C, ∀ n, f n ≤ BoolosBig_PA (C + 6 * Nat.log2 n)`.
- **Machine-checked** (`rayo-lean-boolos/RayoBoolos/AnyTheory.lean`, same
  bar): the lower-bound half of theory independence. `BoolosBigIn T` is the
  function for an arbitrary theory; `BoolosBigIn_log_bound` gives one
  constant `C`, independent of `T`, with `f n ≤ BoolosBigIn T (C + 6 *
  Nat.log2 n)` for every consistent `T ⊇ 𝗣𝗔⁻`; also
  `BoolosBigIn_dominates_computable`, `BoolosBigIn_not_computable`,
  `BoolosBigIn_mono_theory`, and `BoolosBigIn_PA` (it agrees with
  `BoolosBig_PA`). Only consistency of `T` is used, not soundness, and the
  base theory is `𝗣𝗔⁻`, which has no induction.
- **Machine-checked** (`rayo-lean-boolos/RayoBoolos/BusyBeaver.lean`, same
  bar): Theorem 2, the Busy Beaver lower bound, for Mathlib's programs
  (`Nat.Partrec.Code`) indexed by code number: `BB_le_BoolosBigIn` and
  `BBtime_le_BoolosBigIn`, `BB N ≤ BoolosBigIn T (C + 6 * Nat.log2 N)` with
  one `C` for all consistent `T ⊇ 𝗣𝗔⁻`. The general form is
  `BoolosBigIn_partrec_bound`, for any partial recursive function.
- **Machine-checked** (`rayo-lean-boolos/RayoBoolos/UpperBound.lean`, same
  bar): Theorem 3 and Corollary 4 in a non-quantitative form. Proof search
  for a computably axiomatized `T` is a partial recursive function
  (`exists_search`), and `BoolosBigIn_le_any` gives `BoolosBigIn T n ≤
  BoolosBigIn U (C + 6 * Nat.log2 (templateCode n))` for every consistent
  `U ⊇ 𝗣𝗔⁻`, where `templateCode n` is a fixed function independent of both
  theories.
- **Still paper only:** the `n log n` size of that rescaling (it needs an
  efficient formula encoding), and Corollary 5.

The rest of the project has been edited to match (§7): `README.md`,
`KAPPA-TABLE.md`, `RAYO-GROWTH-RATE.md`, and a correction note in
`BOOLOS-B0-WELLDEFINEDNESS.md` §6. The central correction, that `BoolosBig_PA` is not an
`ε₀`-class function but dominates every computable function, no longer
depends on anyone's reading of a paper proof.

## 0. Summary in plain language

Several notes in this project (`README.md`, `KAPPA-TABLE.md`,
`RAYO-GROWTH-RATE.md`, `BOOLOS-B0-WELLDEFINEDNESS.md` §6) describe the
provability-based function `BoolosBig_PA` as growing at "about `ε₀`", the
ceiling of the functions Peano Arithmetic can prove total. That is the *lower
bound we proved* (`BoolosBig_PA_dominates`), and it has been read as the
function's actual size. It is not. The claims of this note:

1. **`BoolosBig_PA` eventually dominates every computable function**, not just
   the PA-provably-total ones (Theorem 1). The proof is shorter than the one
   already mechanized, needs no totality proof inside PA, and needs no
   monotonicity assumption on `f`.
2. **It dominates a Busy Beaver function**, up to a linear rescaling of the
   argument (Theorem 2), so it is not computable.
3. **It is dominated by a Busy Beaver function**, up to an `n log n` rescaling
   of the argument (Theorem 3).
4. **The choice of theory barely matters** (Corollary 4). Replacing PA by any
   consistent, computably axiomatized theory that contains a little
   arithmetic, weaker or far stronger, changes the function by at most such a
   rescaling of the argument.

So provable naming does not sit on an `ε₀` rung between the ordinal
notations and Rayo. It sits in the same tier as Turing machines and lambda
calculus.

The individual ingredients are standard (Σ₁-completeness, minimization,
proof search). I have not searched the literature for this exact statement
and would expect it to be folklore; the point of the note is that it corrects
our own reading.

*Literature check, 2026-11-24 (`LITERATURE-SURVEY.md`):* the notion of
"names" here is exactly Boolos's (1989). The sandwich and theory
independence were not found stated explicitly in the sources read; they are
best described as apparently unstated folklore. Theorem 1's first claim is
classical representability with short numerals.

## 1. Setting

Fix a theory `T` in the language of arithmetic `ℒₒᵣ = {0, 1, +, ·, <}` with:

- **(A1)** `T` is consistent and computably axiomatized (so its proofs can be
  enumerated by a program);
- **(A2)** `T` proves every true Σ₁ sentence (**Σ₁-completeness**);
- **(A3)** `T` proves `<` is a linear order (trichotomy is all that is used).

PA satisfies all three. So do `PA⁻`, `IΣ₁`, and the arithmetic part of ZFC.

Definitions, exactly as in `rayo-lean-boolos/RayoBoolos/`:

- A formula `φ(x)` with one free variable **T-names** `k` when
  `T ⊢ ∀x (φ(x) ↔ x = k̄)` (`TNamesMeta`).
- `|φ|` is the node count `fSize`: one per connective, quantifier, relation
  symbol, function symbol and variable occurrence.
- `BoolosBig_T(n) := max { k : some φ with |φ| ≤ n T-names k }`.

`BoolosBig_T` is well defined and monotone: there are finitely many formulas
of size `≤ n`, and by consistency each names at most one number (if it named
`k₁ ≠ k₂` then `T ⊢ k̄₁ = k̄₂`, which a consistent `T` with (A2) refutes).
This is `BOOLOS-B0-WELLDEFINEDNESS.md`, mechanized for PA as
`namedValues_finite`, `TNamesMeta_unique`, `BoolosBig_PA_mono`.

## 2. The one lemma: naming by minimization

**Short numerals.** Define closed terms `bin(n)` by `bin(0) = 0`,
`bin(1) = 1`, `bin(2m) = (1+1)·bin(m)`, `bin(2m+1) = (1+1)·bin(m) + 1` for
`m ≥ 1`. Then `bin(n)` has value `n` and `|bin(n)| ≤ 6·log₂(n+2)`. (Each
doubling step adds at most 6 nodes.) This replaces the unary numeral, whose
`O(n)` cost is what forced the `n²` pre-inflation in
`BOOLOS-B3-PAPER-VERIFICATION.md` §3.

**Lemma (minimization naming).** Let `δ(z, x, w)` be a Δ₀ formula. Put

```
B(z, x, s)  :≡  x ≤ s ∧ ∃w ≤ s  δ(z, x, w)

μ(z, x)     :≡  ∃s [ B(z, x, s)
                   ∧ ∀s' < s ∀x' ≤ s'  ¬B(z, x', s')
                   ∧ ∀x' < x  ¬B(z, x', s) ]

μₙ(x)       :≡  ∃z ( z = bin(n) ∧ μ(z, x) )
```

In words: `s` is the least bound below which *some* pair `(x, w)` satisfying
`δ` appears, and `x` is the least such `x` at that bound. Suppose that in the
standard model `∃x ∃w δ(n, x, w)` holds, and let `k` be the `x` selected this
way. Then

- (a) `μₙ` T-names `k`;
- (b) `|μₙ| ≤ C_δ + 6·log₂(n+2)`, where `C_δ` depends only on `δ`.

*Proof.* (b) is a count: `μ(z, x)` is one fixed formula, and `n` enters only
through the single occurrence of `bin(n)`.

(a), direction `←`. The sentence `μₙ(k̄)` is Σ₁: an existential quantifier
(`∃z ∃s`) in front of a formula with only bounded quantifiers. It is true in
the standard model by the choice of `k`. By (A2), `T ⊢ μₙ(k̄)`.

(a), direction `→`. Uniqueness is provable in `T` from the shape of `μ`
alone. Work in `T`; suppose `μ(z, x)` with bound `s` and `μ(z, y)` with bound
`s'`.

- If `s < s'`: the second clause for `y` says `∀s'' < s' ∀x' ≤ s'' ¬B(z, x',
  s'')`. Take `s'' = s`, `x' = x` (we have `x ≤ s` from `B(z, x, s)`). This
  gives `¬B(z, x, s)`, contradicting `B(z, x, s)`.
- If `s' < s`: symmetric.
- So `s = s'` by trichotomy (A3). If `x < y`, the third clause for `y` gives
  `¬B(z, x, s)`, a contradiction; `y < x` is symmetric. So `x = y`.

Hence `T ⊢ ∀x ∀y (μₙ(x) ∧ μₙ(y) → x = y)`. Together with `T ⊢ μₙ(k̄)` this
gives `T ⊢ ∀x (μₙ(x) → x = k̄)`. ∎

**What the lemma does not need.** It never asks `T` to prove that a witness
exists *for all* `n`. It uses only that, for each particular `n`, a witness
does exist, which makes one particular Σ₁ sentence true and therefore
provable. That is the whole difference from the mechanized route, which
derived the naming fact from `T ⊢ ∀n ∃!y θ(y, n)` and so was restricted to
provably total functions.

**As mechanized.** `Minimization.lean` uses a slightly different wrapper,
`minGraph θ`: "some `s ≥ x` gives `θ` a witness bounded by `s`, and every
`x' ≤ s' ≤ s` with a witness bounded by `s'` equals `x`". Instead of
asserting that `s` is minimal it asserts that everything found below `s`
agrees. Uniqueness then needs only that `≤` is total (`minGraph_unique`),
and the formula is Σ₁ because the bounded version of `θ` is Δ₀
(`hierarchy_bd`). `Foundation`'s Σ₁ formulas are not in the prenex form
`∃w δ` assumed above, so the Lean proof first bounds every existential
quantifier of `θ` by a fresh variable (`bd`) and proves in `ℕ` that this is
sound, monotone, and complete for true Σ₁ formulas (`of_bd`, `bd_mono`,
`exists_bd`).

## 3. Theorem 1: domination of every computable function

**Theorem 1.** Let `f : ℕ → ℕ` be any total computable function. There is a
constant `C_f` with

```
BoolosBig_T( C_f + 6·log₂(n+2) )  ≥  f(n)        for every n.
```

Consequently there is `N` with `BoolosBig_T(m) ≥ f(m)` for all `m > N`.

*Proof.* The graph of a computable function is Σ₁: there is a Δ₀ formula
`δ_f(z, x, w)` with `f(n) = k ⟺ ℕ ⊨ ∃w δ_f(n, k, w)`. Apply the Lemma. For
each `n` a witness exists (`f` is total), and since `x = f(n)` is the *only*
value with a witness, the selected `k` is `f(n)`. So `μₙ` T-names `f(n)` and
has size `≤ C_f + 6·log₂(n+2)`, giving the first claim by the definition of
`BoolosBig_T`.

For the second, `C_f + 6·log₂(m+2) ≤ m` for all large `m`, and `BoolosBig_T`
is monotone, so `BoolosBig_T(m) ≥ BoolosBig_T(C_f + 6·log₂(m+2)) ≥ f(m)`. ∎

**[Lean]** for both claims. The first is `BoolosBig_PA_log_bound`
(`Binary.lean`), in the form `f n ≤ BoolosBig_PA (C + 6 * Nat.log2 n)`,
using the binary numerals of §2 (`bin`, `tSize_bin_le`, `val_bin`). The
second is `BoolosBig_PA_dominates_computable` (`Minimization.lean`), which
was proved first and by a cruder route: unary numerals, a naming formula of
size linear in `n`, applied to `g(n) := max_{i ≤ n²} f(i)` with `n ≈ √m`.

Three remarks.

- **No monotonicity of `f`.** The mechanized theorem needs `Monotone f` to
  move from `f(n²)` back to `f(m)`. Here the name is for `f(m)` itself.
- **The bound is exponentially stronger than domination.** Reading it the
  other way, `BoolosBig_T(m) ≥ f(2^⌊(m − C_f)/6⌋ − 2)`.
- **Corollary: `BoolosBig_T` is not computable.** **[Lean,
  `BoolosBig_PA_not_computable`]** If it were, `f :=
  BoolosBig_T + 1` would be computable, and Theorem 1 would give
  `BoolosBig_T(m) ≥ BoolosBig_T(m) + 1` for large `m`.

In particular `BoolosBig_PA` eventually dominates the Goodstein function,
`f_{ε₀}`, the Buchholz-hydra function, `f_α` for every computable ordinal
notation `α`, and every row of `KAPPA-TABLE.md` below the uncomputable ones.

## 4. Theorem 2: a Busy Beaver lower bound

Fix a universal machine `U` taking binary programs, and let

```
S(ℓ) := max { t : some program p with |p| ≤ ℓ halts on U after exactly t steps }.
```

This is the Busy Beaver step function for `U`. (Radó's `S(k)` for `k`-state
machines is the same thing for a particular encoding; a `k`-state, 2-symbol
machine is a program of about `2k·log₂(4k)` bits.)

**Theorem 2.** There are constants `a, b` with `BoolosBig_T(a·ℓ + b) ≥ S(ℓ)`
for every `ℓ`.

*Proof.* "The program with code `z` halts on `U` after exactly `x` steps, as
witnessed by the computation record `w`" is a Δ₀ formula `δ_U(z, x, w)`. Let
`p` be a program of length `≤ ℓ` that halts after `t` steps, and let `n < 2^(ℓ+1)`
be its code. A witness exists and `t` is the only `x` with one, so by the
Lemma `μₙ` T-names `t`, with `|μₙ| ≤ C_U + 6·log₂(n+2) ≤ 6ℓ + C_U + 12`. ∎

## 5. Theorem 3: a Busy Beaver upper bound

**Theorem 3.** There are constants `c` (absolute) and `c_T` with
`BoolosBig_T(n) ≤ S(c·n·log₂(n+2) + c_T)` for every `n`.

*Proof.* For a formula `φ` let `P_φ` be the program: "enumerate all
`T`-proofs; on finding a proof of `∀x(φ(x) ↔ x = k̄)` for some `k`, idle for
`k` further steps and halt." By (A1) this is a program. If `φ` T-names `k`
then `P_φ` halts, after more than `k` steps. Its length is a fixed
proof-searcher (`c_T` bits) plus a description of `φ`. A formula with `n`
nodes is described by its tree shape and one label per node; every label
comes from a fixed finite set except variable indices, which are below the
quantifier depth and so below `n + 1`. That is `O(n log n)` bits. Taking `φ`
to be the formula of size `≤ n` naming `BoolosBig_T(n)` gives the claim. ∎

The `log n` factor is an artifact of `fSize` charging one unit for a variable
occurrence whatever its index. Under a size measure that charges for the
index, the bound is linear.

## 6. Corollaries

**Corollary 4 (theory independence).** Let `T ⊆ T'` both satisfy (A1)-(A3).
Then for all `n`

```
BoolosBig_T(n)  ≤  BoolosBig_T'(n)  ≤  BoolosBig_T( a·(c·n·log₂(n+2) + c_T') + b ).
```

*Proof.* The first inequality holds because `T'` proves everything `T` does.
The second is Theorem 3 for `T'` followed by Theorem 2 for `T`. ∎

So passing from PA to ZFC, or to ZFC with large cardinals, buys at most a
slightly-more-than-linear stretch of the argument plus a constant. The reason
is visible in the proofs: PA can name the halting time of *any* halting
program, including the program that searches through ZFC-proofs.

The constant `c_T'` is where theory strength hides, and it is not negligible
at small `n`: a strong theory may name, with a short formula, a number whose
shortest PA-name is much longer. What the corollary rules out is a difference
of growth *class*.

**Corollary 5 (degree).** `BoolosBig_T` is Turing-equivalent to the halting
problem. From `BoolosBig_T` one computes a bound on halting times (Theorem
2), which decides halting. Conversely, with a halting oracle one can decide
for each `φ` whether `P_φ` halts, hence compute the maximum.

**Corollary 6 (strict transcendence for free).**
`BOOLOS-B3-PAPER-VERIFICATION.md` §4 notes that the direct route proves only
`≥` every PA-provably-total function and not that `BoolosBig_PA` escapes
that class. It does escape: it is not computable at all.

## 7. What this changes in the project

**Applied 2026-11-24**, after Theorem 1 was machine-checked.

- **`README.md` "The throughline"**: "Boolos burns provability-in-PA … and
  tops out at growth class ε₀" should read that it reaches Busy-Beaver class.
  The sentence that the gap between the forks "traces to one variable" still
  stands, but the two settings of that variable are now *computably
  enumerable* (provability, in any theory) versus *not arithmetically
  definable* (truth in `V`), and the strength of the theory is not the dial.
- **`KAPPA-TABLE.md`** Boolos row (and lines ~174, ~226-233): growth is
  "uncomputable, Busy-Beaver class", joining the saturating Turing-complete
  rows. It is no longer a second mechanism landing at `ε₀`, so it is not the
  evidence about the sub-Turing gradient that
  `BOOLOS-B0-WELLDEFINEDNESS.md` §6 hoped for. It is instead a third
  independent instance of the Part 1 finding: once a system can express
  "this computation halts", extra strength buys no new growth class.
- **`RAYO-GROWTH-RATE.md`** §5 and line ~206 ("Boolos `= ε₀`"): same
  correction. The comparison with Rayo gets sharper, since the true contrast
  is Busy-Beaver class against beyond-arithmetical.
- **`BoolosBig_PA_dominates`** stays correct. It is a true but weak corollary
  of Theorem 1.

The resulting picture is three tiers, each closed off from the next by a
classical wall:

| tier | examples in this project | wall above it |
|---|---|---|
| computable ladders | BMS, System F / CoC | computability (halting problem) |
| Busy-Beaver class | Turing machines, BLC, provable naming in any theory | definability of truth (Tarski) |
| truth-based | Rayo | needs MK-strength commitment (R0) |

## 8. Mechanization plan

**Done 2026-11-24** for the target below, by the unary-numeral route
described at the end of this section: `RayoBoolos/Minimization.lean`. Item
4 (binary numerals, for the logarithmic bound) followed in
`RayoBoolos/Binary.lean`. What remains is Theorems 2 and 3.

Target, in `rayo-lean-boolos/`, replacing the `ProvablyTotal` hypothesis:

```
theorem BoolosBig_PA_dominates_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ N, ∀ m > N, BoolosBig_PA m ≥ f m
```

Pieces, with what already exists:

1. Σ₁ graph of a computable function: `computable_iff_sigma1` in
   `Foundation/FirstOrder/Arithmetic/R0/Representation.lean`.
2. Σ₁-completeness: `sigma_one_completeness` (`R0/Basic.lean`), already used
   in `Domination.lean`.
3. The minimization wrapper `μ` and its provable uniqueness: new, but it is
   pure order reasoning and can be done semantically through
   `Arithmetic.complete`, the technique `Domination.lean` already uses.
4. `bin(n)` with `tSize (bin n) ≤ 6 * Nat.log2 (n+2)` and value `n`: new,
   elementary.
5. Size bookkeeping: `fSize_rew_le` already exists.
6. Assembly: as in `BoolosBig_PA_dominates`, without `Nat.sqrt`.

Item 4 can be skipped for a first version that keeps unary numerals: the
minimization lemma alone removes both `ProvablyTotal` and `Monotone`, if
combined with pre-inflation by `f'(n) := max_{i ≤ n²} f(i)`, which is
computable and monotone. Binary numerals are needed only for the sharper `log` bound and
for Theorem 2's linear rescaling.

Theorems 2 and 3 need a formalized universal machine and proof enumeration
and are a larger job; Theorem 1 with its non-computability corollary already
carries the correction.

## 9. Things to check

- The Σ₁-completeness step applies to a sentence containing the closed term
  `bin(n)`, not a numeral. Standard Σ₁-completeness covers closed terms, but
  the Lean lemma should be checked for the form it takes.
- (A3) as stated is more than is needed (one of the two bounds compared is
  always a standard number once `μₙ(k̄)` is in hand), so the result probably
  extends to Robinson's `Q`. Not needed for PA.
- Theorem 3's `n log n` depends on the exact size measure; the constant
  factor was not computed.
- Whether the arithmetical-truth analogues (naming by truth of Σ_k formulas
  in `ℕ`) give the expected oracle Busy-Beaver levels, and so a ladder of
  intermediate tiers between this one and Rayo. Expected, not worked out.
