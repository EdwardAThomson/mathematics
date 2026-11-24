# The largest number a theory can name in n symbols

*Report, 2026-11-24.* The literature check is summarized in §10; the
full survey is [`LITERATURE-SURVEY.md`](LITERATURE-SURVEY.md).

Every statement is tagged:

- **[Lean]** machine-checked in Lean 4 against Mathlib and
  FormalizedFormalLogic/Foundation, with no `sorry` and no axioms beyond
  `propext`, `Classical.choice`, `Quot.sound`;
- **[paper]** proved in this report, not machine-checked.

---

## 1. Summary

Fix a theory `T` of arithmetic. Say a formula `φ(x)` **names** the number
`k` in `T` when `T` proves `∀x (φ(x) ↔ x = k)`. Define

    Big_T(n) = the largest number named in T by a formula of at most n symbols.

This is the provability version of "the largest number definable in n
symbols". Unlike Rayo's function, it needs no notion of truth for the
whole language: whether `φ` names `k` is a question about the existence of
a proof.

A natural guess is that `Big_T` reflects the strength of `T`, so that for
Peano Arithmetic it grows about as fast as the fastest function PA can
prove total (the ε₀ level of the fast-growing hierarchy), and that
stronger theories give essentially faster functions. An earlier version of
this project made that guess. It is wrong. The results:

1. **`Big_T` eventually dominates every computable function**, for every
   consistent theory `T` containing a small base theory. The threshold
   does not depend on `T`. (Theorems 2, 3) **[Lean]**
2. **Values of computable functions are cheap to name**: `f(n)` is named
   by a formula of `C_f + 6·log₂ n` symbols, with `C_f` independent of
   `T`. (Theorem 2) **[Lean]**
3. **`Big_T` is not computable.** (Theorem 3) **[Lean]**
4. **`Big_T` dominates a Busy Beaver function** after a logarithmic
   rescaling: a halting program with code number `N` outputs, and runs
   for, at most `Big_T(C + 6·log₂ N)`. (Theorem 5) **[Lean]**
5. **`Big_T` is dominated by a Busy Beaver function** after a rescaling
   of the argument, when `T` is computably axiomatized. (Theorem 6)
   **[Lean]** with a rescaling that is fixed but not bounded explicitly;
   **[paper]** for the `n log n` form.
6. Consequently **the choice of axioms changes `Big_T` only by a rescaling
   of its argument**. PA, a fragment with no induction at all, and ZFC all
   give the same growth class. (Corollary 7) **[Lean]**, same proviso.
7. **`T` cannot prove any exact value of `Big_T`**, although it proves
   every true lower bound. (Theorem 8) **[paper]**
8. **No naming scheme is final.** In an abstract setting: a scheme cannot
   name "its own record at budget n, plus one" within budget n, and any
   extension that can do so cheaply has a strictly larger record.
   (Theorem 9) **[Lean]**

The distinction that explains the wrong guess: ε₀ measures which functions
PA can prove **total**, a statement about all inputs at once. Naming asks
only that `T` confirm **one value at a time**, and for that a finished
computation is enough.

## 2. Setting

The language is that of ordered semirings, `0, 1, +, ·, =, <`. The base
theory is `PA⁻`: the finitely many axioms of discretely ordered
semirings, with no induction.

**Size.** `|t|` and `|φ|` count nodes of the syntax tree: one for each
variable occurrence, constant, function symbol, relation symbol,
connective and quantifier. (Lean: `tSize`, `fSize`.) There are finitely
many formulas of a given size with one free variable
(`formsUpTo_finite`). **[Lean]**

**Naming.** `φ` names `k` in `T` when `T ⊢ ∀x (φ(x) ↔ x = k̄)`, where `k̄`
is the numeral of `k`. (Lean: `NamesIn T φ k`.)

**Theorem 1 (well-definedness). [Lean]** Let `T ⊇ PA⁻` be consistent.
Each formula names at most one number in `T`, so the set of numbers named
by formulas of size at most `n` is finite and `Big_T(n)` is well defined.
It is monotone in `n`, and monotone in `T`: if `T ⊆ U` then
`Big_T(n) ≤ Big_U(n)`.

*Proof.* If `φ` names `k₁` and `k₂` then in every model of `T` the
numerals `k̄₁` and `k̄₂` denote the same element. In models of `PA⁻`
distinct numerals denote distinct elements. So if `k₁ ≠ k₂` then `T` has
no models, and by completeness `T ⊢ ⊥`. Only consistency is used, not
truth of `T` in the standard model. The rest is finiteness. ∎

Lean: `NamesIn.unique`, `namedValuesIn_finite`, `BoolosBigIn`,
`BoolosBigIn_mono`, `BoolosBigIn_mono_theory` (`AnyTheory.lean`). For
`T = PA` the function coincides with the project's earlier `BoolosBig_PA`
(`BoolosBigIn_PA`).

## 3. The key lemma: naming by bounded search

Two standard facts are used.

- **Σ₁-completeness.** `PA⁻` proves every Σ₁ sentence that is true in the
  standard model. (Foundation: `sigma_one_completeness_iff_param`.)
- **Σ₁ graphs.** Every partial recursive function `g` has a Σ₁ formula
  `θ(y, x)` with `ℕ ⊨ θ(v, n)` exactly when `g(n) = v`. (Foundation:
  `codeOfPartrec'`.)

Σ₁-completeness lets `T` *confirm* `θ(v̄, n̄)` when it is true. It does not
let `T` prove that `v` is the *only* `y` with `θ(y, n̄)`: that is a Π₁
fact, and a nonstandard model may contain other witnesses. The lemma
wraps `θ` so that uniqueness becomes provable for free.

**Bounding.** For a formula `θ`, let `θ^s` be `θ` with every unbounded
existential quantifier `∃z` replaced by `∃z ≤ s`, for a fresh variable
`s`. (Lean: `bd`.) In the standard model, for Σ₁ formulas `θ`:

- `θ^s → θ` (`of_bd`);
- `θ^s → θ^{s'}` whenever `s ≤ s'` (`bd_mono`);
- if `θ` holds then `θ^s` holds for some `s` (`exists_bd`);
- `θ^s` is Δ₀ (`hierarchy_bd`). **[Lean]**

**The wrapper.** Define

    M_θ(y, x)  :≡  ∃s [ y ≤ s ∧ θ^s(y, x)
                        ∧ ∀s' ≤ s ∀y' ≤ s' ( θ^{s'}(y', x) → y' = y ) ].

In words: there is a search bound `s` at which `y` shows up, and
everything that shows up at or below that bound is equal to `y`. (Lean:
`minGraph`.) `M_θ` is Σ₁ (`minGraph_sigma1`).

**Lemma A (uniqueness is free). [Lean]** In every model of `PA⁻`, if
`M_θ(y, x)` and `M_θ(y', x)` then `y = y'`.

*Proof.* Let `s`, `s'` be the two bounds. The order is total, so say
`s ≤ s'`. The second witness's universal clause, applied at the bound `s`
to the value `y` (which satisfies `y ≤ s` and `θ^s(y, x)`), gives
`y = y'`. ∎ (`minGraph_unique`.)

**Lemma B (truth at a point). [Lean]** Suppose that in the standard model
`θ(v, n)` holds and `v` is the only `y` with `θ(y, n)`. Then
`ℕ ⊨ M_θ(v, n)`.

*Proof.* Pick `s₀` with `θ^{s₀}(v, n)` and take `s = max(s₀, v)`. Any
`y'` with `θ^{s'}(y', n)` satisfies `θ(y', n)`, hence `y' = v`. ∎
(`minGraph_true_at`.)

**Lemma C (naming at a point). [Lean]** Under the hypothesis of Lemma B,
the formula `M_θ(x, n̄)` names `v` in `PA⁻`, hence in every `T ⊇ PA⁻`.

*Proof.* `M_θ(v̄, n̄)` is a true Σ₁ sentence, so `PA⁻` proves it. In any
model of `PA⁻`, if `M_θ(x, n̄)` then `x = v̄` by Lemma A; conversely
`M_θ(v̄, n̄)` holds. By completeness `PA⁻ ⊢ ∀x (M_θ(x, n̄) ↔ x = v̄)`. ∎
(`minGraph_namesIn_partial`.)

Nothing here asks `T` to prove that a value exists for *every* input.
That is the whole difference from arguments that go through provable
totality.

**Short numerals. [Lean]** The standard numeral for `n` has size about
`2n`. Define instead `bin(0) = 0`, `bin(1) = 1`,
`bin(2m) = (1+1)·bin(m)`, `bin(2m+1) = (1+1)·bin(m) + 1`. Then
`|bin(n)| ≤ 6·log₂ n + 1` (`tSize_bin_le`), and `bin(n)` denotes `n` in
every model of `PA⁻` (`val_bin`). Put

    L_{θ,n}(y)  :≡  ∃x ( x = bin(n) ∧ M_θ(y, x) ).

Then `|L_{θ,n}| ≤ |M_θ| + 5 + 6·log₂ n` (`fSize_logName_le`), and
`L_{θ,n}` names whatever `M_θ(·, n̄)` names (`logName_namesIn_partial`).

## 4. Main results

**Theorem 2 (logarithmic naming). [Lean]** Let `g` be a partial recursive
function. There is a constant `C` such that for every consistent
`T ⊇ PA⁻`, every `n`, and every `v` with `g(n) = v`,

    v ≤ Big_T(C + 6·log₂ n).

In fact `v` itself is named by a formula of that size. `C` depends on `g`
only, not on `T`.

*Proof.* Take a Σ₁ graph `θ` for `g`. Values of `g` are unique, so Lemma C
applies at every point where `g` is defined, and `L_{θ,n}` has the stated
size with `C = |M_θ| + 5`. ∎ (`BoolosBigIn_partrec_bound`; for total `g`,
`BoolosBigIn_log_bound`.)

**Theorem 3 (domination, non-computability). [Lean]** For every
computable `f` there is `N` such that for every consistent `T ⊇ PA⁻` and
every `m > N`, `f(m) ≤ Big_T(m)`. Hence `Big_T` is not computable.

*Proof.* Apply Theorem 2 to the running maximum of `f` and use
`C + 6·log₂ m ≤ m` for `m > 2C + 64`, with monotonicity of `Big_T`. If
`Big_T` were computable, apply the first part to `Big_T + 1`. ∎
(`BoolosBigIn_dominates_computable`, `BoolosBigIn_not_computable`.)

**Remark 4.** Theorem 2 is much stronger than domination. Read backwards
it says `Big_T(m) ≥ f(2^⌊(m − C)/6⌋)` for every computable `f`.

## 5. The Busy Beaver sandwich

Take any standard enumeration of programs; the Lean development uses
Mathlib's `Nat.Partrec.Code` and its numbering. Let

- `BB(N)` = the largest output of a program with code number at most `N`
  that halts on input 0;
- `BBtime(N)` = the largest halting time of such a program.

A program with code number `N` is `log₂ N` bits long, so these are Busy
Beaver functions indexed by `2^(program length)`.

**Theorem 5 (lower bound). [Lean]** There is a constant `C` such that for
every consistent `T ⊇ PA⁻` and every `N`,

    BB(N) ≤ Big_T(C + 6·log₂ N),     BBtime(N) ≤ Big_T(C + 6·log₂ N).

*Proof.* "The output of program `e` on input 0" and "the halting time of
program `e` on input 0" are partial recursive functions of `e`. Apply
Theorem 2 and take the maximum over `e ≤ N`, using monotonicity. ∎
(`BB_le_BoolosBigIn`, `BBtime_le_BoolosBigIn`.)

In terms of program length `ℓ`: a halting program of `ℓ` bits produces a
number that every such theory can name in `C + 6ℓ` symbols.

**Theorem 6 (upper bound).** Let `T ⊇ PA⁻` be consistent and computably
axiomatized.

- (a) **[Lean]** There is a partial recursive function `g_T` such that
  whenever `φ` names `k` in `T`, `g_T(⌜N_φ⌝) = k`, where `N_φ(y)` is the
  formula `∀x (φ(x) ↔ x = y)` and `⌜·⌝` is the Gödel number.
  (`exists_search`.)
- (b) **[paper]** There are constants `c` (absolute) and `c_T` such that
  `Big_T(n)` is at most the largest output of any halting program of at
  most `c·n·log₂ n + c_T` bits.

*Proof.* (a) The relation "`x` codes a formula `N` and `T ⊢ N(k̄)`" is
Σ₁ in `(x, k)`, hence recursively enumerable; a partial recursive
function selects a witness `k` whenever one exists (`re_select`), and by
Theorem 1 the witness is the number named.

(b) Let `P_T` be the program that reads a formula `φ`, enumerates
proofs of `T`, and halts with output `k` when it finds a proof of
`∀x (φ(x) ↔ x = k̄)`. By Theorem 1 the output is determined. If `φ` names
`k` then `P_T` on `φ` halts with `k`. A formula of size `n` is a tree of
`n` nodes whose labels are symbols or variable indices below `n`, so it
has a description of `c·n·log₂ n` bits. Hard-wiring that description
into `P_T` gives a program of `c·n·log₂ n + c_T` bits that outputs
`k`. ∎

**Corollary 7 (the axioms do not matter).** Let `T ⊇ PA⁻` be consistent
and computably axiomatized, and let `U ⊇ PA⁻` be consistent.

- (a) **[Lean]** There is a constant `C` with

      Big_T(n) ≤ Big_U(C + 6·log₂ M(n))     for all n,

  where `M(n)` is the largest Gödel number of `N_φ` over formulas `φ` of
  size at most `n`. `M` depends on neither theory.
  (`BoolosBigIn_le_any`; for `T = PA`, `BoolosBig_PA_le_any`.)
- (b) **[paper]** With an efficient encoding of formulas,
  `log₂ M(n) ≤ c·n·log₂ n`, so `Big_T(n) ≤ Big_U(a·n·log₂ n + b)`.

*Proof.* (a) Theorem 6(a) for `T`, then Theorem 2 for `U` applied to
`g_T`. (b) Theorem 6(b), then Theorem 5. ∎

The Lean statement (a) does not bound `M(n)`. The Gödel numbering of the
underlying library uses nested pairing, for which `log₂ M(n)` is larger
than `n log n`. What (a) establishes is that one fixed rescaling of the
argument, the same for all theories, absorbs any difference in axioms.

So strengthening the axioms from `PA⁻` to PA to ZFC does make more
formulas name numbers, and `Big` does increase pointwise (Theorem 1), but
only by an amount that a slightly larger symbol budget recovers in the
weakest theory.

## 6. What the theory can know about its own function

**Theorem 8. [paper]** Let `T ⊇ IΣ₁` be consistent and computably
axiomatized, and let `n ≥ 1`. Formalize "`Big_T(n) = k`" in arithmetic in
the natural way. Then:

- (a) for every true inequality `Big_T(n) ≥ k`, `T` proves it;
- (b) `T` does not prove `Big_T(n) = k` for any `k`.

*Proof.* (a) "`Big_T(n) ≥ k`" asserts that some formula of size at most
`n` provably names some number `≥ k`. That is a Σ₁ sentence, and true Σ₁
sentences are provable.

(b) "`Big_T(n) = k`" implies, for a fixed formula `φ₀` of size 1, that
`T` does not prove that `φ₀` names `k + 1`. Inside `T`, the
unprovability of any one sentence implies the consistency of `T`. So a
proof of "`Big_T(n) = k`" in `T` yields a proof of `Con(T)` in `T`,
contradicting Gödel's second incompleteness theorem. ∎

The function is defined entirely by what `T` proves, and `T` can
determine none of its values.

## 7. No scheme is final

The preceding sections fix one notion of naming. This section is about
changing it. The setting is deliberately bare.

A **scheme** is a set of expressions, each with a size, finitely many of
each size, and a relation "expression `e` names number `k`" under which
each expression names at most one number. Its **record** at budget `n` is
the largest number named by an expression of size at most `n`.

**Theorem 9. [Lean]**

- (a) Every scheme has a unique record at each budget, monotone in the
  budget.
- (b) (**Berry**) If an expression of a scheme names its record at
  budget `n` plus one, that expression has size greater than `n`.
- (c) If a scheme `S'` extends `S` (every `S`-expression is an
  `S'`-expression of the same size naming the same number) and `S'` has
  an expression of size at most `n` naming the `S`-record at budget `n`
  plus one, then the `S'`-record at `n` is strictly larger than the
  `S`-record at `n`.

Lean: `exists_isBN_of_finite`, `IsBN.unique`, `IsBN.mono`,
`size_gt_of_names_succ_record`, `record_lt_of_names_succ_record`
(`Rayo/NoTop.lean`, Lean core only), with a toy pair of schemes
satisfying (c).

Part (b) says no scheme can describe its own record cheaply. Part (c)
says any scheme that can describe another's record cheaply beats it. A
language with a truth predicate for a smaller language is the standard
way to meet the hypothesis of (c): "the largest number named in `S` by an
expression of size at most `n`, plus one" becomes expressible with `n`
written in binary. That step is classical (Tarski) and is not
machine-checked here.

**Where the schemes sit. [classical unless tagged]**

| rung | "names" may refer to | Big(n) |
|---|---|---|
| 0 | a fixed terminating process | a computable function |
| 1 | halting, or provability in any reasonable theory | Busy Beaver class (§§4, 5) |
| k | halting with k−1 nested halting oracles | k-th order Busy Beaver |
| ω | truth in arithmetic | beats every rung k |
| … | truth in richer languages | … |
| Rayo | truth in first-order set theory | Rayo's function |

Rung 1 is the content of this report: Turing machines, lambda calculus
and provable naming in every consistent computably axiomatized theory
share it. There is no ε₀ rung between rung 0 and rung 1 on which provable
naming in PA sits.

## 8. Reading the results as description complexity

Let `D_T(k)` be the size of the smallest formula naming `k` in `T`. Then
`Big_T(n)` is the largest `k` with `D_T(k) ≤ n`, exactly as a Busy Beaver
function is the largest `k` of Kolmogorov complexity at most `n`. In this
language:

- Theorem 2: `D_T(g(n)) ≤ C_g + 6·log₂ n`, the analogue of
  `K(g(n)) ≤ K(n) + C_g`. **[Lean]**
- Theorem 5: `D_T(k) ≤ C + 6·K'(k)`, where `K'(k)` is the bit length of
  the smallest code number of a program printing `k`. **[Lean]**
- Theorem 6: `K(k) ≤ c·D_T(k)·log D_T(k) + c_T`. **[paper]**

So provability complexity and Kolmogorov complexity are the same measure
up to a constant factor and a logarithm, for every admissible `T`.

## 9. Machine-checked statements and how to reproduce

| result | Lean name | file |
|---|---|---|
| Theorem 1 | `NamesIn.unique`, `namedValuesIn_finite`, `BoolosBigIn_mono`, `BoolosBigIn_mono_theory`, `BoolosBigIn_PA` | `RayoBoolos/AnyTheory.lean` |
| Lemmas A to C | `minGraph_unique`, `minGraph_true_at`, `minGraph_namesIn_partial` | `RayoBoolos/Minimization.lean`, `RayoBoolos/BusyBeaver.lean` |
| Short numerals | `tSize_bin_le`, `val_bin`, `fSize_logName_le` | `RayoBoolos/Binary.lean` |
| Theorem 2 | `BoolosBigIn_partrec_bound`, `BoolosBigIn_log_bound` | `RayoBoolos/BusyBeaver.lean`, `RayoBoolos/AnyTheory.lean` |
| Theorem 3 | `BoolosBigIn_dominates_computable`, `BoolosBigIn_not_computable` | `RayoBoolos/AnyTheory.lean` |
| Theorem 5 | `BB_le_BoolosBigIn`, `BBtime_le_BoolosBigIn` | `RayoBoolos/BusyBeaver.lean` |
| Theorem 6(a), Corollary 7(a) | `exists_search`, `BoolosBigIn_le_any`, `BoolosBig_PA_le_any` | `RayoBoolos/UpperBound.lean` |
| Theorem 9 | see §7 | `rayo-lean/Rayo/NoTop.lean` |

All `RayoBoolos` files are under `large-numbers/rayo-lean-boolos/`.
Toolchain: Lean 4 `v4.32.2`, with Mathlib and Foundation pinned by
`lake-manifest.json`. To check: run `lake build` in
`large-numbers/rayo-lean-boolos/` (1260 jobs) and in
`large-numbers/rayo-lean/`. Each file ends with `#print axioms` for its
headline theorems.

The exact Lean statement of Theorem 2:

```lean
theorem BoolosBigIn_partrec_bound {g : ℕ →. ℕ} (hg : Partrec g) :
    ∃ C, ∀ (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T],
      ∀ n v, v ∈ g n → v ≤ BoolosBigIn T (C + 6 * Nat.log2 n)
```

## 10. Related work, and what is claimed

The full survey, with a bibliography and the reading status of each
source, is `LITERATURE-SURVEY.md`. In brief:

- **The notion of naming is Boolos's.** In "A new proof of the Gödel
  incompleteness theorem" (1989) a formula `F(x)` names `n` when
  `∀x (F(x) ↔ x = n̄)` is a theorem. Boolos used it for a Berry-paradox
  proof of incompleteness. `Big_T` is the largest number Boolos-named by
  a formula of at most `n` symbols.
- **Theorem 2 is classical in substance.** It is the strong
  representability of computable functions in a weak arithmetic by a
  least-witness formula (Tarski, Mostowski and Robinson, *Undecidable
  Theories*, 1953), combined with short numerals, which Boolos also
  uses. The program-size analogue `K(f(n)) ≤ K(n) + c_f` is textbook.
- **The Busy Beaver sandwich and its independence of the axioms**
  (Theorems 5, 6, Corollary 7) follow from standard facts in a few
  lines. We did not find them stated for the naming function, and expect
  they are known to specialists. Closely related: Chaitin (1974, 1987);
  Chaitin, Arslanov and Calude (1995), who prove the program-size form
  of Theorem 5; Lafitte, "Busy beavers gone wild" (2009); Lacerda (2014);
  and Simmons, "Naming the largest number" (arXiv:1809.08676), who
  compares naming strategies across theories by proof length.
- **Theorem 8** is an immediate corollary of the standard fact that a
  consistent theory proves no instance of its own unprovability. We did
  not find it applied to the naming function. It is offered as an
  observation. Related: Aaronson, "The Busy Beaver Frontier" (2020),
  Prop. 4; Kritchman and Raz (2010); Kikuchi (1997).
- **Theorem 9 and the table of rungs** restate Berry's paradox and
  Tarski's theorem; oracle Busy Beavers are in Aaronson (2020) §3.

**What is claimed.** Not new theorems. The contribution is:

1. machine-checked proofs of Theorems 1, 2, 3, 5, 6(a), Corollary 7(a)
   and Theorem 9, with explicit constants and a base theory with no
   induction (we are not aware of a prior formalization of a Boolos-style
   naming function or of its growth);
2. the wrapper of Lemma A, which obtains provable uniqueness from the
   order axioms and a semantic completeness argument;
3. a worked correction of the tempting identification of "what PA can
   name" with "what PA can prove total".

**A caution.** The constants `C` and `c_T` above are not measures of the
strength of `T`. They depend on the coding (see Raatikainen, "On
interpreting Chaitin's incompleteness theorem", 1998). The claim here is
only about growth class.

**Gaps in the survey.** Not yet read in full: Kikuchi, Kurahashi and
Sakai (2012); the later sections of Simmons; Googology Wiki pages on
provability-based variants. Some standard references are cited from
memory and need checking against the publications.

## 11. Open items

- Machine-check the quantitative forms Theorem 6(b) and Corollary 7(b),
  which need an efficient encoding of formulas and a bound on its size.
- Machine-check Theorem 8.
- Exhibit one concrete pair of languages meeting the hypothesis of
  Theorem 9(c), for example arithmetic and arithmetic with a halting
  predicate.
- State and prove the rung-k analogue of the sandwich.
- Sharpen the constants: the `6` in Theorem 2 comes from the term
  encoding of binary numerals and is not optimal.
