# The largest number a theory can name in n symbols

**Report, 2026-11-24.** The literature check is
summarized in §10; the full survey is `LITERATURE-SURVEY.md`.

Every statement is tagged:

- **[Lean]** machine-checked in Lean 4 against Mathlib and
  FormalizedFormalLogic/Foundation, with no `sorry` and no axioms beyond
  `propext`, `Classical.choice`, `Quot.sound`;
- **[paper]** proved in this report or in the note it cites, not
  machine-checked.

§9 lists each machine-checked statement beside its Lean name, and records
the places where the formal statement is narrower or differently phrased
than the prose.

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
   of the argument by `O(n log n)`, when `T` is computably axiomatized.
   (Theorem 6) **[Lean]**: `Big_T(n) ≤ BB(2^(C·(n+1)·(log₂(n+1)+6)))`, so
   every number `T` names in `n` symbols is printed by a program of
   `O(n log n)` bits.
6. Consequently **the choice of axioms changes `Big_T` only by a rescaling
   of its argument**. PA, a fragment with no induction at all, and ZFC all
   give the same growth class: `Big_T(n) ≤ Big_U(C + 240·(n+1)·(log₂(n+1)+6))`.
   (Corollary 7) **[Lean]**
7. **`T` cannot prove any exact value of `Big_T`**, nor even any upper
   bound, although it proves every true lower bound. (Theorem 8) **[Lean]**
8. **No naming scheme is final.** In an abstract setting: a scheme cannot
   name "its own record at budget n, plus one" within budget n, and any
   extension that can do so cheaply has a strictly larger record.
   (Theorem 9) **[Lean]**
9. **The rungs between Busy Beaver and arithmetic truth are located.**
   Naming by *truth* of arithmetic formulas with `k` "for all" blocks
   matches the Busy Beaver function for machines with the `k`-th iterated
   halting oracle. This proves a 2010 guess of Aaronson. (Theorem 10)
   **[paper]** for all `k`; the bottom level and the first step up are
   **[Lean]**.
10. **One statement covers all of these.** For any consistent theory,
    computably axiomatized or not, provable naming is the Busy Beaver
    function over the oracles the theory can decide. (Theorem 11)
    **[paper]**

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
connective and quantifier. (Lean: `tSize`, `fSize`.) Formulas are in
negation normal form, as in the underlying library: the connectives are
`∧` and `∨`, negation is applied only to atomic formulas and a negated
atom costs the same as an atom, and `→` and `↔` are abbreviations that are
counted after expansion (so `A ↔ B` counts `A` and `B` twice). Variables
are de Bruijn indices and each occurrence costs one. Every bound in this
report is stated for this size measure; another reasonable measure changes
the constants. There are finitely
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
Beaver functions indexed by `2^(program length)`. Two points about the
formal definitions. "Halting time" is the least step bound at which
Mathlib's bounded evaluator `Code.evaln` returns a result, which is that
library's notion of running time and not a count of Turing machine steps.
And the numbering is Mathlib's numbering of `Nat.Partrec.Code`, in which
some small programs have large code numbers (see Theorem 6(b)).

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
- (b) There are constants `c` (absolute) and `c_T` such that
  `Big_T(n)` is at most the largest output of any halting program of at
  most `c·n·log₂ n + c_T` bits.
  - **[Lean]** in the form: there is one partial recursive function
    `g_T` such that every number `T` names with a formula of size at most
    `n` is an output of `g_T` on some input `m` with
    `log₂ m < 4·(2n+10)·(log₂(2n+26)+1)` (`exists_compact_search`). The
    program `g_T` is fixed, so its size is `c_T`, and the input carries
    the `O(n log n)` bits.
  - **[Lean]** with the input built into the program, so that the
    bound is on the *code number* in Mathlib's numbering of
    `Nat.Partrec.Code`, the numbering the Lean `BB` uses: there is `C`
    with

        Big_T(n) ≤ BB(2^(C·(n+1)·(log₂(n+1)+6)))     for all n

    (`BoolosBigIn_le_BB_nlogn'`; for `T = PA`, `BoolosBig_PA_le_BB_nlogn`).
    This step needs care because Mathlib's `Code.const m` writes `m` in
    unary, as `m` nested compositions, and each nesting roughly squares
    the code number, so "output `m`" written that way has a code number
    near `2^(2^m)`. `RayoBoolos/HardWire.lean` instead writes `m` as a
    balanced binary tree of its bits (`binCode`): a tree of depth `j`
    holds `2^j` bits and has a code number below `2^(8·2^j)`
    (`encode_binCode_le`), so constants cost a constant times their bit
    length. A fixed primitive recursive decoder turns the tree back into
    `m` (`binDecode_binTree`, `primrec_binDecode`), and
    `exists_hardwire` gives, for every partial recursive `f`, a constant
    `A` such that an input `m` of fewer than `L` bits can be built into a
    program for `f(m)` with code number below `2^(A·L)`.

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

In Lean (`RayoBoolos/CompactCode.lean`) the description is the formula in
Polish notation, one token per symbol (`fSize φ` tokens, each below
`b = 15 + fSize φ`), packed as base-`b` digits together with `b` and the
length. A stack machine turns the token list back into `Foundation`'s
Gödel number; it is proved primitive recursive (`primrec_compactDecode`)
and correct (`compactDecode_compactCode`). The code of the naming
template of a formula of size `n` then has fewer than
`4·(2n+10)·(log₂(2n+26)+1)` bits (`log2_compact_template_lt`).
`exists_hardwire` then builds that code into the search program.

**The sandwich in one statement. [Lean]** For a consistent, computably
axiomatized `T ⊇ PA⁻` there is one constant `C` with, for all `n` and `s`,

    BB(2^s) ≤ Big_T(C + 6·s),     Big_T(n) ≤ BB(2^(C·(n+1)·(log₂(n+1)+6))).

In words: programs of `s` bits are beaten by formulas of `C + 6s`
symbols, and formulas of `n` symbols are beaten by programs of
`O(n log n)` bits. (`busy_beaver_sandwich`.)

**Corollary 7 (the axioms do not matter).** Let `T ⊇ PA⁻` be consistent
and computably axiomatized, and let `U ⊇ PA⁻` be consistent.

- (a) **[Lean]** There is a constant `C` with

      Big_T(n) ≤ Big_U(C + 6·log₂ M(n))     for all n,

  where `M(n)` is the largest Gödel number of `N_φ` over formulas `φ` of
  size at most `n`. `M` depends on neither theory.
  (`BoolosBigIn_le_any`; for `T = PA`, `BoolosBig_PA_le_any`.)
- (b) **[Lean]** With the compact encoding of formulas of Theorem 6(b),
  there is a constant `C` (depending on `T` only through its proof-search
  program) such that for every consistent `U ⊇ PA⁻`, computably
  axiomatized or not, and every `n`,

      Big_T(n) ≤ Big_U(C + 240·(n+1)·(log₂(n+1) + 6)).

  (`BoolosBigIn_le_any_nlogn'`; the sharper `C + 6·nlogBound(n)` with
  `nlogBound(n) = 4·(2n+10)·(log₂(2n+26)+1)` is `BoolosBigIn_le_any_nlogn`;
  for `T = PA`, `BoolosBig_PA_le_any_nlogn`.)

*Proof.* (a) Theorem 6(a) for `T`, then Theorem 2 for `U` applied to
`g_T`. (b) Theorem 2 for `U` applied to the function `g_T` of Theorem
6(b), whose inputs have `O(n log n)` bits. ∎

In (a), `M(n)` is not bounded: the Gödel numbering of the underlying
library uses nested pairing, for which `log₂ M(n)` is far larger than
`n log n`. (b) replaces that numbering by the compact code, which is why
it needs no hard-wiring step.

So strengthening the axioms from `PA⁻` to PA to ZFC does make more
formulas name numbers, and `Big` does increase pointwise (Theorem 1), but
only by an amount that a slightly larger symbol budget recovers in the
weakest theory.

## 6. What the theory can know about its own function

**Theorem 8. [Lean]** Let `T ⊇ IΣ₁` be consistent and computably
axiomatized, and let `n ≥ 1`. Formalize "`Big_T(n) = k`" in arithmetic in
the natural way. Then:

- (a) whenever some formula of size at most `n` names a number `≥ k`,
  `T` proves "`Big_T(n) ≥ k`" (this is every true lower bound, except
  the empty case `k = 0` at budgets too small to name anything);
- (b) `T` does not prove `Big_T(n) = k` for any `k`. In fact `T` proves
  no upper bound `Big_T(n) ≤ k` at all.

**The formalization in Lean** (`RayoBoolos/NoExactValue.lean`). The
formulas of size at most `n` are finitely many and are listed outside the
theory, so size is not arithmetized. For each such `φ`, with `N_φ(y)` the
formula `∀x (φ(x) ↔ x = y)`:

- "`Big_T(n) ≤ k`" (`bigLe T n k`) is the conjunction over these `φ` of
  `∀m ∀y (y = ⌜N_φ(m̄)⌝ ∧ Prov_T(y) → m ≤ k)`, where `y = ⌜N_φ(m̄)⌝` is
  `Foundation`'s Σ₁ graph of substituting the numeral of `m` into the
  code of `N_φ`, and `Prov_T` is its standard provability predicate;
- "`Big_T(n) ≥ k`" (`bigGe T n k`) is the disjunction over these `φ` of
  `∃m ∃y (k ≤ m ∧ y = ⌜N_φ(m̄)⌝ ∧ Prov_T(y))`, a Σ₁ sentence;
- "`Big_T(n) = k`" (`bigEq T n k`) is their conjunction.

These mean what they should: `bigLe T n k` is true in ℕ exactly when
`Big_T(n) ≤ k` (`bigLe_true_iff`), and `bigGe T n k` is true exactly when
some formula of size at most `n` names a number `≥ k` (`bigGe_true_iff`).
The theorems are `provable_bigGe` (a), `not_provable_bigLe` and
`not_provable_bigEq` (b). Part (b) uses only one conjunct of `bigLe`, so
any formalization that provably in `T` implies "the fixed formula `⊤`
names no number above `k`" is covered as well.

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
satisfying (c). The Lean form of (c) is slightly more general than the
prose: it does not use that `S'` extends `S`, and it concludes that the
`S'`-record at the budget of the naming expression exceeds the `S`-record
at `n`; the statement above follows by monotonicity (a).

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
| 1 | halting; provability in any reasonable theory; truth of Σ₁ formulas | Busy Beaver class (§§4, 5) |
| k+1 | truth of formulas with k "for all" blocks (Π_k or Σ_{k+1}) | Busy Beaver with the k-th halting oracle (Theorem 10) |
| ω | truth in arithmetic | beats every rung k; a limit, not an oracle rung (Theorem 11(c)) |
| above ω | truth of formulas that also quantify over sets of numbers, level by level | one rung per level; the first (`Σ¹₁` or `Π¹₁`) is Busy Beaver over hyperarithmetic oracles and beats rung ω **[paper]**, `SECOND-ORDER-RUNGS.md` |
| … | truth in richer languages still | … |
| Rayo | truth in first-order set theory | Rayo's function |

**Theorem 10 (the middle rungs).** Let `Truth_Γ(n)` be the largest number
`m` such that some formula of class `Γ` and size at most `n` is true of `m`
and of nothing else, in the standard model. The classes are the liberal
ones of the underlying library: bounded quantifiers are free, and
`Σ_{k+1}` contains `Π_k`.

- (a) **[Lean]** `BB(N) ≤ Truth_{Σ₁}(C + 6·log₂ N)`, and
  `Truth_{Σ₁}(n) ≤ BB(h(n))` for a fixed function `h`. So naming by Σ₁
  truth is Busy Beaver class, like provable naming.
  (`BB_le_TruthBig_sigma1`, `TruthBig_sigma1_le_BB`.) With `h` made
  explicit in the input form of Theorem 6(b): one fixed program outputs
  every value of `Truth_{Σ₁}(n)` on an input of fewer than
  `4·n·(log₂(n+16)+1)` bits (`TruthBig_sigma1_compact`), and with the
  input built in, `Truth_{Σ₁}(n) ≤ BB(2^(C·(n+1)·(log₂(n+16)+1)))`
  (`TruthBig_sigma1_le_BB_nlogn`).
- (b) **[Lean]** `BB(N) < Truth_{Σ₂}(C + 6·log₂ N)`: one "for all" block
  names "one more than the Busy Beaver value". This is a concrete instance
  of Theorem 9(c). (`BB_lt_TruthBig_sigma2`, `sigma2_record_gt_sigma1`.)
- (c) **[paper]** For every `k`, `Truth_{Π_k}`, `Truth_{Σ_{k+1}}` and the
  Busy Beaver function for machines with oracle `0^(k)` bound one another
  after a rescaling of the argument by at most `n log n`. A leading
  "there exists" is free; each "for all" block costs one oracle level.

The proofs are in `MIDDLE-RUNGS.md`. Part (c) is a paper proof that has
not been independently checked.

**Theorem 11 (the general form). [paper]** Say a formula `Θ(y)`
**decides** a set `A` in `T` when `T ⊢ Θ(ī)` for every `i ∈ A` and
`T ⊢ ¬Θ(ī)` for every `i ∉ A`. Let `BB^{[T]}(ℓ)` be the longest halting
time of an oracle program `p` with oracle `A`, over all pairs of a program
and a formula `Θ` deciding `A` in `T` with `|Θ| + |p| ≤ ℓ`. Let `T ⊇ PA⁻`
be consistent, computably axiomatized or not.

- (a) With absolute constants `a, b, c`,
  `BB^{[T]}(ℓ) ≤ Big_T(aℓ + b)` and `Big_T(n) ≤ BB^{[T]}(n + c)`.
- (b) If `T` decides a set `A` from which the theorems of `T` can be
  computably listed, then `Big_T` is in the growth class of Busy Beaver
  with oracle `A`, up to an `n log n` rescaling. Computably axiomatized
  theories are the case `A = ∅` (Theorems 5, 6); theories containing every
  true `Π_k` sentence are the case `A = 0^(k)`.
- (c) Naming in true arithmetic eventually dominates Busy Beaver with
  oracle `0^(k)` for every `k`, and is dominated by Busy Beaver with an
  oracle for arithmetic truth. It is a limit of the rungs below it, not an
  oracle rung of its own.

The oracle here is what `T` decides, not what `T` proves. The set of
theorems of PA computes the halting problem, yet `Big_PA` is plain Busy
Beaver: "Busy Beaver relative to the theorems of `T`" overshoots by
exactly one jump.

The proofs are in `GENERAL-NAMING-THEOREM.md`, and have not been
independently checked. Machine-checked there **[Lean]**: a formula naming
`m` decides `{m}`, which is the first step of the upper bound in (a), and
a consistent theory decides at most one set with a given formula
(`namesIn_decides_singleton`, `DecidesIn.unique`, `RayoBoolos/Decided.lean`).

**Above arithmetic truth. [paper, one pass, not re-read]**
`SECOND-ORDER-RUNGS.md` works out the next rungs, where formulas may
quantify over sets of numbers. Naming by truth of `Σ¹₁` or `Π¹₁` formulas
is a single rung (number quantifiers are free there), equal to Busy Beaver
over hyperarithmetic oracles with the oracle's description counted, and it
beats arithmetic-truth naming under every computable rescaling. Each
further level `Σ¹_k` is a distinct rung. Busy Beaver with oracle Kleene's
`O`, and Busy Beaver for infinite-time Turing machines, both sit strictly
between the `Π¹₁` and `Σ¹₂` rungs.

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
- Theorem 6: `K(k) ≤ c·D_T(k)·log D_T(k) + c_T`, with `K` measured by
  code numbers of Mathlib programs (Theorem 6(b)). **[Lean]**

So provability complexity and Kolmogorov complexity are the same measure
up to a constant factor and a logarithm, for every admissible `T`.

**Bounding the proof as well.** All of the above bounds only the formula.
[`PROOF-BUDGETS-AND-COMPLEXITY.md`](PROOF-BUDGETS-AND-COMPLEXITY.md) asks
what happens when the proof is also given a length budget. In short
**[paper, with open checks listed in that note]**: if the proof must
exhibit the number, the number is capped by the proof length, short
proofs reach that cap up to a constant, and nothing interesting grows;
if the proof need only show that a unique value
exists, the strength of the theory matters again and the function tracks
the theory's provably total functions; and the natural budgeted measure
sits between two standard time-bounded complexity measures. Nothing there
bears on P versus NP, and [`P-VS-NP-LIMITS.md`](P-VS-NP-LIMITS.md) explains
why it could not: every argument in this report still works when all
machines are given the same oracle, and such arguments are known not to
settle that question.

**Proof budgets, computed in a small system.**
[`NAMING-RECORDS-SMALL-SYSTEM.md`](NAMING-RECORDS-SMALL-SYSTEM.md) computes
the budgeted records exactly in a toy binary arithmetic (constructors
`0`, `D0`, `D1`; operations `S`, `+`, `·`, `^`; a proof is a rewriting
chain, and its length is the total number of symbols written). Every
name up to size 10 was evaluated. Largest number named with name size
`≤ n` and proof length `≤ t` **[computed]**:

| n \ t | 100 | 1,000 | 3,000 | 10⁴ | 10⁵ | 10⁶ | numeral alone |
|---|---|---|---|---|---|---|---|
| 8 | 127 | 216 | 729 | 2,187 | 2,187 | 2,187 | 127 |
| 9 | 255 | 512 | 16,384 | 279,936 | ≈2^23.8 | ≈2^23.8 | 255 |
| 10 | 511 | 1,025 | 262,144 | ≈2^28.0 | ≈2^39.6 | ≈2^49.1 | 511 |

Below 742 proof symbols the record is always a numeral. Compound names
(`24^2` is the first) win only once the budget pays for their
calculation. Cheapest names tell the same story. Only 109 of the numbers
named at size `≤ 10` have a name cheaper than their own numeral on
`|name| + log₂(proof length)`, all of them powers **[computed]**:

| number | numeral's cost | best cost | best name | proof length |
|---|---|---|---|---|
| `6^6` = 46,656 (the smallest) | 21.1 | 21.05 | `6^6` | 4,243 |
| `2^18` = 262,144 | 24.3 | 21.5 | `8^6` | 2,882 |
| `7^15` ≈ 2^42.1 | 49.5 | 26.7 | `7^15` | 106,275 |
| `3^31` ≈ 2^49.1 (the largest saving) | 56.7 | 27.7 | `3^31` | 216,059 |

That is Levin's `Kt` in miniature: most numbers are incompressible, and
the few that compress have a description that is both short and quick
to check.

How fast the record grows with the budget depends on whether proofs can
state lemmas with variables. The toy cannot, and stays far below the
ceiling. First-order proofs in `PA⁻` can, and reach it up to a constant
(Proposition 2 of the proof-budgets note, proved by "doubling" lemmas
such as `∀w ∀z (Dⁿ(w)·z = Dⁿ(w·z))`):

| proofs | unary record at budget `t` | binary record at budget `t` | status |
|---|---|---|---|
| ceiling: the proof writes the numeral | `t/2` | `2^t` | [paper] |
| toy, rewriting chains | about `0.7·√t` | about `2^{0.29·√t}` | [computed, observation] |
| toy, closed lemmas proved once and reused | about `0.45·√t` | about `2^{0.58·√t}` | [computed, observation] |
| `PA⁻`, Hilbert-style, lemmas with variables | at least `t/C` (about `t/660` at powers of two) | at least `2^{t/C}` (about `2^{t/10,900}`) | [paper; checked line by line for `k ≤ 2^20` and `k ≤ 2^{65536}`] |

So the budget does all the work once the proof system is a real one. The
toy's `√t` measures the cost of having no variables, not a property of
proof budgets.

**A picture of the whole ladder.** [`THE-LADDER.md`](THE-LADDER.md) lays
out every rung with its status, places the fast-growing hierarchy and the
well-known named numbers on it, and gives the argument that there is no
top.

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
| Theorem 6(b) (input form), Corollary 7(b) | `compactDecode_compactCode`, `primrec_compactDecode`, `log2_compactCode_lt`, `exists_compact_search`, `BoolosBigIn_le_any_nlogn`, `BoolosBigIn_le_any_nlogn'`, `BoolosBig_PA_le_any_nlogn` | `RayoBoolos/CompactCode.lean` |
| Theorem 6(b) (program form), the sandwich in one statement, Theorem 10(a) with explicit rescaling | `encode_binCode_le`, `binDecode_binTree`, `primrec_binDecode`, `exists_hardwire`, `BoolosBigIn_le_BB_nlogn`, `BoolosBigIn_le_BB_nlogn'`, `BoolosBig_PA_le_BB_nlogn`, `busy_beaver_sandwich`, `TruthBig_sigma1_le_BB_nlogn` | `RayoBoolos/HardWire.lean` |
| Theorem 8 | `bigLe_true_iff`, `bigGe_true_iff`, `provable_bigGe`, `not_provable_bigLe`, `not_provable_bigEq` | `RayoBoolos/NoExactValue.lean` |
| Theorem 9 | see §7 | `rayo-lean/Rayo/NoTop.lean` |
| Theorem 10(a), (b) | `BB_le_TruthBig_sigma1`, `TruthBig_sigma1_le_BB`, `BB_lt_TruthBig_sigma2`, `sigma2_record_gt_sigma1` | `RayoBoolos/TruthNaming.lean` |
| Theorem 10(a), explicit input length | `TruthBig_sigma1_compact` | `RayoBoolos/TruthCompact.lean` |
| Theorem 11, first step of the upper bound only | `namesIn_decides_singleton`, `DecidesIn.unique` | `RayoBoolos/Decided.lean` |

**How the formal statements differ from the prose.** Each line of the
table was compared with the Lean statement on 2026-11-24. The statements
agree, with these qualifications, all noted where the theorem is stated:

- size is the node count of negation normal form (§2);
- "computably axiomatized" is the library's `T.Δ₁` (the axiom set has a
  Δ₁ definition), and "`T ⊇ PA⁻`" is `𝗣𝗔⁻ ⪯ T` (`T` proves every axiom of
  `PA⁻`);
- `BB` and `BBtime` use Mathlib's program numbering and its bounded
  evaluator's notion of time (§5);
- Theorem 8(a) is checked in the form "some formula names a number
  `≥ k`", and Theorem 8 needs `n ≥ 1`;
- Theorem 9(c) is checked in a slightly more general form (§7);
- in Theorem 10(a) and Corollary 7(a) the rescaling functions `h` and
  `M` are not bounded; the bounded forms are `TruthBig_sigma1_compact`,
  `TruthBig_sigma1_le_BB_nlogn` and Corollary 7(b);
- Theorem 10(b) is checked for `Σ₂`, not for the smaller class `Π₁`;
- Theorems 10(c) and 11 are not machine-checked beyond the entries above.

All `RayoBoolos` files are under `large-numbers/rayo-lean-boolos/`.
Toolchain: Lean 4 `v4.32.2`, with Mathlib and Foundation pinned by
`lake-manifest.json`. To check: run `lake build` in
`large-numbers/rayo-lean-boolos/` (1266 jobs) and in
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
  lines. The upper half appears informally: a MathOverflow discussion
  (question 34710, 2010) bounds definability-by-provability in ZFC by a
  second-level Busy Beaver, and the Googology Wiki page on Rayo's number
  remarks that a provability reading would not be much larger than a
  Busy Beaver value. We did not find the lower half, the two-sided
  sandwich, or the independence of the axioms stated anywhere, and expect
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
- **The complexity `D_T` of §8** is a known notion: Kikuchi, Kurahashi
  and Sakai (2012) define a provability-based Kolmogorov complexity.
- **Theorem 9 and the table of rungs** restate Berry's paradox and
  Tarski's theorem; oracle Busy Beavers are in Aaronson (2020) §3.
  Simmons (Theorem 2.4 and Appendix C) gives the provability instance of
  the step up: a metalanguage names "the largest number named by a term
  that the theory proves names a number in fewer than n symbols" with a
  term of size about log n.
- **The repetition of the pattern from rung to rung is classical.** The
  hierarchy of Busy Beaver functions through the computable ordinals,
  the fact that each level's theory is the previous one relativized, and
  the dependence on ordinal notation at limit stages are in Aaronson
  (2020) §3 and rest on Post and Kleene. It is not claimed here. What is
  added is the translation to naming in `n` symbols at the levels
  treated (`LITERATURE-SURVEY.md` §9).
- **Theorem 10** proves a guess of Aaronson from the same MathOverflow
  discussion (2010), that definability with truth fixed for `Π_k`
  sentences grows like a Busy Beaver function `k` levels up. The
  ingredients are classical; we found no earlier proof or precise
  statement. Upper bounds of this kind appear in Goucher, "The Ξ
  function" (2013) and Cao (2025).

- **Theorem 11** is built from classical ingredients: strong
  representability (Tarski, Mostowski and Robinson 1953), the
  representable sets of complete theories (Scott 1962), and oracle
  search. We found no earlier statement of it, of its single-oracle form
  for theories that are not computably axiomatized, or of the one-jump
  overshoot.

**What is claimed.** For Theorems 1 to 9, not new theorems. Theorem 10
is offered as a proof of a stated guess, on paper for general `k`, and
Theorem 11 as a general statement we did not find in the literature, on
paper. Neither has been checked by an outside reader. The contribution
is:

1. machine-checked proofs of Theorems 1, 2, 3, 5, 6 (including 6(b) as a
   bound on Mathlib program code numbers), Corollary 7, Theorem 8 and Theorem 9, with explicit
   constants and a base theory with no
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
Sakai (2012) beyond its abstract and definitions.

## 11. What the results say

Five conclusions, in plain terms. None is a new theorem; each is a reading
of the results above.

1. **Bits are the wrong currency.** The project began by asking how the
   cost of a naming scheme, measured in bits, relates to how fast its
   numbers grow, and found no clean law. The reason is now visible.
   Within one rung, changing the scheme shifts the budget by a constant
   (Corollary 7), and a step up to the next rung costs about `log n`
   symbols (Theorems 2 and 9). Symbols are nearly free. What a faster
   function costs is the strength of what is assumed.

2. **There are two regimes, with a sharp line between them.** While
   "names" means *provably names*, stronger axioms buy nothing: every
   consistent, computably axiomatized theory lands in the Busy Beaver
   class (Theorems 5 and 6, Corollary 7). Once "names" means *truly
   names*, stronger assumptions are the only thing that buys anything,
   and Theorems 10 and 11 say exactly what moves a scheme up: which
   questions the theory can settle both ways, counted in the arithmetic
   case by blocks of "for all", and never how many axioms there are.

3. **A largest-number contest has no winner without a referee.** "The
   biggest number in `n` symbols" means something only once the scheme
   and the assumptions behind it are fixed. Left open, the winner is
   whoever assumes the most, up to the point of contradiction (Section 7).
   BIG FOOT, whose defining notion of truth turned out to be
   inconsistent, shows what crossing that point looks like.

4. **Every rung has its own blind spot.** A theory proves no exact value
   of its own naming function (Theorem 8), and each rung's values encode
   about `n` bits that the rung below cannot obtain (Section 8). So the
   cost of a rung shows up twice: in what must be assumed, and in what
   can no longer be proved.

5. **Size is not information.** These numbers are unimaginably long and
   carry at most about `n` symbols of information. The ladder ranks how
   much can be unpacked from a short description, given what a
   description is allowed to mean. The essay
   [`BIG-NUMBERS-AS-COMPRESSION.md`](BIG-NUMBERS-AS-COMPRESSION.md)
   develops this reading.

Two questions these suggest, with what is now known:

- **One scale for the whole ladder.** Tested in
  [`ASSUMPTION-COST-SCALE.md`](ASSUMPTION-COST-SCALE.md) **[paper and
  expected; see the tags there]**. The obvious candidate, the weakest
  theory proving a scheme's numbers exist, fails: a weak theory proves
  every Busy Beaver value exists, while proving TREE total needs a far
  stronger one, so that scale puts TREE above schemes that vastly outgrow
  it. Two different assumptions are in play, and each is free where the
  other does the work: believing a process stops (priced by an ordinal,
  the only thing that moves on the computable rung), and treating a body
  of truths as given (the only thing that moves above it). What survives
  is a law with two coordinates read in order: first how much truth a
  scheme consults, then its termination ordinal. Whether one natural
  measure combines the two remains open.
- **A general theorem behind points 1 and 2.** Answered by Theorem 11.
  The first guess, Busy Beaver relative to the theorems of `T`, was wrong
  by one jump; the right oracle is what `T` decides.

## 12. Open items

- Re-read `SECOND-ORDER-RUNGS.md` and `ASSUMPTION-COST-SCALE.md`, which
  have had one pass only.
- Have Theorems 10(c) and 11 checked independently, and machine-check
  them, which needs oracle machines tied to the arithmetical hierarchy.
- Sharpen the constants: the `6` in Theorem 2 comes from the term
  encoding of binary numerals and is not optimal.
