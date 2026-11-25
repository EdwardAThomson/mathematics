# The middle rungs: naming by bounded arithmetic truth is oracle Busy Beaver

**Status, 2026-11-24.** Paper proofs for every level `k`. The bottom rung
(`Σ₁` truth naming against Busy Beaver, both directions), the step to the next
rung (`Σ₂` truth names one more than Busy Beaver), and from these one concrete
instance of Claim B of `THE-LADDER.md` §3, are machine-checked (§8). Each claim is tagged **[Lean]**, **[paper]** or **[classical]** as in
`THE-LADDER.md`.

## 0. In plain language

`THE-LADDER.md` puts a rung between Busy Beaver and full arithmetic truth for
every `k`: "the formula is a statement of arithmetic with `k` alternations of
*there exists* and *for all*, and it is true of the number and nothing else",
and says this should match Busy Beaver for machines with an oracle for the
halting problem iterated `k − 1` times. That match was tagged **[expected]**.
This note proves it, and finds that the count is slightly different from the
one guessed.

What matters is the number of **"for all" blocks**, not the number of
alternations:

| naming by truth of | grows like | 
|---|---|
| bounded formulas (`Δ₀`), or `Σ₁` | Busy Beaver `BB` |
| `Π₁`, or `Σ₂` | `BB'`, Busy Beaver with a halting oracle |
| `Π_k`, or `Σ_{k+1}` | `BB^{(k)}`, Busy Beaver with the `k`-th jump as oracle |

In each row the two naming functions and the Busy Beaver function bound one
another after a rescaling of the argument by at most `n log n`. A leading
"there exists" is free, because whatever it asserts exists can be packed into
the number being named. Each "for all" costs exactly one oracle level.

Two things fall out.

- **Rung 1 needs no unbounded quantifier at all.** A bounded formula that says
  "`x` is the complete record of a halting run of program `e`" is true of one
  number, and that number is at least the run time. Truth alone, with no
  proofs and no search inside the formula, already reaches Busy Beaver.
- **Aaronson's 2010 guess holds.** On MathOverflow (question 34710, August
  2010) Aaronson asked for the growth of `z_k(n)`, the largest number
  definable in `n` symbols when truth is fixed for `Π_k` sentences, and
  guessed it grows "more-or-less like `BB_{k+c}(n)`". Theorem 5 proves this
  for the reading "provable in a theory that contains every true `Π_k`
  sentence", with `BB_{k+c} = BB^{(k)}`, and Theorems 1 and 2 prove it for the
  reading "true `Π_k` or `Σ_{k+1}` formula".

On novelty, see §7. Every ingredient is classical. We found no statement of
the sandwich itself, and the only statement of the correspondence we found is
Aaronson's, as a guess.

## 1. Setting

The language is `ℒₒᵣ = {0, 1, +, ·, <}`, with the size `|φ|` the node count
used throughout this project (`fSize`). Numerals are the short binary terms
`bin(n)` of `BOOLOS-IS-BUSY-BEAVER-CLASS.md` §2, with `|bin(n)| ≤ 6·log₂(n+2)`.

**Formula classes.** We use the liberal classes of the `Foundation` library
(`Hierarchy Γ k`): `Σ₀ = Π₀ = Δ₀` are the formulas whose quantifiers are all
bounded (`∀x < t`, `∃x < t`); `Σ_{k+1}` is closed under `∧`, `∨`, bounded
quantifiers and unbounded `∃`, and contains `Π_k`; dually for `Π_{k+1}`. In
particular `Σ_k ∪ Π_k ⊆ Σ_{k+1} ∩ Π_{k+1}` with no change of size. Every
liberal `Σ_k` formula is equivalent in `ℕ` to a prenex one, and all results
below hold for prenex classes too, with different constants (the
`Σ_{k+1}` upper bound is proved for the larger, liberal class; the lower
bounds produce formulas that can be put in prenex form once and for all,
since they are fixed formulas with a numeral substituted).

**Truth naming.** A formula `φ(x)` with one free variable *names* `m` (by
truth) when `ℕ ⊨ ∀x (φ(x) ↔ x = m)`: `m` is the only number `φ` is true of.
For a class `Γ`,

```
N_Γ(n) := max { m : some φ ∈ Γ with |φ| ≤ n names m }     (0 if there is none).
```

Each formula names at most one number and there are finitely many formulas of
each size, so `N_Γ` is well defined and non-decreasing. **[Lean for
`Γ = Σ_k, Π_k`, every `k`: `TruthBig`, `TruthBig_mono` in
`RayoBoolos/TruthNaming.lean`]**

**Oracle Busy Beaver.** `0^(0) = ∅` and `0^(j+1)` is the halting problem for
machines with oracle `0^(j)`. Fix a universal oracle machine `U` reading
binary programs. For a program `p` let `U^A(p)↓t` mean that `U` run on `p`
with oracle `A` halts after exactly `t` steps. Then

```
BB^{(k)}(ℓ) := max { t : |p| ≤ ℓ and U^{0^(k)}(p)↓t }.
```

`BB^{(0)}` is the step function `S` of the Busy Beaver note. **[classical:
Aaronson, "The Busy Beaver Frontier" (2020) §3; Cao (2025)]**

## 2. Classical facts used

- **(F1) Post's theorem, uniform form.** For `k ≥ 1`, `q ∈ 0^(k)` iff
  `ℕ ⊨ ∃w θ_k(q, w)` for a fixed `Π_{k−1}` formula `θ_k`. The set of true
  `Σ_{k+1}` sentences is computably enumerable relative to `0^(k)`, uniformly
  in the sentence; in particular `0^(k)` decides truth of `Σ_k` and `Π_k`
  sentences. **[classical: Post 1948; Soare, *Recursively Enumerable Sets
  and Degrees*, IV.2]**
- **(F2) Oracle runs are checkable from a finite query record.** Let a
  *record* be a finite list `σ = ((q₀, a₀), …, (q_{r−1}, a_{r−1}))` with each
  `aᵢ ∈ {0, 1}`. There is a `Δ₀` formula `H(e, t, σ, c)` saying: "`c` is the
  complete step-by-step trace of `U` run on program `e`, with its `i`-th
  oracle query answered by `aᵢ`; the run asks exactly `r` queries, the `i`-th
  is `qᵢ`, and it halts after exactly `t` steps". **[classical: Kleene's
  normal form, relativized]**

  The trace `c` has to be an argument. "Halts after exactly `t` steps" is
  not a bounded property of `e, t, σ` alone, because the trace is far larger
  than any polynomial in them; with the trace supplied, checking it is
  bounded. Sequences and tuples are coded injectively (each has exactly one
  code), so that the trace and the record of a run are single numbers.

  If `U^A(e)↓t` then there is exactly one pair `σ, c` with `H(e, t, σ, c)`
  and all answers correct for `A` (`aᵢ = 1 ↔ qᵢ ∈ A`), namely the actual
  record and trace of the run; and if `U^A(e)` does not halt there is none,
  for any `t`. *Proof:* by induction on `i`, a record whose answers are all
  correct agrees with the actual run up to its `i`-th query.
- **(F3) Short programs for numerals.** A program can hard-wire a number `L`
  in `log₂ L + O(1)` bits.

## 3. Theorem 1 (lower bound): `Π_k` truth naming reaches `BB^{(k)}`

**Theorem 1.** For each `k ≥ 0` there is a constant `C_k` such that, whenever
the program with code `e` satisfies `U^{0^(k)}(e)↓t`,

```
N_{Π_k}( C_k + 12·log₂(e+2) )  ≥  t.
```

(For `k ≥ 1` the factor 12 can be 6.) Since a program of length `≤ ℓ` has
code `e < 2^{ℓ+1}`, this gives `N_{Π_k}(12ℓ + C_k + 24) ≥ BB^{(k)}(ℓ)`.

*Proof.* Let `x` range over codes of tuples `⟨t, σ, W, c⟩` (Cantor pairing
and an injective, `Δ₀`-decodable sequence coding, with every component `≤`
the code). Define

```
Ψ_k(z, x)  :≡  ∃ t, σ, W, c ≤ x [ x = ⟨t, σ, W, c⟩  ∧  H(z, t, σ, c)  ∧  |W| = |σ|
                ∧ ∀ i < |σ| ( Yes_k(qᵢ, aᵢ, wᵢ) ) ]
```

where, for `k ≥ 1`,

```
Yes_k(q, a, w)  :≡  ( a = 1 → θ_k(q, w) ∧ ∀w' < w ¬θ_k(q, w') )
                  ∧ ( a = 0 → w = 0 ∧ ∀w' ¬θ_k(q, w') )
```

and, for `k = 0`, `Yes_0(q, a, w) :≡ a = 0 ∧ w = 0` (the oracle is empty).

*Complexity.* `θ_k` is `Π_{k−1}`, so `¬θ_k` is `Σ_{k−1}`, and `∀w'¬θ_k` is
`Π_k`. Everything else is `Δ₀`, and the liberal class allows the bounded
quantifiers. So `Ψ_k` is `Π_k` (and `Δ₀` for `k = 0`).

*Exactly one `x`.* By (F1) the conditions `Yes_k` say precisely that each
answer is correct for `0^(k)` and that `wᵢ` is the least witness for a "yes"
and `0` for a "no". By (F2) `σ` is then the actual record, `c` the actual
trace and `t` the actual halting time, and `W` is determined by `σ`. Codes
are unique, so in `ℕ`, `Ψ_k(e, x)` holds of exactly one `x`, namely
`x_e := ⟨t, σ, W, c⟩`, and `x_e ≥ t`.

*The name.* Put `φ_e(x) :≡ ∀z (z = bin(e) → Ψ_k(z, x))` for `k ≥ 1`, and
`φ_e(x) :≡ ∃z < bin(e)+1 (z = bin(e) ∧ Ψ_0(z, x))` for `k = 0`. Both are in
`Π_k`, both are equivalent in `ℕ` to `Ψ_k(e, x)`, so both name `x_e ≥ t`, and
`|φ_e| ≤ |Ψ_k| + 12·log₂(e+2) + 8` (the numeral occurs twice when `k = 0`,
once when `k ≥ 1`). Take `C_k := |Ψ_k| + 8`. ∎

**[paper]** for all `k`. The Lean file proves the weaker form one level up
instead: for `k = 0`, `Σ₁` (rather than `Δ₀`) naming reaches `BB`; for `k = 1`,
`Σ₂` (rather than `Π₁`) naming exceeds `BB`. See §8.

*Remark.* For `k = 0` the formula is bounded. It is the record of the
computation, not a search for it, so a `Δ₀` formula names a number at least as
large as the run time of any halting program of comparable description
length.

## 4. Theorem 2 (upper bound): `Σ_{k+1}` truth naming stays below `BB^{(k)}`

**Theorem 2.** For each `k ≥ 0` there are constants `c` (absolute) and `c_k`
with

```
N_{Σ_{k+1}}(n)  ≤  BB^{(k)}( c·n·log₂(n+2) + c_k ).
```

*Proof.* For a formula `φ(x)` let `P_φ` be the oracle program: "enumerate the
true `Σ_{k+1}` sentences, using the oracle (F1); on meeting `φ(j̄)` for some
`j`, idle for `j` steps and halt." If `φ ∈ Σ_{k+1}` names `m`, then `φ(m̄)` is
a true `Σ_{k+1}` sentence and `φ(j̄)` is false for `j ≠ m`, so
`U^{0^(k)}(P_φ)` halts after more than `m` steps. `P_φ` is a fixed enumerator
(`c_k` bits) plus a description of `φ`: its tree shape and one label per node,
where labels other than variable indices come from a fixed finite set and
variable indices are `< n`, for `c·n·log₂(n+2)` bits. ∎ **[paper]**

The same argument with "true `Σ_{k+1}`" replaced by "provable in `T`" is
Theorem 3 of the Busy Beaver note.

## 5. Theorem 3: the rung

Since `Π_k ⊆ Σ_{k+1}` without change of size, Theorems 1 and 2 combine:

**Theorem 3.** For each `k ≥ 0` there are constants `a, b, c, c_k` with

```
BB^{(k)}(ℓ)  ≤  N_{Π_k}(aℓ + b)  ≤  N_{Σ_{k+1}}(aℓ + b),
N_{Π_k}(n)  ≤  N_{Σ_{k+1}}(n)  ≤  BB^{(k)}( c·n·log₂(n+2) + c_k ).
```

So `N_{Π_k}`, `N_{Σ_{k+1}}` and `BB^{(k)}` are one growth class, up to a
rescaling of the argument by at most `n log n`. **[paper]**

**Corollary 4 (the rungs are distinct).** `N_{Π_{k+1}}` eventually dominates
`N_{Σ_{k+1}}` composed with any function computable from `0^(k+1)`, and in
Berry form,

```
N_{Π_{k+1}}( C + 12·log₂(n+2) )  >  N_{Σ_{k+1}}(n)     for all n,
```

for a constant `C`. *Proof.* Let `L(n) := c·n·log₂(n+2) + c_k`. The
`0^(k+1)`-program "for each program `p` of length `≤ L`, ask whether
`U^{0^(k)}(p)` halts (a `Σ_{k+1}` question, decided by `0^(k+1)`), run the
ones that do (simulating the `0^(k)` oracle with `0^(k+1)`), take the largest
run time `B`, idle `B + 1` steps and halt" has `log₂ L + O(1)` bits (F3) and
runs more than `BB^{(k)}(L) ≥ N_{Σ_{k+1}}(n)` steps. Apply Theorem 1 at level
`k + 1`; `log₂ L(n) ≤ 2·log₂(n+2) + O(1)`. The domination statement is the
classical fact that `BB^{(k+1)}` dominates every `0^(k+1)`-computable function
**[classical]**, applied through Theorem 3. ∎ **[paper; the Berry form is [Lean] for `k = 0` with `Σ₂` in place of
`Π₁` and an unquantified rescaling `h` in place of `L`,
`sigma2_record_gt_sigma1` in §8]**

This is Claim B of `THE-LADDER.md` §3 for each middle rung: `R = Σ_{k+1}`
truth naming, `R⁺ = Π_{k+1}` (or `Σ_{k+2}`) truth naming, and the short
formula "one more than the record of `R`" exists in `R⁺` with budget
`C + O(log n)`.

## 6. Theorem 5: provable naming from true `Π_k` sentences (Aaronson's `z_k`)

Let `T` be a consistent theory in `ℒₒᵣ` (or interpreting it, such as ZFC)
that contains `PA⁻` and every true `Π_k` sentence, for some `k ≥ 1`. Here
`Π_k` is the liberal class of §1. If only the true *prenex* `Π_k` sentences
are assumed, the Lemma below needs `T ⊇ PA` (to move bounded quantifiers
inward), which holds in the cases of interest; the lower bound of Theorem 5
holds either way, because for the particular formula used the proof below
only ever calls on prenex `Π_k` sentences (`θ_k(q̄, w̄)` and
`∀w' ¬θ_k(q̄, w')`) after unfolding bounded quantifiers. Let
`BoolosBig_T` be provable naming as in the Busy Beaver note: `φ` names `m`
when `T ⊢ ∀x (φ(x) ↔ x = m̄)`.

**Lemma (`Σ_{k+1}`-completeness).** `T` proves every true `Σ_{k+1}`
sentence. *Proof:* induction on the formula. Atoms and negated atoms are
decided in `PA⁻`; bounded quantifiers with a closed bound unfold, in `PA⁻`,
into finite conjunctions and disjunctions; for an unbounded `∃`, prove the
instance at a true witness; a `Π_k` constituent (including `Σ_j`, `Π_j` for
`j < k`, which are `Π_k`) is in `T` when true. ∎

**Theorem 5.** There are constants with

```
BB^{(k)}(ℓ)  ≤  BoolosBig_T(aℓ + b),          BoolosBig_T(n)  ≤  BB^{(k)}(c·n·log₂(n+2) + c_T)
```

where the second needs `T` to be computably enumerable relative to `0^(k)`
(true for `PA + Th_{Π_k}(ℕ)` and for `ZFC + Th_{Π_k}(ℕ)`, since `0^(k)`
decides `Π_k` truth).

*Proof.* Lower bound: use the minimization lemma of the Busy Beaver note §2
with the `Δ₀` matrix `δ` replaced by the `Π_k` formula `Ψ_k` of Theorem 1.
The naming formula `μ_e` is then `Σ_{k+1}` and true of `x_e`, so `T` proves
`μ_e(x̄_e)` by the Lemma, and uniqueness is provable in `PA⁻` from the shape
of `μ` exactly as before (it uses only trichotomy and that `B` and `¬B`
contradict each other). Upper bound: Theorem 3 of the Busy Beaver note, with
proof search relative to `0^(k)`; consistency makes each name unique. ∎
**[paper]**

So Aaronson's guess `z_k(n) ≈ BB_{k+c}(n)` holds with `BB_{k+c} = BB^{(k)}`,
for any such `T`, and as at rung 1 the choice of `T` only moves constants.
(For ZFC this needs `ZFC + Th_{Π_k}(ℕ)` to be consistent, which holds if ZFC
proves no false arithmetic sentence.)

## 7. Is this known?

What we checked: `LITERATURE-SURVEY.md` (§4a, §7), plus searches on
2026-11-24 for oracle Busy Beaver and arithmetic naming, `Π⁰₁` singletons and
Kolmogorov complexity, and definitional complexity in the arithmetical
hierarchy.

- **Aaronson (MathOverflow 34710, 2010)** states the correspondence as a
  guess, with an unspecified shift `c`. No answer there proves it. This is the
  closest prior statement, and should be cited as the conjecture this note
  proves.
- **Goucher, "The Ξ function" (2013)** evaluates `n`-quantifier formulas with
  a tower of oracle machines, an upper bound of the kind in Theorem 2, without
  the matching lower bound or the `Π`/`Σ` shift.
- **Cao (2025), Prop. 2**: formulas with `i` alternations are decided by
  machines with oracles up to level `i`. Again the upper-bound direction.
- **Kolmogorov complexity relative to `0^(k)`** (Bienvenu, Muchnik, Shen,
  Vereshchagin, "Limit complexities revisited"; Becher, Figueira and others
  on complexity of infinite computations) is closely related: the shortest
  `Σ_{k+1}` definition of a number has length within a factor `O(log)` of its
  `0^(k)`-Kolmogorov complexity, by the proofs above (for `Σ_{k+1}`, name the
  output by `∃x Ψ_k`). We did not find this stated for definitions in
  arithmetic, and it is the kind of fact that is likely folklore there.

**Suggested wording:** "We prove Aaronson's 2010 guess: naming by truth of
`Π_k` or `Σ_{k+1}` formulas, and provable naming from all true `Π_k`
sentences, are each in the growth class of the Busy Beaver function with
oracle `0^(k)`. The ingredients are classical; we found no earlier proof or
precise statement." The observation that `Π_k` and `Σ_{k+1}` land on the same
rung (a leading existential block is free) is part of that statement and
should not be claimed separately.

## 7a. Second read, 2026-11-24

The proofs of §§2 to 6 were re-read line by line, in the thread that wrote
the report (so by the same author, with a fresh pass; not an independent
referee). The theorems stand. Three repairs were made to the text:

- (F2) claimed a bounded formula `H(e, t, σ)` without the trace. That is not
  justified: bounded formulas cannot simulate `t` steps given only `t`. The
  trace is now part of the named number, which is what §0 and §8 already
  described informally. No statement changes.
- Uniqueness in Theorem 1 needs each sequence to have exactly one code. This
  is now stated.
- The Lemma of §6 mixed liberal and prenex `Π_k`. The hypothesis is now
  explicit.

Checked and found correct as written: the level count in `Ψ_k` (each
`Yes_k` is `Π_k`, bounded quantifiers stay inside the liberal class), the
size bounds and the constants 12 and 6, the program-length count in
Theorem 2, the Berry form of Corollary 4 including its `12·log₂(n+2)`, and
provable uniqueness in Theorem 5 from trichotomy alone.

Still **[paper]**. A reader outside this project, or a Lean proof, has not
yet confirmed the general-`k` statements.

## 8. What is machine-checked

`rayo-lean-boolos/RayoBoolos/TruthNaming.lean`, sorry-free, axioms `propext`,
`Classical.choice`, `Quot.sound`, built against the pinned
`Foundation`/Mathlib (`lake build`, 1260 jobs). Formula levels are
`Foundation`'s `Hierarchy Γ k`, the liberal classes of §1. "Programs" are
Mathlib's `Nat.Partrec.Code` run on input `0`, indexed by code number, and
`BB N` is the largest output of a halting program with code `≤ N`
(`RayoBoolos/BusyBeaver.lean`). Since `log₂ N` is the program's length in
bits, `C + 6·log₂ N` below is "linear in program length".

| statement | Lean name |
|---|---|
| `TruthBig Γ k n` is well defined (finitely many values) | `truthValues_finite`, `TruthBig` |
| monotone in `n`; `Π_k` and `Σ_k` naming are part of `Σ_{k+1}` naming | `TruthBig_mono`, `TruthBig_pi_le_sigma_succ`, `TruthBig_sigma_le_sigma_succ` |
| `BB N ≤ TruthBig 𝚺 1 (C + 6·log₂ N)`, and the same for halting times | `BB_le_TruthBig_sigma1`, `BBtime_le_TruthBig_sigma1` |
| `TruthBig 𝚺 1 n ≤ BB (h n)` for a fixed function `h` | `TruthBig_sigma1_le_BB` |
| the same with explicit length: every value of `TruthBig 𝚺 1 n` is an output of one fixed program on an input of fewer than `4·n·(log₂(n+16)+1)` bits | `TruthBig_sigma1_compact` (`RayoBoolos/TruthCompact.lean`) |
| `BB N < TruthBig 𝚺 2 (C + 6·log₂ N)` | `BB_lt_TruthBig_sigma2` |
| Claim B instance: `TruthBig 𝚺 1 n < TruthBig 𝚺 2 (C + 6·log₂ (h n))` | `sigma2_record_gt_sigma1` |

How the proofs go. The `Σ₁` lower bound needs no search and no proofs: the
`Σ₁` graph of "program `e` outputs `v`" (`partrec_graph`) with `e` given as a
binary numeral is true of `v` alone. The `Σ₁` upper bound finds the named
number by proof search in `𝗣𝗔`: a true `Σ₁` sentence is provable
(`sigma_one_completeness_iff`), and anything provable is true in `ℕ`, so the
search returns exactly the named number (`exists_truth_search`); composing the
search code with a constant gives a program with code `h n`. The `Σ₂` formula
is "every output of a halting program with code `≤ N` is `< x`" (`Π₁`) and
"every `w < x` is `≤` some such output" (`Σ₁`), true only of `BB N + 1`
(`succBB_iff`).

Gaps between the Lean and the paper:

- `h` is not bounded explicitly. It comes from `Foundation`'s Gödel numbering,
  and the paper's `c·n·log n` needs an efficient encoding (the same gap as
  `templateCode` in `UpperBound.lean`).
- The sharper level statements, that `Δ₀` already reaches `BB` and `Π₁`
  already exceeds it (Theorem 1 at `k = 0, 1`), need a `Δ₀` formula for a
  complete computation record, which this repository does not have yet.
- The general-`k` theorems need oracle machines relative to `0^(k)`, which
  neither Mathlib nor `Foundation` provides in a form tied to the
  arithmetical hierarchy. They stay **[paper]**.
