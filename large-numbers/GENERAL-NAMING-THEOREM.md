# The general naming theorem: provable naming is Busy Beaver relative to what the theory can decide

Written 2026-11-24, in answer to the open question left in the large-numbers
discussion: is the growth of a theory's naming function "the Busy Beaver
function relative to the set of statements the theory proves", with the
known rungs as special cases?

Tags as in the rest of the project: **[Lean]** machine-checked,
**[paper]** proved here on paper and not independently checked,
**[classical]** a known result we cite.

## 0. In plain language

The guess was nearly right, but it named the wrong oracle, and the gap is
exactly one halting-problem jump.

- **The literal guess is false.** For PA the set of provable statements is
  as hard as the halting problem, so "Busy Beaver relative to PA's
  theorems" is the second Busy Beaver level. But PA's naming function is
  plain Busy Beaver. The same one-level overshoot happens at every middle
  rung. The theorems of a theory are always one jump above what the theory
  can actually use for naming.
- **The right oracle is "what the theory can decide".** Say a theory
  *decides* a set of numbers `A` if some formula `Θ(y)` has the theory
  prove `Θ(i)` for every `i` in `A` and prove `not Θ(i)` for every `i`
  outside it. A machine that asks such an oracle questions can be simulated
  inside the theory, because each answer is a theorem. So the theory can
  name the running time of every such machine (Theorem 2).
- **And nothing more.** Conversely, if a formula names `m`, then that same
  formula decides the one-element set `{m}`, and a tiny machine asking
  "is it 0? is it 1? ..." runs for at least `m` steps. So the naming
  function is exactly the Busy Beaver function for machines that may
  consult any oracle the theory decides, with the oracle's description
  counted in the size (Theorem 4). This holds for every consistent theory
  containing basic arithmetic, with no extra hypothesis.
- **When there is a single best oracle you get a clean rung.** If the
  theory decides some set `A` from which its own theorems can be listed
  (for example, if it can tell which sentences are its own axioms), then
  its naming function is Busy Beaver with oracle `A` (Corollary 6). Every
  ordinary theory has `A` = nothing, giving plain Busy Beaver, and adding
  all true `Π_k` sentences gives `A` = the `k`-th jump. Those are the two
  known results, now as special cases.
- **When there is no best oracle you get a limit, not a rung.** True
  arithmetic decides every arithmetically definable set but no single set
  that lists its theorems (that would contradict Tarski). Its naming
  function beats every finite oracle level and is beaten by Busy Beaver
  with the full arithmetic-truth oracle (Theorem 8). So the "rung ω" of
  `THE-LADDER.md` is a diagonal over the finite rungs, not an oracle Busy
  Beaver of its own.

## 1. Setting

`ℒₒᵣ`, formula size `|φ|`, short numerals `bin(n)`, the universal oracle
machine `U`, and the minimization lemma are as in
`BOOLOS-IS-BUSY-BEAVER-CLASS.md` §§1–2 and `MIDDLE-RUNGS.md` §1. Throughout,
`T` is a **consistent** theory in `ℒₒᵣ` containing `PA⁻`. It need not be
computably axiomatized. `T`-naming and the naming function are as before:

```
φ T-names m   :⟺   T ⊢ ∀x (φ(x) ↔ x = m̄)
Big_T(n)      :=   max { m : some φ with |φ| ≤ n T-names m }.
```

(Well defined for any consistent `T ⊇ PA⁻`: **[Lean]** `BoolosBigIn`,
`namedValuesIn_finite` in `RayoBoolos/AnyTheory.lean`.)

**Oracle Busy Beaver.** For a set `A ⊆ ℕ`,
`BB^A(ℓ) := max { t : |p| ≤ ℓ and U^A(p)↓t }`, the longest halting time of a
program of at most `ℓ` bits with oracle `A`. `BB^∅` is the step function `S`
and `BB^{0^(k)}` is `BB^{(k)}` of `MIDDLE-RUNGS.md`.

**Deciding a set.** A formula `Θ(y)` *decides `A` in `T`* if for every
`i ∈ ℕ`:

```
i ∈ A  ⟹  T ⊢ Θ(ī),          i ∉ A  ⟹  T ⊢ ¬Θ(ī).
```

Write `D(T)` for the sets decided in `T` by some formula. This is the
classical notion of a set being *strongly representable* (or *binumerable*)
in `T`; for complete `T ⊇ PA` it is the set of `T`-representable sets, which
Scott (1962) showed form a Scott set. **[classical]** Two facts we use:

- If `T` is computably axiomatized, `D(T)` is exactly the computable sets.
  **[classical: Tarski, Mostowski and Robinson, *Undecidable Theories*
  (1953)]**
- `D(TA)`, for true arithmetic `TA = Th(ℕ)`, is exactly the arithmetical
  sets: a defining formula decides its set in `TA`, and conversely a set
  decided in `TA` by `Θ` is defined by `Θ`. **[classical, immediate]**

**Busy Beaver relative to `T`'s decided sets.** Charge a machine for its
program and for the formula describing its oracle:

```
BB^{[T]}(ℓ) := max { t : |Θ| + |p| ≤ ℓ, Θ decides some A in T, U^A(p)↓t }.
```

This is finite for each `ℓ`: there are finitely many pairs `(Θ, p)`, and
each `Θ` decides at most one set because `T` is consistent.

## 2. The one new lemma: completeness relative to a decided oracle

Let `Δ₀(Θ)` be the formulas built from atomic `ℒₒᵣ` formulas and instances
`Θ(t)` (with `t` a term) by `¬, ∧, ∨` and bounded quantifiers `∀x < t`,
`∃x < t`. Read in `ℕ` with `Θ` interpreted as `A`, each `Δ₀(Θ)` sentence is
true or false.

**Lemma 1 (relative `Δ₀`-completeness).** If `Θ` decides `A` in `T`, then
for every `Δ₀(Θ)` sentence `σ`: `T ⊢ σ` if `σ` is true in `(ℕ, A)`, and
`T ⊢ ¬σ` if it is false. Consequently `T` proves every `Σ₁(Θ)` sentence
(`∃` in front of `Δ₀(Θ)`) that is true in `(ℕ, A)`.

*Proof.* Induction on `σ`, proving both halves at once. Closed terms
evaluate in `PA⁻` to their numeral values. Atomic `ℒₒᵣ` sentences and their
negations are decided in `PA⁻`. An instance `Θ(t)` with `t` closed: `PA⁻`
proves `t = ī` for its value `i`, and `T` proves `Θ(ī)` or `¬Θ(ī)` as `i`
is in `A` or not. Connectives are immediate from the induction hypothesis.
A bounded quantifier `∀x < t` (or `∃x < t`) with value `t = n`: `PA⁻ ⊢
∀x (x < n̄ ↔ x = 0̄ ∨ … ∨ x = (n−1)‾)`, so the sentence is `T`-equivalent to
a finite conjunction (disjunction) of instances, which the induction
hypothesis decides. The `Σ₁(Θ)` consequence: prove the instance at a true
witness. ∎ **[paper; this is the usual proof of `Δ₀`-completeness of `PA⁻`
with one extra atomic case]**

Note what is *not* used: `Θ` itself can have any complexity, and `T` never
needs to prove anything general about `Θ` (no induction, no totality, no
"`Θ` defines `A`"). Only its individual instances at numerals matter.

## 3. Theorem 2 (lower bound): `T` names every decided-oracle running time

**Theorem 2.** There are absolute constants `a, b` such that if `Θ` decides
`A` in `T` and `U^A(p)↓t`, then `Big_T(a·(|Θ| + |p|) + b) ≥ t`. Hence

```
BB^A(ℓ) ≤ Big_T(a·ℓ + a·|Θ| + b)            for each A ∈ D(T),
BB^{[T]}(ℓ) ≤ Big_T(a·ℓ + b).
```

*Proof.* Use the query record `σ` and the `Δ₀` formula `H(e, t, σ)` of
`MIDDLE-RUNGS.md` (F2): "running `U` on program `e`, answering its `i`-th
query by `aᵢ`, asks exactly the queries `qᵢ` listed in `σ` and halts after
exactly `t` steps". Put

```
δ(z, x, w)  :≡  ∃t ≤ x ∃σ ≤ w [ H(z, t, σ) ∧ ∀i < len(σ) (aᵢ = 1 → Θ(qᵢ)) ∧ (aᵢ = 0 → ¬Θ(qᵢ)) ]
```

a `Δ₀(Θ)` formula with two occurrences of `Θ`. By (F2), `ℕ ⊨ ∃x ∃w δ(e, x, w)`
when `Θ` is read as `A` and `U^A(e)↓t`, and every `x` with a witness has
`x ≥ t`. Apply the minimization lemma of `BOOLOS-IS-BUSY-BEAVER-CLASS.md`
§2 with this `δ`. Existence: `μₑ(k̄)` is a true `Σ₁(Θ)` sentence, so
`T ⊢ μₑ(k̄)` by Lemma 1 (this is the only place the old proof used
`Σ₁`-completeness). Uniqueness: proved in `PA⁻` from the shape of `μ`, using
only trichotomy and that `B` and `¬B` contradict, exactly as before. So
`μₑ` `T`-names some `k ≥ t`, and `|μₑ| ≤ 2|δ| + C + 6 log₂(e+2) ≤
a(|Θ| + |p|) + b`. ∎ **[paper]**

The bound is uniform in `Θ`: the oracle's description enters additively, so
the second display follows.

## 4. Theorem 3 (upper bound): a name is a decided singleton

**Theorem 3.** If `φ` `T`-names `m`, then `φ` decides `{m}` in `T`. Hence
there is an absolute constant `c` with `Big_T(n) ≤ BB^{[T]}(n + c)`.

*Proof.* From `T ⊢ ∀x (φ(x) ↔ x = m̄)`: instantiating at `m̄` gives
`T ⊢ φ(m̄)`; instantiating at `ī` for `i ≠ m` and using `PA⁻ ⊢ ī ≠ m̄`
gives `T ⊢ ¬φ(ī)`. So `φ` decides `{m}`. Let `p₀` be the fixed program
"for `i = 0, 1, 2, …` ask whether `i` is in the oracle; halt at the first
yes". With oracle `{m}` it halts after at least `m` steps, and
`|φ| + |p₀| ≤ n + c`. ∎ **[Lean for the first sentence:
`namesIn_decides_singleton` in `RayoBoolos/Decided.lean`; second sentence
paper]**

## 5. Theorem 4: the general theorem

Theorems 2 and 3 together:

**Theorem 4.** For every consistent `T ⊇ PA⁻` (computably axiomatized or
not), with absolute constants `a, b, c`:

```
BB^{[T]}(ℓ)  ≤  Big_T(a·ℓ + b),          Big_T(n)  ≤  BB^{[T]}(n + c).
```

So the naming function of `T` is, up to a linear rescaling, the Busy Beaver
function for machines that may consult any oracle `T` decides, paying for
the oracle's description. **[paper]**

Theorem 3 is nearly a tautology. The content is Theorem 2: deciding an
oracle pointwise is already enough for `T` to verify, and therefore name,
the running time of every machine using it.

## 6. Single-oracle rungs

`BB^{[T]}` mixes all decided oracles. It collapses to one oracle `A` when
`A` is large enough to list `T`'s theorems.

**Theorem 5 (oracle search).** If the set of theorems of `T` is computably
enumerable relative to `Y`, then `Big_T(n) ≤ BB^Y(c·n·log₂(n+2) + c_{T,Y})`.

*Proof.* Theorem 3 of `BOOLOS-IS-BUSY-BEAVER-CLASS.md` relativized: a
program with `φ` hard-wired (`O(n log n)` bits) enumerates the theorems of
`T` using `Y` until it meets `∀x (φ(x) ↔ x = k̄)` for some `k`, then runs `k`
more steps. Consistency makes `k` unique. ∎ **[paper; classical method]**

**Corollary 6 (the conjecture, corrected).** Suppose `T` decides a set `A`
relative to which its theorems are computably enumerable. Then

```
BB^A(ℓ)  ≤  Big_T(aℓ + b_T),          Big_T(n)  ≤  BB^A(c·n·log₂(n+2) + c_T),
```

so `Big_T` is in the growth class of `BB^A`. In particular this holds when
`T` has an axiom set `Ax` that `T` itself decides (take `A = Ax`). **[paper]**

The two known results are the instances:

| Theory | Decided `A` that lists the theorems | Result |
|---|---|---|
| any computably axiomatized `T ⊇ PA⁻` | `∅` (decided by `y ≠ y`) | `Big_T ≈ BB`: report Thms 5–6 (lower bound [Lean]) |
| `PA⁻ + all true Π_k` (or PA, ZFC plus them) | `0^(k)`, decided by its `Σ_k` definition, since `T` proves all true `Σ_k` and `Π_k` sentences | `Big_T ≈ BB^{(k)}`: `MIDDLE-RUNGS.md` Thm 5 |
| `PA + {θᵢ : i ∈ A} + {¬θᵢ : i ∉ A}` for an independent family `θᵢ = Θ(ī)` and any `A ⊆ ℕ` | `A`, decided by `Θ` | `Big_T ≈ BB^A`: any Turing degree is a rung |

The last row needs a computable family of sentences `Θ(ī)` that is
independent over PA (every Boolean combination consistent), which exists
**[classical: Mostowski 1961; see Lindström, *Aspects of Incompleteness*]**.
It shows the rungs are not only the jumps `0^(k)`: every Turing degree `A`
is the rung of some theory.

## 7. Why "relative to the theorems" overshoots by one jump

**Proposition 7.** Under the hypothesis of Corollary 6:

- (a) `Big_T` is computable from `A'`, the halting problem relative to `A`.
- (b) If moreover `T` proves no false `Σ₁(Θ)` sentence, its theorems
  compute `A'`.
- (c) For any `Y` that computes `Big_T`, and any computable `h`,
  `BB^Y(log₂ n + c) > Big_T(h(n))` for all `n`. So `BB^Y` is not in the
  growth class of `Big_T` under any computable rescaling.

*Proof.* (a) "`φ` names something" means "some `k` has `∀x(φ(x) ↔ x = k̄)`
among the theorems", which is `Σ₁` relative to `A`; given a yes, find `k`
by search. So `A'` computes `Big_T`. (b) `U^A(e)` halts iff `T` proves the
`Σ₁(Θ)` sentence "`U^Θ(e)` halts": if it halts, by Lemma 1; if `T` proves
it, by the soundness assumption. (c) The program "compute `Big_T(h(n))`
with oracle `Y`, then run that many steps" has `n` hard-wired, so has
`log₂ n + c` bits. ∎ **[paper; (c) is the classical domination argument]**

So whenever `T`'s theorems compute `Big_T` (always the case under (a) and
(b)), "Busy Beaver relative to `Thm(T)`" is strictly faster than `Big_T` by
any computable rescaling. Concretely:

- **PA** (or any consistent computably axiomatized `T ⊇ PA⁻`): its
  theorems are as hard as the halting problem `0'` **[classical: such `T`
  have creative theorem sets]**, so `BB^{Thm(T)} = BB^{(1)}`, while
  `Big_T ≈ BB^{(0)}`.
- **`PA⁻ + true Π_k`**: it is sound, so by (b) its theorems compute
  `0^(k+1)`, giving `BB^{(k+1)}`, while `Big_T ≈ BB^{(k)}`.

**The obstacle in the original formulation, resolved.** The lower bound
needed `T` to confirm the answers of an oracle for its own theorems. That
is impossible in general: an answer "no, `T` does not prove `σ`" is a
non-provability statement, which `T` cannot confirm. The fix is not a
reflection hypothesis but a smaller oracle: the axioms (or any decided set
that lists the theorems) instead of the theorems. Questions to the axioms
have answers `T` can check one at a time, and the step from axioms to
theorems is a `Σ₁` search that the naming formula can do itself.

## 8. True arithmetic: a limit, not a rung

**Theorem 8.** For `TA = Th(ℕ)`:

- (a) For every `k`, `Big_TA` eventually dominates `BB^{(k)}`.
- (b) `Big_TA` is computable from `TA` (which has the Turing degree of
  `0^(ω)`), so by Proposition 7(c), `BB^{0^(ω)}(log₂ n + c) > Big_TA(h(n))`
  for every computable `h`.
- (c) No set decided by `TA` lists `TA`'s theorems, so Corollary 6 does not
  apply. Instead, by Theorem 4, `Big_TA ≈ BB^{[TA]}`: Busy Beaver over all
  arithmetical oracles, with the oracle's defining formula counted in the
  size.

*Proof.* (a) `TA ⊇ PA⁻ + true Π_{k+1}`, so by Corollary 6 for `k + 1`,
`Big_TA(aℓ + b) ≥ BB^{(k+1)}(ℓ)`, and `BB^{(k+1)}` dominates
`BB^{(k)}` composed with any computable function **[classical]**.
(b) For a sound complete theory, `φ` names something iff `∃!x φ(x)` is in
`TA`, and then `k` is found by asking `φ(0̄), φ(1̄), …`. (c) A set decided by
`TA` is arithmetical; if `TA` were computably enumerable relative to an
arithmetical set it would be arithmetical, contradicting Tarski's theorem.
**[classical]** ∎ **[paper]**

This makes precise the entry "Rung ω: dominates every finite rung
[expected]" in `THE-LADDER.md`: it is now proved, and it sits strictly
below the oracle Busy Beaver for `0^(ω)`.

## 9. Is this known?

Checked: `LITERATURE-SURVEY.md` (all three passes, including Simmons in
full), and searches on 2026-11-24 for provable naming in non-computably
axiomatized theories, oracle Busy Beaver relative to a theory, and strongly
representable sets.

- The ingredients are classical: strong representability (Tarski,
  Mostowski and Robinson 1953), representable sets of complete theories
  (Scott 1962), `Δ₀`-completeness, oracle search, and domination of
  `Y`-computable functions by `BB^Y`.
- We found no statement of Theorem 4, of Corollary 6 for theories that are
  not computably axiomatized beyond the true-`Π_k` case, or of the
  one-jump overshoot. Simmons (arXiv:1809.08676) works with computably
  axiomatized systems and compares them at fixed inputs, not by growth
  class. Aaronson's MathOverflow 34710 question concerns truth naming, the
  case covered by `MIDDLE-RUNGS.md`.
- Suggested wording: "For any consistent theory containing `PA⁻`, the
  provable-naming function is the Busy Beaver function for oracles the
  theory decides. When the theory decides a set from which its theorems can
  be enumerated, it is the Busy Beaver function relative to that set; this
  recovers the computably axiomatized and true-`Π_k` cases. The ingredients
  are classical; we found no earlier statement."

## 10. What is machine-checked

- `RayoBoolos/Decided.lean`: the definition `DecidesIn T Θ A` and
  Theorem 3's first sentence, `namesIn_decides_singleton` (a `T`-name of
  `m` decides `{m}`), for every `T ⊇ PA⁻`; and `DecidesIn.unique` (a
  consistent `T` decides at most one set with a given formula, used for
  `BB^{[T]}` to be well defined). Sorry-free, standard axioms only; full
  `lake build` 1261 jobs, 2026-11-24. **[Lean]**
- Theorem 2 needs oracle machines, which the project's Lean development
  does not have (it uses Mathlib's `Partrec` via Foundation's
  `computable_iff_sigma1`); a Lean version would also need Lemma 1 for a
  formula substituted into a predicate position. Both are listed as
  follow-ups. Theorems 2, 4, 5, Corollary 6, Proposition 7 and Theorem 8
  are **[paper]**.

## 11. Open questions

1. Is there a theory whose naming function is in the growth class of a
   single `BB^Y`, although no set `T` decides lists `T`'s theorems?
2. For which theories does `D(T)` have a largest Turing degree? (For
   complete `T ⊇ PA` this asks when the Scott set of `T` has a top.)
3. Ordering by growth: `Big_T` and `Big_{T'}` are in one class iff
   `BB^{[T]}` and `BB^{[T']}` are; is this the same as `D(T)` and `D(T')`
   having the same Turing degrees, up to uniformity of the descriptions?
