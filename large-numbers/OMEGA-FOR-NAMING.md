# An Omega for provable naming

*2026-11-24, second pass the same evening (§3 carriers, §5 Theorem 6, Lean
for Lemma 0). Each claim is tagged [classical] (a known theorem, cited),
[paper] (proved here, not independently checked), [numeric] (computed by the
script in §9), [Lean] (machine-checked, sorry-free), or [open].*

Question (Ed, via the project chat): pick a formula at random by flipping
coins for its symbols. Let `Ω_T` be the probability that the formula names a
number in theory `T`. Is `Ω_T` Martin-Löf random? Is it Solovay-equivalent
to Chaitin's `Ω` for every `T`?

## 0. Summary in plain language

- `Ω_T` is the same *kind* of number as Chaitin's `Ω`. It can be approximated
  from below, and its bits answer the halting problem. So it is exactly as
  uncomputable as `Ω`, for every consistent theory `T` that a program can
  list (Theorem 1).
- It is **not as random as `Ω`**, under either natural way of flipping coins
  for formulas. Its first `n` bits can be compressed to about `0.70·n` bits
  (fair coin per symbol) or `0.99·n` bits (fair choice among the symbols
  that are grammatical at that point). So `Ω_T` is not Martin-Löf random and
  not Solovay-equivalent to `Ω`. It is strictly Solovay-below `Ω`
  (Theorem 3, Corollary 4).
- What decides this is the **syntax, not the theory**. The compression
  factor is the information rate of the coin process: how many bits of real
  choice each coin flip carries. Formulas are finished objects, and a coin
  process that produces finished objects almost always wastes some of its
  flips. The bounds are the same for every `T`: PA, ZFC, or a consistent
  theory that proves false things.
- `Ω_T` is still partly random. Its first `n` bits cannot be compressed
  below about `0.149·n` bits (fair coin) or `0.279·n` bits (typed choice)
  (Theorem 2, with the better "carriers" of §3). The exact value between
  these and `0.70` / `0.99` is open.
- **No reweighting of the coins rescues randomness.** Even the "critical"
  weighting, which makes the information rate exactly 1, leaves `Ω_T`
  non-random. This holds for every notation produced by a context-free
  grammar with fixed symbol probabilities (Theorem 6, Corollary 7). The
  reason: in any such notation the *length* of a random formula has a
  finite moment of some small positive order, which saves a `log n` in the
  description of `Ω_T↾n`, and by the Miller–Yu theorem even that small
  saving rules out randomness. For `Ω` itself the length of a random
  halting program has no such moment.
- The classical proof that `Ω` is random cannot be copied for formulas, for
  *any* syntax (Proposition 5). A program is read from an endless tape, and
  the machine decides when to stop. A formula's end is fixed by its grammar,
  which cannot know which programs halt.
- The halting-problem half of Theorem 1 (Lemma 0(a, b): "this formula names
  a number iff that program halts", for every consistent `T ⊇ PA⁻`, no
  soundness) is now machine-checked:
  `rayo-lean-boolos/RayoBoolos/OmegaHalting.lean`.
- My going-in guess in the thread was "constant cost per bit gives full
  randomness". That was wrong. Constant cost per bit gives *partial*
  randomness only, with the exponent set by that cost.

## 1. Setting

**Formulas.** These are first-order formulas of arithmetic over `0, 1, +, ×,
=, <`. They are in negation normal form with de Bruijn variables, as in
`rayo-lean-boolos/RayoBoolos/CompactCode.lean`, written in Polish notation.
That file's token for `#i` is unbounded (`14 + i`). Flipping coins needs a
finite alphabet, so here `#i` is written as `↑ⁱ x`: a token `x` for `#0`
and a unary token `↑` for "next variable". This gives 16 tokens:

| sort | tokens (arity) |
|---|---|
| formula | `⊤ ⊥` (0); `= < ≠ ≮` (2 terms); `∧ ∨` (2 formulas); `∀ ∃` (1 formula) |
| term | `0 1` (0); `+ ×` (2 terms); a variable |
| variable | `x` (0); `↑` (1 variable) |

Polish notation is prefix-free: no formula is a proper prefix of another.
Let `F` be the set of all formula token strings. The free variable of a
naming formula is `#0`.

**Two coin processes.** Each gives a weight `ν(φ)` to every `φ ∈ F`, with
`Σ_{φ∈F} ν(φ) ≤ 1`.

- **Uniform (U16).** Each token costs 4 fair coin flips, so
  `ν(φ) = 16^{-|φ|}`. Most coin sequences are not grammatical.
  `ν(F) ≈ 0.1574` [numeric].
- **Typed (TY).** At a formula position, choose one of the 10 formula
  tokens uniformly. At a term position, choose one of `0, 1, +, ×, variable`
  uniformly. At a variable position, choose `x` or `↑` uniformly. So
  `ν(φ) = 10^{-a}·5^{-b}·2^{-c}`. Here `ν(F) = 1`: the process stops with
  probability 1 [numeric].

**Naming.** Let `T` be a consistent theory containing `PA⁻`, as in
`BOOLOS-IS-BUSY-BEAVER-CLASS.md` §1. A formula `φ` *`T`-names* `k` if
`T ⊢ ∀x (φ(x) ↔ x = k̄)`. Then `φ` names at most one `k`, because
`T ⊢ k̄ ≠ k̄'` for `k ≠ k'`. Put

```
N_T = { φ ∈ F : φ T-names some number },     Ω_T = Σ_{φ ∈ N_T} ν(φ).
```

So `M_T : φ ↦ the number φ names` is a partial function on a prefix-free
set, a "prefix-free machine" in the sense of algorithmic information theory,
and `Ω_T` is its halting probability with respect to `ν`.

**Notation.** `U` is a fixed universal prefix-free machine. It is universal
*by adjunction*: for every prefix-free machine `M` there is a string `ρ_M`
with `U(ρ_M q) = M(q)`. `Ω = Σ_{U(p)↓} 2^{-|p|}`. `K` is prefix-free
complexity. `α↾n` is the first `n` binary digits of `α`. A left-c.e. real is
one that is the limit of a computable increasing sequence of rationals.

**One naming formula per program.** Fix a Δ₀ formula `δ(z, x)` saying "`x`
codes a halting computation of `U` on the program with number `z`". This is
[classical]: the Kleene `T`-predicate is Δ₀ under a suitable coding. Put

```
π_p(x)  :≡  ∃y ( y = 1+1 ∧ ∃z ( z = t_p ∧ δ(z, x) ∧ ∀x' < x ¬δ(z, x') ) ),
```

where `t_p` is the Horner term for the number with binary digits `1p`.
`t_p` is built by `t ↦ + × y t b` with `b ∈ {0, 1}`.

**Lemma 0** [(a), (b): Lean, in the form below; (c): paper]. Let `T ⊇ PA⁻`
be consistent.

- (a) If `U(p)↓` and `c` is the least code of its computation, then `π_p`
  `T`-names `c`, and `c` is at least the running time.
- (b) If `U(p)↑`, then `π_p ∉ N_T`.
- (c) Writing `π_p` takes `|p|` Horner steps of 5 tokens each, plus a
  constant. (Under `∃y ∃z`, `y` is `#1` = `↑ x`.) So
  `ν(π_p) ≥ 2^{-c·|p| - d}` with `c = 20` for U16 and
  `c = 4·log₂5 + 2 ≈ 11.29` for TY. §3 gives much better carriers.

*Proof.* (a) The existence half is a true Σ₁ sentence, so `T` proves it.
Uniqueness follows from the least-number clause and trichotomy, exactly as
in the minimization lemma of `BOOLOS-IS-BUSY-BEAVER-CLASS.md` §2. (b) If
`T ⊢ ∀x(π_p(x) ↔ x = k̄)`, then `T ⊢ π_p(k̄)`. But `PA⁻` proves
`t_p = p̄'` and `1+1 = 2̄`, and it refutes the false Δ₀ sentence `δ(p̄', k̄)`,
so `PA⁻ ⊢ ¬π_p(k̄)`. That makes `T` inconsistent. This part needs only
consistency, not Σ₁-soundness: that is why `δ` is Δ₀ in `x`, unlike the Σ₁
formula `μ` of the earlier note. (c) Count tokens. ∎

*As mechanized* (`OmegaHalting.lean`, sorry-free, standard axioms only). The
Lean version avoids a hand-built Kleene predicate. It takes any Σ₁ graph
`θ(v, n)` of a partial recursive function, bounds its existentials by a new
variable `s` (`bd θ`, from `Minimization.lean`), and uses

```
haltGraph θ (s, x)  :≡  (∃ y ≤ s, bd θ (y, x, s)) ∧ ∀ s' < s, ∀ y ≤ s', ¬ bd θ (y, x, s'),
```

"`s` is the least bound at which `θ(·, x)` has a bounded witness". Every
quantifier is bounded, so it is Δ₀ (`haltGraph_delta0`). `haltName θ n` is
`haltGraph θ (·, n̄)`. Proved:

- `namesIn_haltName_iff`: for consistent `T ⊇ 𝗣𝗔⁻`, `haltName θ n` names
  some number in `T` iff `∃ v, θ(v, n)` in `ℕ`.
- `halting_iff_named`: there is one `θ` such that, for every such `T` and
  every Mathlib program code `e`, `e` halts on input 0 iff `haltName θ e`
  `T`-names a number.
- `named_not_computable`: so `e ↦ [haltName θ e names something in T]` is
  not computable, for every such `T`.

Still paper: that `e ↦ ⌜haltName θ e⌝` is computable (it substitutes a
numeral), the real number `Ω_T`, and the measure bookkeeping of Theorem 1.

## 2. Theorem 1: Ω_T is a halting-problem-complete left-c.e. real

**Theorem 1** [paper]. Let `T ⊇ PA⁻` be consistent and recursively
enumerable, and use either coin process. Then `Ω_T` is left-c.e. and
`Ω_T ≡_T 0′`.

*Proof.* `N_T` is c.e.: search proofs. `ν` is computable. So the partial
sums over the enumeration of `N_T` increase to `Ω_T`, and `Ω_T ≤_T 0′`.
For the other direction, given `Ω_T` to precision `2^{-m}`, enumerate `N_T`
until the partial sum is within `2^{-m}` of `Ω_T`. After that, no formula
with `ν(φ) ≥ 2^{-m}` is still missing. So `Ω_T` decides membership in
`N_T`. By Lemma 0(a, b), `π_p ∈ N_T ⟺ U(p)↓`, so `Ω_T` decides halting. ∎

As far as Turing degree goes, every such `T` gives the same answer, and so
does `Ω`.

## 3. Theorem 2: Ω_T is partially random (a Chaitin-style lower bound)

**Theorem 2** [paper]. Same hypotheses as Theorem 1, with `c, d` from
Lemma 0(c). For all `n`,

```
K(Ω_T↾n) ≥ (n − d)/c − O(1).
```

So the effective dimension of `Ω_T` (`liminf K(α↾n)/n`) is at least `1/c`.
With Lemma 0(c) that is `1/20` for U16 and `0.089` for TY. With the carriers
below, it is `0.149` and `0.279`.

*Proof.* Chaitin's argument, run through `N_T`. From `σ = Ω_T↾n`, enumerate
`N_T` until the partial sum exceeds `0.σ`. Every `φ` with `ν(φ) ≥ 2^{-n}`
has then appeared. Let `ℓ = ⌊(n − d)/c⌋`. For every halting `p` with
`|p| ≤ ℓ`, `π_p` has appeared together with the number it names. That
number bounds the running time of `p`. So we know `U(p)` for every
`|p| ≤ ℓ`, and we can output the first string `y` that no such program
outputs. Then `ℓ < K(y) ≤ K(σ) + O(1)`. ∎

**Better carriers** [paper + numeric]. The proof needs only *some*
computable injective way to write every program `p` into a naming formula of
weight at least `2^{-c|p| - d}`. Three improvements on binary Horner:

1. *Put the base variable innermost.* Bind `∃z ∃v_m … ∃v_1 ∃y`, with
   `z = t ∧ y = b ∧ v_j = j+1 ∧ δ(z, x) ∧ …`. Inside `t`, `y` is `#0`, a
   single token `x`.
2. *Make digit 0 cheap.* A Horner step for digit 0 is `× x t` (2 tokens),
   and for digit 1 it is `+ × x t 1` (4 tokens).
3. *Use bound variables as extra digits.* `v_j = #j` costs `j+1` tokens
   (`↑ʲ x`) and stands for digit `j+1`, in base `b = m+2`. A step costs
   `j+4` tokens.

The steps form a code with unequal letter costs. Let `r` be the root of
`Σ_steps 2^{-r·cost} = 1`. By the renewal theorem the number of step
sequences of cost at most `C` is at least `K·2^{rC}`. So every program of
length `ℓ` can be written, injectively and computably, with cost at most
`ℓ/r + O(1)`. The machine `U'` that the formula runs first decodes the
base-`b` digits of `z` back into `p`. That changes `δ` by a constant.

| process | cost of a step (coin bits) | rate `r` (program bits per coin bit) | was |
|---|---|---|---|
| U16 | digit 0: 8; digit 1: 16; `v_j`: `4(j+4)` | **0.1493** (0.1488 with `m = 10`) | 0.05 |
| TY  | digit 0: `log₂ 50`; digit 1: `log₂ 1250`; `v_j`: `log₂ 1250 + j + 1` | **0.2791** (0.2688 with `m = 10`) | 0.089 |

*What does not help: term values.* Closed terms over `0, 1, +, ×` take very
few distinct values. With at most 15 tokens they take only 18 values (0 to
18 except 17, script in §9). So digits written as closed terms carry about
`log₂ s` bits in `s` tokens, which is useless. The cheap carriers are
syntactic choices that the decoder reads off as base-`b` digits.

The upper bound `γ*` of Theorem 3 is the information rate of *all*
formulas. The carriers above use only Horner terms. A carrier reaching `γ*`
would have to make almost every syntactic choice count. Whether one exists
is Open problem B.

## 4. Theorem 3: the syntax caps the randomness

**Theorem 3 (entropy bound)** [paper; the argument is Tadaki's, see §8].
Let `F` be any countable set with a computable weight `ν` (rational values),
and let `N ⊆ F` be c.e. Suppose `γ ∈ (0, 1]` is rational and

```
C_γ := Σ_{φ ∈ F} ν(φ)^γ < ∞.
```

Then `α = Σ_{φ∈N} ν(φ)` satisfies `K(α↾n) ≤ γ·n + O(log n)`.

*Proof.* Put `β = Σ_{φ∈N} ν(φ)^γ ≤ C_γ`. It is left-c.e. along the same
enumeration of `N`. Given `β↾m`, where `m` and the integer part of `β` cost
`O(log m)` extra bits, enumerate `N` until the partial sum `β_s` reaches
`0.β↾m`. The elements of `N` still to come then satisfy
`Σ ν(φ)^γ < 2^{-m}`. Since `1/γ ≥ 1`, `Σ a_i^{1/γ} ≤ (Σ a_i)^{1/γ}` for
`a_i ≥ 0`, so the elements still to come satisfy `Σ ν(φ) < 2^{-m/γ}`. So
`α_s` is within `2^{-m/γ}` of `α`. Take `m = ⌈γn⌉ + 1`: this pins down
`α↾n` up to one carry bit. Total cost: `γn + O(log n)`. ∎

So the randomness of `Ω_T` is capped by the **critical exponent**
`γ* = inf{γ : C_γ < ∞}` of the coin process. That is its information rate:
how many bits of real choice each coin flip carries, on average, on the
formulas that matter. For a fair-coin code it is `log₂(growth rate of
#formulas of length L)` per coin.

**The two processes** [numeric, script in §9]. Both are algebraic systems.
Solve `V = w_v(1+V)`, then the quadratic for `T`, then the quadratic for
`F`. Find the smallest `γ` at which a discriminant reaches 0.

| process | `γ*` | where it comes from |
|---|---|---|
| U16 | `log₂(7.0085)/4 ≈ 0.7023` | formulas of length `s` grow like `7.0085^s`, but each costs `16^s` |
| TY  | `≈ 0.9894` | the process is subcritical: the mean number of term children is `0.8 < 1`, so long formulas are exponentially rare |

**Corollary 4** [paper + numeric]. For every consistent r.e. `T ⊇ PA⁻`:

- (a) Under U16: `K(Ω_T↾n) ≤ 0.703·n + O(log n)`. Under TY:
  `K(Ω_T↾n) ≤ 0.990·n + O(log n)`. So `Ω_T` is **not** Martin-Löf random,
  and its packing (strong) dimension is at most `γ*`.
- (b) `Ω_T <_S Ω`, strictly. `≤_S` holds because `Ω` is Solovay-complete
  among left-c.e. reals (Solovay 1975). `≱_S` holds because, by Kučera and
  Slaman (2001), a left-c.e. real Solovay-above `Ω` is random. So the
  answer to "Solovay-equivalent to `Ω` for every `T`?" is **no, for no `T`**.
- (c) Combining with Theorem 2 and the carriers of §3: under U16,
  `0.149 ≤ dim Ω_T ≤ Dim Ω_T ≤ 0.703`. Under TY,
  `0.279 ≤ dim Ω_T ≤ Dim Ω_T ≤ 0.990`. These bounds are independent of `T`.

*Why the theory cannot help.* Theorem 3 holds for *every* c.e. subset of
`F`. A stronger theory names with more formulas, but they all come out of
the same supply, and the supply has the wrong shape. This is the familiar
pattern from the rest of the project, that theory strength only moves
constants, but here it shows up in a sharper form: the *exponent* is fixed
by the syntax alone.

## 5. Why Ω's randomness proof does not transfer, and what is left open

Chaitin's proof that `Ω` is random gives each program `p` its own share,
`2^{-|p|}`. The natural analogue for formulas: computably assign to every
program `p` a finite set `S_p ⊆ F`, pairwise disjoint, that lies in `N_T`
when `p` halts and has `ν(S_p) ≥ 2^{-|p|-d}`. If this existed, a direct
Solovay reduction would give `Ω ≤_S Ω_T`. It cannot exist, for any syntax:

**Lemma 5a** [paper]. No decidable set `D ⊇ dom U` has
`Σ_{p∈D} 2^{-|p|} < ∞`.

*Proof.* Build a c.e. prefix-free `A` as follows. For each pair `(e, b)`,
reserve a fresh cone `[σ_{e,b}]`. Consider the strings in that cone with
lengths from `|σ|` to `|σ| + 2^{b+|σ|}`. Each length level has Kraft sum
`2^{-|σ|}`, so together they have Kraft sum more than `2^b`. Run the `e`-th
partial computable 0/1 function on them. If it halts on all of them and
some string is not accepted, put the first such string into `A`. Now let `D`
be decidable with Kraft sum at most `2^b`, and let `M` be the machine with
domain `A`. Then `D' = {q : ρ_M q ∈ D}` is decidable with Kraft sum at most
`2^{b+|ρ_M|}`, so `D' = D_e` for some `e` with bound `b' = b + |ρ_M|`, and
`A` contains a string outside `D'`. So `dom U ⊄ D`. ∎

**Proposition 5** [paper]. For any `F` with computable rational `ν`, any
`d`, and any computable `p ↦ S_p` (finite, pairwise disjoint), there is a
halting `p` with `ν(S_p) < 2^{-|p|-d}`.

*Proof.* `D = {p : ν(S_p) ≥ 2^{-|p|-d}}` is decidable, and
`Σ_D 2^{-|p|} ≤ 2^d Σ_p ν(S_p) ≤ 2^d`. Apply Lemma 5a. ∎

For `Ω` itself the sets `S_p = {p}` work only because programs are *not* a
prefix-free family of finished objects. Every string, halting or not, gets
its share `2^{-|p|}`, and the shares sum to infinity. Formulas have no such
slack.

Proposition 5 rules out only the per-program route. Randomness needs only
the aggregate: `cΩ_T = Ω + β` for some left-c.e. `β` (Downey, Hirschfeldt
and Nies 2002). Theorem 3 says this needs `γ* = 1`. That holds for
*critical* (Boltzmann) weights: give each token the probability that makes
the branching process critical, so that `Σ ν^γ = ∞` for every `γ < 1`. The
first pass left this case open. It is now closed, negatively.

**Theorem 6 (a moment of the length rules out randomness)** [paper].
Let `F` be countable with computable rational weights `ν ≤ 1/2`,
`Σ_F ν ≤ 1`. Suppose that for some rational `a ∈ (0, 1/2]`

```
Σ_{φ ∈ F} ν(φ) · (log₂ 1/ν(φ))^a < ∞.                      (★)
```

Then for every c.e. `N ⊆ F`, `α = Σ_N ν` satisfies
`K(α↾n) ≤ n − a·log₂ n + K(n) + O(1)`, and `α` is **not** Martin-Löf random.

*Proof.* Put `g(x) = x·(log₂ 1/x)^a`. On `(0, 1/2]` it is increasing
(its derivative is `L^{a−1}(L − a/ln 2)` with `L = log₂ 1/x ≥ 1 > a/ln 2`), and
`g(x)/x` is decreasing, so `g⁻¹(y)/y` is increasing and `g⁻¹` is
superadditive. Let `β = Σ_N g(ν(φ))`, which is finite by (★) and left-c.e.
Given `n` (`K(n)` bits) and `β↾m` (`m` bits, plus a constant for the integer
part), with `m = n + 2 − ⌊a log₂ n⌋`, enumerate `N` until `β_s ≥ 0.β↾m`. The
elements still to come have `Σ g(ν) < 2^{-m}`, so by superadditivity
`Σ ν ≤ g⁻¹(2^{-m})`. If `x = g⁻¹(y)` with `y ≤ 1/2`, then `x ≤ y` and so
`log₂(1/x) ≥ log₂(1/y)`, which gives `x ≤ y/(log₂ 1/y)^a`. Hence the tail
is at most `2^{-m}/m^a ≤ 2^{-n-1}` for large `n`, and `α↾n` follows with one
carry bit. Total length: `n − a log₂ n + K(n) + O(1)`.

Now use the **Miller–Yu ample excess theorem** [classical; Miller and Yu
2008]: if `α` is ML-random then `Σ_n 2^{n − K(α↾n)} < ∞`. Here
`2^{n − K(α↾n)} ≥ 2^{-O(1)}·n^a·2^{-K(n)}`, and since
`K(n) ≤ log₂ n + 2 log₂ log₂ n + O(1)`, this is at least
`n^{a−1}/(log₂ n)²` up to a constant. That sum diverges for every `a > 0`. ∎

**Corollary 7 (no context-free notation gives a random Omega)** [paper;
the analytic-combinatorics step is cited, not re-proved]. Let the formulas
be the words of an unambiguous context-free grammar, generated by choosing
each production with a fixed positive probability. This covers U16, TY,
every critical reweighting, and Polish notation for any finite language.
Then (★) holds for some `a > 0`, so `Ω_T` is not ML-random, for every `T`.
In particular it is never Solovay-equivalent to `Ω`.

*Proof.* Each token has probability at least some `w > 0`, so
`log₂ 1/ν(φ) ≤ |φ| log₂(1/w)`, and it is enough that the length of a random
formula has a finite `a`-th moment. Let `m_s` be the total weight of
formulas with `s` tokens and `M(z) = Σ m_s z^s`. By Chomsky–Schützenberger,
`M` is algebraic. Its coefficients are nonnegative and `M(1) ≤ 1`.

- If the radius of convergence exceeds 1, the `m_s` decay exponentially.
- Otherwise `M` is bounded on the closed unit disk. At each of its finitely
  many singularities on the circle, its Newton–Puiseux expansion has a
  positive non-integer leading singular exponent `r_j` (algebraic functions
  have no logarithmic terms). Transfer theorems give `m_s = O(s^{-1-r})`
  with `r = min r_j > 0` (Flajolet and Sedgewick, *Analytic Combinatorics*,
  Thm VII.8 with §VI). So `Σ m_s s^a < ∞` for `a < r`.

In the critical case `r = 1/2`, so any `a < 1/2` works. ∎

*The contrast with `Ω`.* Read in reverse, Theorem 6 says that for `Ω`
itself, `Σ_{U(p)↓} 2^{-|p|}·|p|^a = ∞` for every `a > 0`. The length of a
random halting program has no positive moment at all. Programs can afford
this because the machine, not a grammar, decides where they end.

**What is left** [open]. An `Ω_T` could only be random under a notation
that violates (★) for every `a > 0`. An example would be a formula preceded
by a length header drawn with probability about `1/(L log² L)`, which brings
back a program-like stopping rule. Proposition 5 still applies there, so a
proof of randomness would need aggregate methods. Whether any such notation
works is open. It is not a natural notation for formulas.

**Open problem B** [open]. What is `dim Ω_T` for U16 and TY exactly? It lies
in `[0.149, 0.703]` and `[0.279, 0.990]`. Is it `γ*`, which would mean some
carrier of program bits uses the syntax at full rate? Does it depend on
`T`?

## 6. Side cases

- **Inconsistent `T`** [paper]. Every formula names every number, so
  `N_T = F` and `Ω_T = ν(F)`. That is a computable algebraic number:
  `≈ 0.1574` (U16) or `1` (TY).
- **Consistent but Σ₁-unsound `T`** [paper; Lean for Lemma 0]. Nothing
  changes. Lemma 0 and Theorems 1 to 3 used only consistency. That is why
  `π_p` is built from a Δ₀ matrix. `OmegaHalting.lean` assumes only
  `[Entailment.Consistent T]`.
- **True arithmetic `TA`** [paper]. Here `N_TA` is the set of formulas
  defining a singleton in `ℕ`. The formula `x = 0 ∧ σ` is in `N_TA` iff `σ`
  is true, so `Ω_TA ≥_T 0^{(ω)}`. Also `N_TA ≤_T 0^{(ω)}`, and the tails of
  `ν(F)` are computable, so `Ω_TA ≡_T 0^{(ω)}`. Theorem 3 relativizes: `N`
  only needs to be c.e. in the oracle. So
  `K^{0^{(ω)}}(Ω_TA↾n) ≤ γ*·n + O(log n)`: `Ω_TA` is not
  `0^{(ω)}`-random. Compare Becher, Daicz and Chaitin's relativized `Ω^X`,
  which *is* `X`-random.
- **The `Π_k` truth rungs** of `MIDDLE-RUNGS.md` [paper, sketch]. Take `T`
  to be `PA⁻` plus all true `Π_k` sentences. Then `N_T` is c.e. in
  `0^{(k)}`. A true `Σ_{k+1}` sentence is provable and a false one is not,
  so `Ω_T ≡_T 0^{(k+1)}`. Relative to `0^{(k)}`, `Ω_T` is left-c.e. and has
  dimension at most `γ*`. So each rung of the ladder has its own Omega, of
  the matching Turing degree, and the same syntax cap.

## 7. Relation to the rest of the project

- The ladder (`THE-LADDER.md`) ranks schemes by *how fast* they name.
  `Ω_T` packs the same naming facts into one real. Theorem 1 says the real
  sits at the same Turing degree as the rung. Theorem 3 says that within a
  degree, its *randomness* is a property of the notation.
- Theorem 2 uses the same "a short formula names a running time" device as
  the Busy Beaver lower bound (`BOOLOS-IS-BUSY-BEAVER-CLASS.md` Theorem 2).
  It is the information-theoretic face of the same fact.
- `COMPLEXITY-AND-ENTROPY.md` §3 says that `n` bits of `Ω` settle naming up
  to size `n`. That is still true for `Ω`. This note says the converse
  packing, naming facts back into a random real, loses a constant factor
  for any fixed notation.

## 8. Literature

- Chaitin (1975, 1987): `Ω` and its randomness. Solovay (1975, unpublished
  manuscript): Solovay reducibility; `Ω` is complete. Calude, Hertling,
  Khoussainov and Wang (2001): `Ω`-like reals are random. Kučera and
  Slaman (2001): every left-c.e. random is Solovay-complete. Downey,
  Hirschfeldt and Nies (2002): `β ≤_S α` iff `cα = β + γ` for some
  left-c.e. `γ`.
- **Tadaki** (2002, "A generalization of Chaitin's halting probability Ω
  and halting self-similar sets", Hokkaido Math. J.; and arXiv:0805.2691,
  Theorem 2.10). `Ω(D) = Σ_{p∈dom U} 2^{-|p|/D}` is "weakly Chaitin
  `D`-random and `D`-compressible". Theorem 3 above is the compressibility
  half of his argument, applied to an arbitrary weighted c.e. set. The
  observation that a *formula syntax* forces such a weighting does not
  appear in the sources read.
- Miller and Yu (2008, Trans. AMS, "On the initial segment complexity and
  degrees of randomness"): the ample excess lemma used in Theorem 6.
  Flajolet and Sedgewick (2009), *Analytic Combinatorics*, Ch. VI–VII:
  coefficient asymptotics of algebraic functions, used in Corollary 7.
- Becher, Daicz and Chaitin (2001): relativized `Ω`. Becher, Figueira,
  Grigorieff and Miller (2006, JSL), "Randomness and halting
  probabilities": `Ω_U[X]` for sets of outputs, again on program space.
- Salehi (arXiv:2310.14807) discusses what can count as a halting
  probability, and weightings of sentences tied to Chaitin's heuristic
  principle. It does not define a probability of provable naming and
  proves no randomness result (read via summary; checked only for that).
- Searched for, not found: a "probability that a random formula defines
  (or provably defines) a number". Calude and Jürgensen (2005) study the
  density of provable sentences, not this. Treat the novelty claim as
  unverified until a specialist has looked.

## 9. Numerics

`omega_growth.py`, in this directory, recomputes `ν(F)` and `γ*` for both
processes from the closed-form algebraic system. It also recomputes the
carrier rates of §3 and the distinct values of small closed terms. It cross-checks U16 by
counting formulas exactly up to 300 tokens. The ratio of successive counts
at 300 is 6.9735, which matches `7.0085·(1 − 3/(2s))`, the expected
`s^{-3/2}` correction.

## 10. What to check

1. Lemma 0(c) with the §3 carriers: the token counts, and that the decoder
   `U'` is a fixed machine. Lemma 0(a, b) are in Lean.
2. Theorem 3's carry-bit and `O(log n)` bookkeeping.
3. Lemma 5a: the diagonal search across cones is uniform. Check that a
   partial `e` that never halts on some candidate only stalls its own cone.
4. The novelty search in §8.
5. Corollary 7's appeal to Puiseux plus transfer for *periodic* or
   multi-singularity algebraic series. It needs only an `O(s^{-1-r})` upper
   bound, which survives finitely many singularities on the circle.
6. Theorem 6's use of Miller–Yu. Only the easy direction is needed: random
   implies a finite sum.
