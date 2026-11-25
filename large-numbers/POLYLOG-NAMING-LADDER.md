# Polylog budgets: placing naming problems between P and NP

*Written 2026-11-24. Follows `PROOF-BUDGETS-AND-COMPLEXITY.md` (§1, §4)
and `P-VS-NP-LIMITS.md` (§4). Question: if the naming budget is about
`log n`, or `(log n)^j`, where do the problems "find a cheap name" and
"find the record" sit between P and NP? Do they land on the classes
`β_j` of problems that need only `(log n)^j` guessed bits, and is there
a natural naming problem that climbs those classes one rung at a time?*

Tags as elsewhere: **[classical]** known result, cited; **[paper]**
argued in full here; **[sketch]** argued in outline, details not
checked; **[open]**.

Notation. `k` is always the number being named, as in the earlier notes,
and `n = log₂ k` is its length in bits. Rungs of the ladder are indexed
by `j`, so the classes are `β_1, β_2, …`. `N` is the total length of an
input. Logarithms are base 2.

---

## 0. The answer in plain language

1. **A budget on the proof does not work as stated.** A proof that a
   formula names `k` has to write `k` down (the "writing the answer caps
   the answer" point of the proof-budgets note). So the proof is at
   least as long as the input. A proof budget of `log N` symbols leaves
   no yes-instances at all, unless the input is padded with junk to make
   `N` huge. The budget has to go on the *name*, with the proof checked
   or computed in polynomial time, or the input has to be padded. We
   treat both versions. **[paper]**

2. **Budget on the name, proof computed: the clean ladder.** In the
   binary toy arithmetic of `NAMING-RECORDS-SMALL-SYSTEM.md`, the proof
   is just the calculation, so it follows from the name. Ask: "is there
   a name of at most `s` symbols for `k` whose calculation takes at most
   `m` symbols?" With `s ≤ c·log N` there are only polynomially many
   names, and brute force runs in polynomial time: the problem is in P.
   With `s ≤ (log N)^j` the problem needs only `O((log N)^j)` guessed
   bits, so it is in `β_j`. **[paper]**

3. **Is that ladder problem hard for its rung? We don't know.** It has
   the same shape as the circuit-size problem MCSP and the time-bounded
   Kolmogorov problem: the question is whether *some* short description
   exists, and every known way of proving such problems hard runs into
   the same wall. We expect the honest status to stay **[open]**.

4. **With a symbol supplied in the input, completeness is easy.** Let
   the name use one extra function symbol `f` whose meaning is a circuit
   given in the input. Then "is there a name of size `(log N)^j` that
   reaches a target" is complete for `β_j`, for every `j`. That is a
   problem complete at every rung, but for a cheap reason: the circuit
   carries all the difficulty, and the arithmetic plays no part.
   **[paper]**

5. **Under the exponential time hypothesis (ETH) the rungs are all
   different.** ETH says 3-SAT on `n` variables needs time `2^{δn}`.
   A standard padding argument shows that ETH makes
   `P = β_1 ⊊ β_2 ⊊ β_3 ⊊ …`. So the problems in item 4 really do climb
   one rung at a time under ETH. Nothing here separates any classes
   without such an assumption. **[paper, standard argument]**

6. **The padded proof-budget version.** If you pad the input, the
   literal question "is there a proof of at most `(log N)^j` symbols?"
   makes sense and sits in `β_j`. Deciding it in polynomial time is the
   same as finding short proofs (or short naming proofs) in time
   `2^{O(m^{1/j})}` for budget `m`, a subexponential algorithm. Under
   ETH this family climbs without bound, at least one rung for every two
   steps (strictly, if satisfiability has quasi-linear proofs, which is
   open). But it is *not* complete for its rung, under a nondeterministic
   cousin of ETH: completeness would let you squeeze many satisfiability
   instances into one tiny one, and the Fortnow–Santhanam argument turns
   that into a fast way to certify unsatisfiability. **[paper, under
   the stated assumptions]**

7. **Budget on the formula in full first-order arithmetic: not on the
   ladder.** In a theory like PA a short formula can name `k` only via a
   proof that has to be found, and that proof is long. The guessing
   lives in the proof, so a short formula does not limit the
   guessing. This version stays NP-type at every budget. It matches the
   proof-budgets note: calculation names behave like Levin's `Kt`,
   proof names like the nondeterministic `KNt`. The `β_j` ladder lives
   on the `Kt` side. **[paper]**

In short: (a) yes, an `O(log N)` budget on the name gives problems in P
by brute force; (b) a `(log N)^j` budget on the name gives problems in
`β_j`, but completeness is only proved for the version with a symbol
from the input; (c) that version is complete at every rung and, under
ETH, climbs strictly. None of this says anything about P versus NP.

---

## 1. Limited nondeterminism

**Definition. [classical]** `β_j` is the class of languages accepted by
a nondeterministic Turing machine that runs in polynomial time and makes
`O((log N)^j)` binary guesses on inputs of length `N`. Equivalently,
`L ∈ β_j` iff there are a polynomial-time relation `R` and a constant
`c` with

    x ∈ L  ⇔  ∃y ( |y| ≤ c·(log|x|)^j  ∧  R(x, y) ).

The classes were studied by Kintala and Fischer (1980) for general guess
bounds. The name `β_j` and the polylog hierarchy are from Díaz and Torán
(1990). Buss and Goldsmith (1993) studied a finer quasi-linear version,
`N^m P_l`.

Basic facts **[classical]**:

- `β_1 = P`: try all `2^{c log N} = N^c` guess strings.
- `β_1 ⊆ β_2 ⊆ … ⊆ NP`, and `β_j ⊆ DTIME(2^{O((log N)^j)})`, quasi-polynomial
  time.
- **Generic complete problem.** `CSAT_j`: circuits `C` of size `N` with
  at most `(log N)^j` inputs that have a satisfying input. It is
  `β_j`-complete under polynomial-time many-one reductions. (Given
  `L ∈ β_j` with relation `R`, map `x` to the circuit `y ↦ R(x, y)`,
  padded so its size `N'` satisfies `c(log|x|)^j ≤ (log N')^j`.) Buss
  and Goldsmith give the quasi-linear version (their Theorem 6) and
  several less generic complete problems (their Theorems 9 and 10).
- Natural problems inside `β_2` include tournament dominating set and
  computing the VC dimension (Papadimitriou and Yannakakis 1996, the
  classes LOGNP and LOGSNP).

**Proposition 1 (ETH separates the ladder). [paper, standard padding
argument]** If ETH holds, then `β_j ⊊ β_{j+1}` for every `j ≥ 1`. In
particular `P ⊊ β_2`.

*Proof.* Suppose `β_{j+1} ⊆ β_j`. Let

    PAD = { (φ, 1^N) : φ a satisfiable 3-CNF with v variables,
                        N = 2^{⌈v^{1/(j+1)}⌉} }.

`PAD ∈ β_{j+1}`: the guess is an assignment, `v ≤ (log N)^{j+1}` bits,
and checking takes time polynomial in `N` (for large `v`, `N` exceeds
`|φ|`, so the input length is `Θ(N)`). By assumption `PAD ∈ β_j`, so
there are constants `a, c` and a deterministic algorithm running in time
`2^{c(log N)^j}·N^a` by trying all guess strings. Now
`(log N)^j = O(v^{j/(j+1)})` and `log N = O(v^{1/(j+1)})`. To decide a
3-CNF `φ`, write out `(φ, 1^N)` in time `O(N)` and run the algorithm.
The total time is `2^{O(v^{j/(j+1)})} = 2^{o(v)}`, against ETH. ∎

The case `P ≠ β_2` also follows from a known equivalence (Flum and
Grohe, see §7): ETH rules out `P = NP[ι(n)·log n]` for every unbounded
`ι`. We did not find the full strict ladder stated in what we read.

The same argument shows: under ETH, a `β_{j+1}`-complete problem is not
in `β_j`. This is all we need for "climbs one rung at a time".
Without ETH the ladder might collapse. Buss and Goldsmith (Theorem 12)
give an oracle relative to which their whole hierarchy collapses to P
and yet P ≠ NP, so a collapse would not by itself say anything about P
versus NP.

---

## 2. The catch: proofs write the answer

**Lemma 2. [paper]** In the setting of the proof-budgets note (§1,
binary target), every proof `π` of `∀x (φ(x) ↔ x = bin(k))` contains the
term `bin(k)`, so `|π| ≥ |bin(k)| ≥ log₂ k`. In the binary toy
arithmetic B, the evaluation proof of a name of `k` ends in the numeral
for `k`, so its length is at least `n + 1`.

*Proof.* The conclusion is a line of the proof, and contains the
numeral. ∎

So if `k` is part of the input, which it must be for "does `k` have a
cheap name?", then every proof has length at least about the input
length `N`. A proof budget of `(log N)^j` gives no yes-instances, unless
the input contains about `2^{n^{1/j}}` symbols of padding. There are two
ways to make the question meaningful:

- **Budget on the name** (§3, §4). The name is short. The proof is
  polynomially long but either computed from the name (toy arithmetic,
  programs) or not limited in its guessing at all (first-order theories,
  §6).
- **Padding** (§5). Append `1^N` to the input and allow proofs of length
  `(log N)^j`. Then everything meaningful in the input has polylog size.

The combined Levin-style cost `D = |name| + log₂|proof|` does not fit
either. `D ≤ c·log n` bounds the proof by `n^c`, which is polynomial,
and the size of the name by `c·log n`, which is fine: that version is in
P (Proposition 3(a)). But `D ≤ (log n)^j` allows proofs of length
`2^{(log n)^j}`, quasi-polynomial, so for `j ≥ 2` checking a single name
already takes too long for `β_j`. The ladder needs a separate polynomial
bound on the proof, as in time-bounded Kolmogorov complexity `K^t` with
`t` a polynomial, rather than Levin's `Kt`.

---

## 3. Calculation names: membership

Use the binary toy arithmetic B of `NAMING-RECORDS-SMALL-SYSTEM.md` §1:
symbols `0` (arity 0), `D0, D1, S` (arity 1), `+, ·, ^` (arity 2), the
rewrite rules listed there, and the **evaluation proof**: the fixed
rewriting order used in the tables. A name's evaluation proof is
determined by the name. Its length is the total number of symbols in the
chain of terms.

> **CalcName.** Input: `k` in binary, a size bound `s`, a proof budget
> `m` in unary. Question: is there a closed term `τ` with `|τ| ≤ s` whose
> evaluation proof has length `≤ m` and ends in the numeral for `k`?
>
> **CalcName_j** is the same with the extra requirement
> `s ≤ (log N)^j`, where `N` is the input length (instances that break
> it are rejected).

**Proposition 3. [paper]**

(a) `CalcName_1 ∈ P`, and for each fixed `c` the problem
"`D_B(k) ≤ c·log₂ n`" is in P, where `D_B` is the combined cost in B.

(b) `CalcName_j ∈ β_j` for every `j`.

(c) Without the size restriction, `CalcName ∈ NP`.

*Proof.* Terms are written in prefix (Polish) notation over the 7
symbols. Since arities are fixed this is uniquely readable, and a term
of size `s` is a string of length `s`, so `3s` bits.

*Checking one candidate.* Given `τ` and `m`, generate the evaluation
proof one step at a time. Each step finds the next redex in the fixed
order and rewrites it, in time polynomial in the current term size, and
the current term size is at most the running total. Stop with "no" as
soon as the running total exceeds `m`. If the chain ends in a numeral
within budget, compare it with `k`. This takes time polynomial in `m`,
which is at most `N` because `m` is in unary.

(a) There are fewer than `7^{s+1}` strings of length at most `s`. With
`s ≤ log N` that is at most `7·N^{log₂ 7}`, polynomially many; check each.
For `D_B(k) ≤ c·log₂ n`: any witness has size `≤ c·log n` and proof
length `≤ 2^{c log n} = n^c`, so run the same search with `s = c·log n`
and `m = n^c`. (The input is `k`, of length about `n`.)

(b) Guess the `3s ≤ 3(log N)^j` bits of `τ`, then check it.

(c) Guess `τ` (`|τ| ≤ s ≤ m`, since the first line of the proof is `τ`)
and check it. ∎

**Remark (same for programs).** Replace B by programs for a fixed
universal machine, with "evaluation proof" meaning the run. This is
`MINKT`, the decision version of `K^t`: does `x` have a program of
length `≤ s` printing it in `≤ t` steps, `t` in unary? The same proof
puts `MINKT` with `s ≤ (log N)^j` in `β_j`, and with `s ≤ c·log N` in P.
By Proposition 5 of the proof-budgets note, first-order naming with
calculation-style proofs is within constant factors of `Kt`, so
`CalcName` is the arithmetic, toy-sized version of `MINKT`.

**Records.** "Find the record" (the largest `k` nameable within size `s`
and proof budget `m`) is a function problem. For `s ≤ c·log N` it is in
polynomial time by the same enumeration. For `s ≤ (log N)^j` it is
computable in polynomial time with a `CalcName_j`-style oracle by binary
search on `k`, using the decision version "is some `k' ≥ k` nameable?".
That decision version is in `β_j` by the same proof. **[paper]**

---

## 4. Hardness

### 4.1 With a symbol from the input: complete at every rung

Add to B a unary function symbol `f` and a new constant `⊤` that is not
a number and cannot be written in a name. The input supplies a Boolean
circuit `C` with `ℓ` inputs, and there is one new rewrite rule:

    f(ν) → ⊤   if ν is a numeral for u and C(u mod 2^ℓ) = 1,
    f(ν) → 0   if ν is a numeral for u and C(u mod 2^ℓ) = 0.

No rule takes `⊤` as an argument, so a term with `⊤` strictly inside it
is stuck. The evaluation proof counts one application of the `f` rule
as one step, like any other rule. The checker evaluates `C` there, in
time polynomial in `|C|`.

> **OracleName_j.** Input: a circuit `C`, a size bound
> `s ≤ (log N)^j`, a proof budget `m` in unary, and padding `1^P` (which
> only adds to the input length `N`). Question: is there a
> name of size `≤ s` over B plus `f` whose evaluation proof has length
> `≤ m` and ends in `⊤`?

**Theorem 4. [paper]** For every `j ≥ 1`, `OracleName_j` is
`β_j`-complete under polynomial-time many-one reductions. Under ETH,
`OracleName_{j+1} ∉ β_j` for every `j`.

*Proof.* *Membership.* As in Proposition 3(b): the alphabet now has 8
name symbols, so guess `3s` bits and check, evaluating `C` at each `f`
step.

*Hardness.* Let `L ∈ β_j` with relation `R` and guesses of exactly
`ℓ(x) = ⌈c(log|x|)^j⌉` bits (pad shorter guesses). Map `x` to:

- `C_x`, the circuit computing `y ↦ R(x, y)` on `ℓ = ℓ(x)` input bits,
  of size polynomial in `|x|`;
- `s = ℓ + 3`;
- `m = 2(ℓ + 3)` in unary;
- padding `1^P` with `P` large enough that the input length `N`
  satisfies `(log N)^j ≥ ℓ + 3`. Since `ℓ + 3 ≤ (c+1)(log|x|)^j`, it is enough that
  `N ≥ |x|^{(c+1)^{1/j}}`, a polynomial.

If `x ∈ L` with witness `y`, let `u = 2^ℓ + y` (a leading 1 so the
numeral has no leading zero and exactly `ℓ + 1` digits; its low `ℓ`
bits are `y`). The name `f(numeral of u)` has size `ℓ + 3`, is already
`f` applied to a numeral, and its evaluation proof is
`f(ν) → ⊤`, of length `(ℓ + 3) + 1 ≤ m`.

Conversely, suppose some name `τ` has an evaluation proof ending in `⊤`.
Only the `f` rule produces `⊤`, and nothing consumes it, so the last
step rewrote the whole term `f(ν)` to `⊤`, with `ν` a numeral for some
`u` and `C_x(u mod 2^ℓ) = 1`. So `y = u mod 2^ℓ` is a witness and
`x ∈ L`.

*ETH.* By Proposition 1's argument, a `β_{j+1}`-complete problem in
`β_j` would put `PAD` in `β_j`. ∎

This answers (c) of the question with a "yes, but". The family
`OracleName_1, OracleName_2, …` is complete at every rung and, under
ETH, climbs strictly. But it is the generic problem `CSAT_j` in
disguise: the circuit `C` is the problem, and the arithmetic only spells
out the witness. It is the oracle-relative naming of the general naming
theorem (`P-VS-NP-LIMITS.md` §2) cut down to polynomial size.

### 4.2 Plain calculation names: open

**Question. [open]** Is `CalcName_j` hard for `β_j` for some `j ≥ 2`?
Is it in P?

Why the reduction from 4.1 does not transfer. A reduction from `CSAT_j`
has to turn a circuit `C` into a target number `k_C` such that `k_C` has
a short name exactly when `C` is satisfiable. It must compute `k_C`
without knowing a witness, yet in the yes case `k_C` must be the value
of a short term built from a witness. Different short terms may also
reach `k_C` for reasons unrelated to `C`. This is the problem described
for Short-naming in `P-VS-NP-LIMITS.md` §4, and the same one met by MCSP
and `MINKT` **[classical]**:

- Kabanets and Cai (2000): if MCSP is NP-hard under deterministic
  "natural" reductions, then EXP ⊄ P/poly. Later work extended the
  barrier to more general deterministic reductions: Murray and Williams
  (2015/17; from memory, their conclusion is EXP ≠ ZPP for any
  deterministic polynomial-time many-one reduction), Hitchcock and Pavan
  (2015), Hirahara and Watanabe (2016), Saks and Santhanam (2020). This
  list is as given in Hirahara (2022) §1.2. So a simple deterministic
  hardness proof would prove a new lower bound.
- Randomized reductions avoid these barriers. Hirahara (2022) proves
  that the *partial-function* versions MCSP\* and MINKT\* are NP-hard
  under randomized polynomial-time reductions (his Theorem 1.2).
- Ko (1991): there are oracles relative to which `MINKT` is not
  NP-hard, so hardness needs non-relativizing ideas.

*Update:* `CALCNAME2-HARDNESS.md` proves the Kabanets–Cai-type barrier
for natural deterministic reductions (Theorem A there), tries the partial
version with an arithmetic gadget (complete but unsound), and counts short
names in B. The question stays open. The rest of this subsection is the
original text.

We have not proved a barrier of this kind for `CalcName_j`, though we
expect one. A natural first target is the partial version ("is there a
short name for a number that agrees with `k` on the given bit
positions?") under randomized reductions, following Hirahara. Nor do we know an upper bound better
than `β_j`. Small values of `s` do not obviously help: B has
exponentiation, so terms of size `(log N)^j` reach numbers far beyond
`2^N`, and the set of values is not obviously structured enough for a
polynomial search.

---

## 5. The padded proof-budget version

Now take the question literally, with padding.

> **PadProv_j.** Input: a sentence `ψ`, a budget `1^m` and padding
> `1^N'`, with `m ≤ (log N)^j` for the total input length `N`.
> Question: does `T` prove `ψ` with a proof of at most `m` symbols?
>
> **PadName_j.** The same for Short-naming (`P-VS-NP-LIMITS.md` §4): is
> there `φ` with `|φ| ≤ s` and a proof of at most `m` symbols of
> `∀x (φ(x) ↔ x = bin(k))`, with `m ≤ (log N)^j`?

Proofs are strings over a finite alphabet (variables written with a
binary index), checked in polynomial time, as in the proof-budgets note
§1.

**Proposition 5. [paper]**

(a) `PadProv_j, PadName_j ∈ β_j`, and `PadProv_1, PadName_1 ∈ P` by brute
force over all `|Σ|^m ≤ N^{c}` strings.

(b) `PadProv_j ∈ P` if and only if bounded provability (input `ψ`, `1^m`)
can be decided in time `2^{O(m^{1/j})}·poly(m)`, and similarly for
`PadName_j` and Short-naming.

*Proof.* (a) Guess the proof: `O(m) = O((log N)^j)` bits. (b) Lemma 2
and its first-order analogue give `|ψ| ≤ m` and `|bin(k)| ≤ m` on
yes-instances, so the real input has size `O(m)`. A polynomial-time
algorithm for `PadProv_j` runs in time `poly(N)` with `N` as small as
`2^{⌈m^{1/j}⌉}`, which is `2^{O(m^{1/j})}`. Conversely, such an
algorithm for bounded provability runs in time polynomial in `N` once
`(log N)^j ≥ m`. ∎

So a polylog proof budget is the same thing as asking for
subexponential proof search.

**Lemma 6′ (proofs of satisfiability). [paper]** Let `T ⊇ PA⁻` be
consistent, with a Hilbert-style proof system as in the proof-budgets
note §1. For a 3-CNF `φ` with `v` variables and `r` clauses, let

    ψ_φ  =  ∃x_1 … ∃x_v ( B ∧ Θ ),
    B    =  ⋀_i (x_i = 0 ∨ x_i = 1),
    Θ    =  ⋀_c (ℓ_{c,1} ∨ ℓ_{c,2} ∨ ℓ_{c,3}),

where a literal is `x_i = 1` or `x_i = 0`, and both big conjunctions are
written as balanced binary trees. Then:

(a) `|ψ_φ| = O((v + r)·log v)`, since variable indices are written in
binary.

(b) If `φ` is satisfiable, a satisfying assignment gives, in polynomial
time, a proof of `ψ_φ` of length `O(v·|ψ_φ|) = O(v·(v + r)·log v)`.

(c) If `T ⊢ ψ_φ` then `φ` is satisfiable.

*Proof.* (a) is clear.

(b) Fix a satisfying assignment `a ∈ {0,1}^v`. Every fixed
propositional step used below (∨-introduction, ∧-introduction) is
derivable in a fixed number of lines, each of size linear in the
formulas involved. Call that constant `c₀`.

1. *Leaves.* For each `i`, `a_i = a_i` is an equality axiom; one
   ∨-introduction gives `a_i = 0 ∨ a_i = 1`. For each clause pick a
   literal that `a` makes true, say `x_i = a_i`, and get the clause
   instance by two ∨-introductions. Each leaf costs `O(1)` lines of
   `O(1)` symbols (the numerals `0`, `1` are constants and the variables
   are gone).
2. *Conjunction tree.* Combine the leaves bottom-up along the balanced
   trees of `B` and `Θ`, then join the two. A node's line has the size
   of its subformula, and the subformulas at one depth have total size
   at most `|B ∧ Θ|`. There are `O(log(v + r))` depths, so this costs
   `O(c₀·|B ∧ Θ|·log(v + r))`. Here `|B ∧ Θ(a)|` has no variable
   indices, so it is `O(v + r)`.
3. *Existential introductions.* For `i = v, v−1, …, 1` use the axiom
   `χ(t) → ∃x χ(x)` with `χ(x_i) = ∃x_{i+1}…∃x_v (B ∧ Θ)(a_1,…,a_{i−1}, x_i, …)`
   and `t = a_i`, then modus ponens. That is three lines of size
   `O(|ψ_φ|)` per variable, `O(v·|ψ_φ|)` in all.

Step 3 dominates, giving (b).

(c) `ψ_φ` is equivalent in pure logic plus `PA⁻` to the disjunction over
all `a ∈ {0,1}^v` of the closed instances, and `PA⁻` refutes every false
closed quantifier-free sentence. So if `φ` is unsatisfiable, `PA⁻ ⊢ ¬ψ_φ`
(by a long proof, which does not matter here), and `T ⊢ ψ_φ` would make
`T` inconsistent. ∎

The quadratic cost comes from step 3: in a symbol-counted Hilbert
system every line that carries the whole body costs its full size, and
there is one such line per quantifier. Coding the assignment as one
number `x` and reading bits from it does not help directly, because then
every leaf mentions the numeral for `x`, which has about `v` symbols.
Whether quasi-linear proofs `|φ|^{1+o(1)}` exist for some natural choice
of `ψ_φ` is **[open]** here. A proof system with abbreviations
(definitions, as in extended Frege) would give them.

**Proposition 6 (the padded family climbs). [paper, assuming ETH]**

(a) For all `j ≥ 3` and `1 ≤ j' < j/2`: `PadProv_j ∉ β_{j'}`. So
`PadProv_3 ∉ P`, `PadProv_5 ∉ β_2`, and in general
`PadProv_{2j'+1} ∉ β_{j'}`. The family climbs without bound, at least
one rung for every two steps.

(b) If quasi-linear proofs as above exist, the climb is strict:
`PadProv_{j+1} ∉ β_j` for every `j`.

(c) The same holds for `PadName_j` if Short-naming is NP-hard by a
reduction from 3-SAT with naming budget `m ≤ v^{2+o(1)}` for (a), or
`m ≤ v^{1+o(1)}` for (b). That hardness is **[open]**
(`P-VS-NP-LIMITS.md` §4).

*Proof of (a).* By the sparsification lemma (Impagliazzo, Paturi and
Zane 2001), ETH implies that 3-SAT restricted to `r = O(v)` clauses has
no `2^{o(v)}` algorithm. For such `φ`, Lemma 6′ gives a budget
`m = C·v²·log v` computable in polynomial time, with `T` proving `ψ_φ`
within `m` symbols iff `φ` is satisfiable. Map `φ` to
`(ψ_φ, 1^m, padding)` with `N = 2^{⌈m^{1/j}⌉}`, so that
`(log N)^j ≥ m`. Writing this down takes time
`2^{O(m^{1/j})} = 2^{O(v^{2/j} log v)} = 2^{o(v)}` because `j ≥ 3`. If
`PadProv_j ∈ β_{j'}`, then brute force over the guesses decides it in time
`2^{O((log N)^{j'})}·poly(N) = 2^{O(m^{j'/j})}·2^{O(m^{1/j})}`, and
`m^{j'/j} = v^{2j'/j + o(1)} = o(v)` since `2j'/j < 1`. That is a
`2^{o(v)}` algorithm for sparse 3-SAT, against ETH.

(b) The same with `m = v^{1+o(1)}`: then `m^{j/(j+1)} = o(v)`.

(c) The same, with Short-naming in place of bounded provability. ∎

**Proposition 7 (padded problems are not complete). [paper, assuming
hypothesis H below; the argument is Fortnow and Santhanam's, with the
parameters checked here]**

Call a language `A` *polylog-content at level `j`* if every instance
of `A` has the form `(z, 1^P)` and there is a constant `c` such that
every yes-instance satisfies `|z| ≤ c·(log N)^j`, where `N` is the
instance length. `PadProv_j` and `PadName_j` have this form: on a
yes-instance, `|ψ| ≤ m` (and `|bin(k)|, s ≤ m`) with `m ≤ (log N)^j`.

> **Hypothesis H.** Unsatisfiability of 3-CNFs with `v` variables is not
> decidable by nondeterministic machines in time `2^{O(√v)}` with
> polynomial-size advice.

H is a non-uniform, nondeterministic cousin of ETH for refutations. It
is stronger than the assumption `coNP ⊄ NP/poly` that Fortnow and
Santhanam use, and it is not known to follow from ETH.

**Claim.** If H holds, then for `j ≥ 2` no polylog-content language at
level `j` is `β_j`-hard under polynomial-time many-one reductions. In
particular `PadProv_j` and `PadName_j` are not `β_j`-complete.

*Proof.* Suppose `A` is such a language and `R` reduces `CSAT_j` to it
in polynomial time. Change `R` so that it outputs a fixed no-instance
`(z₀, 1^{P₀})` whenever its output has `|z| > c(log N)^j`. That is still
a reduction, because those outputs were no-instances anyway.

*OR-compression.* Fix `v` and let `t = 2^{⌈2v^{1/j}⌉}`. Given 3-CNFs
`φ_1, …, φ_t` on `v` variables (each of length at most
`ℓ₀ = O(v³ log v)` bits), build the circuit `OR_t(i, y) = φ_i(y)`, with
inputs `i` (`log t` bits) and `y` (`v` bits). It has size
`M = O(t·v³ log v)`, so `(log M)^j ≥ (2v^{1/j})^j = 2^j·v ≥ v + log t`.
So it is a legal `CSAT_j` instance, satisfiable iff some `φ_i` is.
Apply `R`. The output has `N ≤ poly(M)`, so `(log N)^j = O(v)`, and its
content is `z` plus the number `N` in binary: at most `ℓ = O(v)` bits.
Call the whole map `f`. It runs in time `poly(t, v)`.

*Covering lemma.* Let `U` be the unsatisfiable 3-CNFs on `v` variables,
`|U| ≤ 2^{ℓ₀}`. All-unsatisfiable tuples map to no-instances with at most
`ℓ` bits of content, so into a set `V` of size at most `2^{ℓ+1}`. Start
with `U' = U` and repeat: pick `w ∈ V` hit by the most tuples from
`U'^t`, at least `|U'|^t / 2^{ℓ+1}` of them. Let `Y ⊆ U'` be the formulas
that occur in none of those tuples. All those tuples lie in
`(U' ∖ Y)^t`, so `|U' ∖ Y| ≥ |U'|·2^{−(ℓ+1)/t} ≥ |U'|/2` once
`t ≥ ℓ + 1`, which holds for large `v`. Put `w` into `S` and continue
with `U' := Y`. Each round at least halves `U'`, so after at most
`ℓ₀ + 1` rounds every unsatisfiable formula is *covered*: it occurs in
some tuple of unsatisfiable formulas that `f` maps into `S`. And
`|S| ≤ ℓ₀ + 1`, so `S` is `poly(v)` bits of advice.

*Refuter.* On input `φ` (with `v` variables) and advice `S`: guess a
position and `t − 1` further formulas, compute `f` of the tuple, and
accept iff the result is in `S`. If `φ` is unsatisfiable, the covering
lemma gives an accepting guess. If `φ` is satisfiable, every tuple
containing it has a satisfiable OR, so `f` maps it to a yes-instance,
while every element of `S` is the image of an all-unsatisfiable tuple,
a no-instance. So the refuter rejects. Its running time is
`poly(t, v) = 2^{O(v^{1/j})} ≤ 2^{O(√v)}` for `j ≥ 2`, which
contradicts H. ∎

So the padded family is a natural problem that climbs (Proposition 6)
but, under H, is complete at no rung `j ≥ 2`. The reason is plain:
completeness for `β_j` needs room in the input for a big circuit, and a
padded problem keeps only polylog bits of real content.

---

## 6. Full first-order naming: the guessing is in the proof

Short-naming in a first-order theory `T` with the size budget on the
formula only:

> Is there `φ` with `|φ| ≤ s` and a proof of length `≤ m` (`m` in unary)
> of `∀x (φ(x) ↔ x = bin(k))`?

Even for `s` a constant, the proof has to be guessed, and it has
length between `n` and `m`. So the obvious upper bound is NP at every
size budget, and brute force over formulas does not help. **[paper]**

This is the same split as in `PROOF-BUDGETS-AND-COMPLEXITY.md` §4.

- **Calculation names** (toy arithmetic, programs, first-order names of
  the form "the output of program `d`" with their canonical proofs from
  Lemma A4): the proof is computed from the name. The budget on the name
  is all the guessing, and the problems land on `β_j` (§3). These are
  the `Kt` side.
- **Proof names** (any `φ`, any proof): the guessing is in the proof,
  and the problem is NP-type whatever the size budget. This is the `KNt`
  side.

Whether first-order naming with formula budget `c·log N` is in P is
**[open]**. A yes would mean that the cheapest naming *proofs* can be
found fast when the formula is tiny, which is a proof-search question
like the ones in §5. If `P = NP`, all versions collapse to P.

---

## 7. Summary

| problem | budget on | `c·log N` | `(log N)^j` | hard for its rung? |
|---|---|---|---|---|
| CalcName (toy B, or `MINKT`) | name; proof computed | P | `β_j` | open (MCSP-type wall) |
| OracleName (B + circuit symbol) | name | P | `β_j` | complete, every `j` |
| PadProv / PadName | proof, input padded | P | `β_j` | not complete for `j ≥ 2` under H (Prop 7); PadProv climbs under ETH, one rung per two steps (Prop 6) |
| first-order Short-naming | formula only | NP (P open) | NP | — |

Under ETH: `P = β_1 ⊊ β_2 ⊊ …` (Proposition 1), so `OracleName_j` climbs
one rung at a time. Every result here relativizes, so none bears on
P versus NP (`P-VS-NP-LIMITS.md` §1–2).

### What is known and what is new

We checked the following sources for this section (2026-11-24): Buss and
Goldsmith (1993) in full; Flum and Grohe's BEATCS column *Parameterized
complexity and subexponential time*, about two thirds verbatim; Hirahara
(ECCC TR22-119), §§1–2 verbatim; Hu, Lu and Oliveira (ECCC TR25-203),
§§1–3. A survey thesis on limited nondeterminism (Kentucky) and ECCC
TR20-050 could not be fetched.

**Known.**

- `β_j` and the generic complete problem: Kintala–Fischer, Díaz–Torán,
  Buss–Goldsmith (§1).
- `P ≠ β_2` under ETH, and more. Flum and Grohe (Corollary 4.7 in the
  column, attributed there to earlier work) show that `W[P] = FPT` iff
  circuit satisfiability has a subexponential algorithm iff
  `P = NP[ι(n)·log n]` for some unbounded computable `ι`. ETH rules out
  the middle statement, so `P ≠ NP[ι(n)·log n]` for *every* unbounded
  `ι`, in particular `P ≠ β_2`.
- Small thresholds make meta-complexity problems easy. Hirahara (2022)
  notes that MCSP\* with size `s` is solvable in time `2^{O(s log s)}`,
  and that his NP-hardness needs `s = 2^{Θ(n)}`, "inevitable unless NP
  can be solved in randomized sub-exponential time". Our Proposition 3
  is the same observation for naming.
- The barriers for deterministic hardness proofs and the randomized
  route around them (§4.2).
- On the nondeterministic side: Hu, Lu and Oliveira (2025) show that
  `MINnKT` (nondeterministic time-bounded Kolmogorov complexity) is in
  BPP iff NP ⊆ BPP. First-order naming sits between `Kt` and `KNt`
  (proof-budgets note, Proposition 5), so this is the closest known
  result to the question in §6. It suggests that first-order
  Short-naming might be NP-hard in the same randomized sense.
- The compression argument (Fortnow and Santhanam 2008). Proposition 7
  reruns it with superpolynomial `t`; the parameter check is ours.

**Not found in what we read, so possibly new (or folklore):**

- The full strict ladder `β_j ⊊ β_{j+1}` under ETH (Proposition 1). The
  padding is routine, and the `P ≠ β_2` case is covered above.
- Lemma 2's point that a polylog *proof* budget is vacuous without
  padding, and the three-way split: name budget (`CalcName`), oracle
  version (`OracleName`, complete), padded proof budget (`PadProv`).
- `CalcName_j ∈ β_j` and `OracleName_j` complete for `β_j`. Both are
  routine once the problems are set up.
- Propositions 6 and 7: the padded family climbs under ETH but is not
  complete under H.

**Still to check.**

- Whether `ψ_φ` can be proved in quasi-linear length in a plain Hilbert
  system (Lemma 6′ remark). That would make Proposition 6 strict.
- The Goldsmith–Levy–Mundhenk survey (1996) for a citation of
  Proposition 1.
- The open problem worth keeping: **is `CalcName_2` in P, or hard for
  `β_2`?** It is the smallest natural naming question in this note whose
  status is unknown. The partial version under randomized reductions is
  the most promising route (§4.2).

---

## References

- J. Buss and J. Goldsmith, *Nondeterminism within P*, SIAM J. Comput.
  22 (1993) 560–572. Read in full for this note (author's copy at
  cs.uky.edu/~goldsmit/papers/NondetWithinP.pdf): definitions of
  `N^m P_l`, Theorems 2, 5, 6, 9, 10, 12.
- J. Díaz and J. Torán, *Classes of bounded nondeterminism*, Math.
  Systems Theory 23 (1990) 21–32. Source of `β_k` (cited via Buss and
  Goldsmith, not read).
- C. Kintala and P. Fischer, *Refining nondeterminism in relativized
  polynomial-time bounded computations*, SIAM J. Comput. 9 (1980)
  46–53. (Not read.)
- J. Goldsmith, M. Levy and M. Mundhenk, *Limited nondeterminism*,
  SIGACT News 27(2) (1996). (Not read.)
- C. Papadimitriou and M. Yannakakis, *On limited nondeterminism and the
  complexity of the V-C dimension*, JCSS 53 (1996). (Not read.)
- J. Flum and M. Grohe, *Parameterized complexity and subexponential
  time*, BEATCS 84 (2004), Computational Complexity Column. Read in part
  (Theorem 3.12, Corollary 4.7).
- S. Hirahara, *NP-hardness of learning programs and partial MCSP*,
  FOCS 2022, ECCC TR22-119. Read §§1–2 (Theorems 1.1, 1.2; §1.2 on
  barriers).
- J. Hu, Z. Lu and I. C. Oliveira, *Hardness of computing
  nondeterministic Kolmogorov complexity*, ECCC TR25-203 (revision 2,
  2026). Read §§1–3 (Theorem 1).
- V. Kabanets and J.-Y. Cai, *Circuit minimization problem*, STOC 2000.
  (Cited via Hirahara 2022.)
- R. Impagliazzo, R. Paturi and F. Zane, *Which problems have strongly
  exponential complexity?*, JCSS 63 (2001). (Sparsification lemma; not
  read.)
- L. Fortnow and R. Santhanam, *Infeasibility of instance compression
  and succinct PCPs for NP*, STOC 2008 / JCSS 2011. (Not read.)
- C. Murray and R. Williams, *On the (non) NP-hardness of computing
  circuit complexity*, CCC 2015. (Not read.)
- K. Ko, *On the complexity of learning minimum time-bounded Turing
  machines*, SIAM J. Comput. 20 (1991). (As cited in `P-VS-NP-LIMITS.md`.)
