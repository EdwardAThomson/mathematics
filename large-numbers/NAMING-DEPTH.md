# Naming depth

*Written 2026-11-24. A sequel to `PROOF-BUDGETS-AND-COMPLEXITY.md` §4.
Question: Bennett's logical depth of a string is the running time of its
near-shortest programs. Replace programs by naming formulas and running
time by proof length. Is the result a sensible notion, and does it obey
a slow-growth law like Bennett's?*

*Second pass, same day: Bennett's paper read directly (§1, §4), the
citation for Lemma A4 found, Proposition 12 written out with its lemma
(§5), and a bit-charged version added in which Bennett's own definition
and his loss-free law go through (§6). Third pass: Proposition 12
restated with the hypothesis its proof uses, so that it has no asserted
step, and the link to consistency statements moved to Lemma 12a. Fourth
pass: §6 re-read and tightened, and the derivations of Lemma 11 and
Lemma 12a written out for a fixed proof system as a script that checks
them (`naming-depth/collision_check.py`).*

Tags as elsewhere: **[paper]** argued here, not machine-checked;
**[paper, modulo A4]** uses Lemma A4 of the proof-budgets note
(polynomial-size proofs of correct runs). That lemma is Theorem 6.1.4 of
Pudlák's Handbook chapter, where the proof is a sketch; **[paper,
sketch]** the argument is outlined and some bookkeeping is not written
out; **[checked on instances]** the derivations are built and verified
by the script for many inputs, which is evidence and not a proof for all
inputs; **[classical]** textbook or cited; **[expected]** believed, not
proved here; **[open]** not settled. Nothing here is Lean-checked.

---

## 0. The answer in plain language

1. **The definition works.** For a number `k` and a formula budget `b`,
   let `t_k(b)` be the length of the shortest proof that some formula of
   at most `b` symbols names `k`. This is the **naming profile** of `k`.
   The **naming depth** of `k` at slack `s` is the profile read at the
   budget `D_T(k) + s`, that is, among names within `s` symbols of the
   shortest one. It is not computable, but it can be approximated from
   below. **[paper]**

2. **Deep numbers exist, and they need not be large.** For every
   computable threshold there are numbers with a name of about `log n`
   symbols and only about `n log n` binary digits, such that every name
   of up to `n` symbols needs a proof longer than the threshold. Size and
   depth are different things: a number can be enormous and shallow
   (relative to its length), or modest and deep. **[paper]**

3. **Naming depth sits between two versions of Bennett's depth.** It is
   at most polynomial in the running-time depth, and at least the
   nondeterministic running-time depth, after the usual rescaling of the
   budget. If P = NP the three agree up to polynomials, so a number that
   is much shallower for proofs than for programs would separate P from
   NP. **[paper, modulo A4]**

4. **There is a slow-growth law.** If a formula of `b` symbols names `k`
   with a proof of length `t`, and `f` is computable, then a formula of
   `b + C_f` symbols names `f(k)` with a proof of length about `t` plus a
   polynomial in the running time of `f`. Read as a statement about
   slack, the slack grows by `C_f` plus the number of symbols of
   information that `f` throws away. For a reversible `f` nothing is
   thrown away: a quick recoding cannot make a shallow number deep, or a
   deep one shallow. **[paper, modulo A4]** The extra term for
   information loss has the same shape as in the closest published
   analogue (Antunes, Fortnow, van Melkebeek and Vinodchandran, Theorem
   14). The definition used here is one Bennett considered and rejected
   (his "tentative definition 0.2"). His final definition avoids the
   loss term; item 6 carries it over.

5. **Theory strength comes back, but at most exponentially, and probably
   hard to show that it comes back at all.** I expected depth to be the
   place where a stronger theory makes a real difference, because of
   Gödel's speed-up theorem. That is true for a *fixed name*: a stronger
   theory can shorten the proof for one formula by more than any
   computable amount. It is false for the *number*: the weak theory can
   switch to a different name, "the output of the search through the
   strong theory's proofs", and so its depth is at most exponential in
   the strong theory's depth. **[paper, modulo A4]** Whether the gap is
   ever more than polynomial is tied to a known open problem of Pudlák
   on proofs of finite consistency statements, and a positive answer
   would imply NP ≠ coNP. **[paper, with the derivations involved
   written out and checked on instances, one standard formalisation
   fact assumed, plus cited results]**

6. **Charged in bits, the theory becomes Bennett's.** Items 1 to 5 use
   the project's size measure, the number of symbols in a formula. That
   measure is too coarse for "within `s` of the shortest name" to mean
   much. §6 charges a name in bits and lets it carry a self-delimiting
   binary data part. Then the cost of the cheapest name of `k` equals
   the Kolmogorov complexity `K(k)` up to an additive constant, for
   every theory. Bennett's own definition makes sense (a name counts
   when the name itself is incompressible), the slow-growth law holds
   with no loss term, random numbers are shallow, and the diagonal
   numbers are deep at almost every significance level, exactly as in
   his paper. Naming depth and Bennett's depth then bound each other,
   polynomially in one direction and exponentially in the other, with
   only a logarithmic change in the significance level. **[paper,
   modulo A4]**

So naming depth behaves like Bennett's depth in the ways that matter, it
is robust in the same way naming complexity is (the theory only moves
things by a bounded amount), and the questions it leaves open are the
standard hard ones of proof complexity.

---

## 1. Setting and definition

As in `PROOF-BUDGETS-AND-COMPLEXITY.md` §1 and Appendix A.0. `T ⊇ IΣ₁` is
consistent with a polynomial-time decidable set of axioms (PA, `IΣ_k`,
ZFC). `|φ|` is the node count of a formula, `|π|` the total size of the
formulas in a Hilbert-style proof. Naming uses the **binary target**: `π`
is a naming proof for `(φ, k)` when it proves `∀x (φ(x) ↔ x = bin(k))`.

Two complexities, to keep apart from the start:

- `D_T(k)` = the size of the smallest formula naming `k` in `T`, with no
  bound on the proof (Report §8). This plays the role of `K`.
- `D_T^t(k)` = the size of the smallest formula naming `k` with a proof
  of length at most `t`. This plays the role of the time-bounded `K^t`.

(The proof-budgets note writes `D_T` for `|φ| + log₂|π|`, the analogue of
Levin's `Kt`. That measure is not used here.)

**Definition (naming profile).** For `b ≥ D_T(k)`,

    t_k(b) = min { |π| : π is a naming proof for (φ, k), |φ| ≤ b }.

Equivalently `t_k(b)` is the least `t` with `D_T^t(k) ≤ b`. Say `k` is
**(b, t)-nameable** when `t_k(b) ≤ t`. The profile is non-increasing in
`b`.

**Definition (naming depth).** For a slack `s ≥ 0`,

    depth_T^s(k) = t_k(D_T(k) + s)
                 = the shortest proof among names within s symbols of the shortest.

**Which of Bennett's definitions this copies. [classical, from the
paper]** Bennett (1988, §3) works up to his definition in steps.

- Tentative definition 0.1: the running time of the minimal program.
  Rejected as unstable.
- Tentative definition 0.2: "the time required to compute the string by
  a program no more than s bits larger than the minimal program".
  Rejected because `2^k` distinct programs of `n + k` bits get no more
  weight than one.
- Tentative definition 0.3: the time for the probability of the output
  under time-bounded random programs to rise to within a factor `2^{-s}`
  of its limit. He calls this satisfactory.
- Definition 1, the one he adopts: `D_s(x) = min { T(p) : |p| − |p*| < s
  and U(p) = x }`, the least time of a program for `x` that is *itself*
  incompressible by `s` bits. He prefers it to 0.3 because "it appears
  to yield a stronger slow growth property".

The definition above is the proof-length copy of **tentative definition
0.2**. It is also the form `min { t : K^t(x) − K(x) ≤ s }`, and
`K^t(x) − K(x)` is the "basic computational depth" of Antunes, Fortnow,
van Melkebeek and Vinodchandran (2006). §§2 to 5 work with it because it
is the direct reading of "shortest proof among near-shortest names" and
needs nothing beyond the project's size measure. §6 gives the copy of
Definition 1.

**A caution about additive slack.** With programs, "within `s` bits of
the shortest" is meaningful because a universal machine is optimal up to
an additive constant. Formula size has no such property. The literal
name `x = bin(k)` costs about `6 log₂ k` symbols, while a formula of `n`
symbols can carry about `n log n` bits, so for a typical `k` the literal
name is a factor of order `log log k` away from the shortest one, not an
additive constant. For this reason the theorems below are stated for the
profile `t_k(b)`, which involves no comparison with `D_T(k)`, and then
read as statements about slack where that is safe. Statements about
*deep* numbers survive this well (Theorem 3 holds for a huge range of
slack). Statements that particular numbers are *shallow at small
additive slack* generally cannot be proved for this size measure, since
they need lower bounds on `D_T(k)` for specific `k`. §6 removes the
problem by changing the size measure.

## 2. Basic facts

**Proposition 1 (range). [paper]** For `k ≥ 1`:

- `t_k(b) ≥ log₂ k` for every `b`. The numeral `bin(k)` is in the last
  line of the proof.
- `t_k(b) ≤ c·log₂ k + c` once `b ≥ 6·log₂ k + 3`. The literal name
  `x = bin(k)` fits the budget and `∀x (x = bin(k) ↔ x = bin(k))` is a
  logical truth with a proof linear in its size.

So the profile of every number falls from `depth_T^0(k)` at `b = D_T(k)`
to within a constant factor of its floor `log₂ k` by `b = 6 log₂ k + 3`.
All the interest is in how fast it falls. Because of the floor, it is
natural to call `k` **shallow at budget `b`** when `t_k(b)` is polynomial
in `log₂ k`, its number of digits, and **deep** when it is far larger.
This is depth *relative to length*. Bennett's depth is an absolute time,
and the theorems below are stated in absolute terms.

**Proposition 2 (computability). [paper]**

- (a) `depth_T^s` is computable from `D_T`, hence from the halting
  problem.
- (b) `depth_T^s` is approximable from below: there is a computable
  sequence, non-decreasing in the stage, converging to `depth_T^s(k)`.
- (c) For no `s` is `depth_T^s` computable.
- (d) For no `s` is `depth_T^s(k)` bounded by a computable function of
  `k`.

*Proof.* (a) Given `D_T(k)`, list proofs by length until one is a naming
proof for some `(φ, k)` with `|φ| ≤ D_T(k) + s`. One exists. (b) Proof
search gives a computable sequence `d₀ ≥ d₁ ≥ …` converging to `D_T(k)`.
At each stage run (a) with `d_i` in place of `D_T(k)`. A smaller `d_i`
admits fewer formulas, so the answers do not decrease, and they are
correct once `d_i = D_T(k)`. (c) Suppose `depth_T^s` were computable. Put
`t = depth_T^s(k)` and compute `D_T^t(k)` by listing the proofs of length
at most `t`. Then `D_T(k) ≤ D_T^t(k) ≤ D_T(k) + s`, so
`g(k) = D_T^t(k) − s` is a computable lower bound on `D_T`, and it is
unbounded because only finitely many numbers have `D_T` below a given
value. Let `f(n)` be the least `k` with `g(k) ≥ n`. It is computable, so
`D_T(f(n)) ≤ C + 6 log₂ n` (Report, Theorem 2), yet `D_T(f(n)) ≥ n`.
Contradiction for large `n`. (d) By Theorem 3 below. ∎

**Theorem 3 (deep numbers exist). [paper]** Let `g` be a computable
function. There are constants `C_g` and `c` and numbers `k_n` such that
for every `n`:

- `k_n < 2^{c·n·log₂ n}`, so `k_n` has at most `c·n·log₂ n` binary
  digits;
- `D_T(k_n) ≤ C_g + 6·log₂ n`;
- every formula of size at most `n` that names `k_n` has only naming
  proofs longer than `g(n)`. That is, `t_{k_n}(b) > g(n)` for all
  `b ≤ n`.

Hence `depth_T^s(k_n) > g(n)` for every slack `s ≤ n − C_g − 6·log₂ n`.

*Proof.* Let `k_n` be the least number that is **not** named by any
formula of size at most `n` with a naming proof of length at most
`g(n)`. Third item: by definition. First item: each formula names at
most one number (Report, Theorem 1), so at most `F(n)` numbers are
excluded, where `F(n) ≤ 2^{c n log n}` is the number of formulas of size
at most `n`, and `k_n ≤ F(n)`. Second item: `n ↦ k_n` is computable,
because there are finitely many proofs of length at most `g(n)` up to
renaming of variables and proofs can be checked. Apply Theorem 2 of the
Report. ∎

Three remarks.

- **Relative to length.** Given a computable non-decreasing `G`, take
  `g(n) = G(c·n·log₂ n)`. Then the proofs are longer than `G` of the
  number of digits of `k_n`. So no computable function of the length
  bounds the depth. Proposition 2(d) follows by taking `g(n)` to be the
  maximum of a given function over `[0, F(n)]`.
- **The slack range is wide.** `D_T(k_n)` is about `log n` and the depth
  persists up to slack about `n`. So `k_n` is deep under any reasonable
  rescaling of the budget, including a constant or logarithmic factor.
  This is why the "caution about additive slack" does not affect it.
- **This is Bennett's diagonal example.** The string version is the
  first string of length `n` with no program shorter than `n` running
  within time `g(n)`. **[classical]**

## 3. Comparison with Bennett's depth

Fix a universal machine. For a number `k` written in binary, let

- `τ_k(b)` = the least running time of a program of at most `b` bits
  that prints `k`;
- `τ^N_k(b)` = the same for nondeterministic programs, every accepting
  run printing `k`.

`τ_k` is the profile behind the `K^t − K` form of logical depth:
`min { t : K^t(k) ≤ K(k) + s }` is `τ_k(K(k) + s)`.

**Proposition 4 (sandwich). [paper, modulo A4]** There are an absolute
constant `c`, a constant `c_T`, and a polynomial `q` such that for all
`k` and `b`, writing `t = t_k(b)`:

- (a) `t_k(6b + c) ≤ q(τ_k(b) + b)`;
- (b) `τ^N_k(c·b·log₂ b + c·log₂ t + c_T) ≤ q(t)`;
- (c) `τ_k(c·b·log₂ b + c_T) ≤ 2^{c·t·log₂ t}`.

*Proof.* These are the two halves of Proposition 5 of the proof-budgets
note with the size and the time kept separate. (a) If `d` prints `k` in
`τ` steps, the formula "`x` is the output of program `bin(d)`" has size
at most `6|d| + c` and a naming proof of length `q(τ + |d|)`: one fixed
uniqueness lemma of `IΣ₁` and a verification of the run (Lemma A4). (b) A
nondeterministic program holding `φ` and `t` guesses a string of size
`t`, checks that it is a naming proof for `φ`, and prints the number in
its last line. Every accepting run prints `k` because `φ` names only
`k`. (c) A deterministic program holding `φ` tries all candidate proofs
in order of length. There are `2^{O(t log t)}` of size at most `t`. ∎

In words: a fast program gives a short proof, and a short proof gives a
fast *nondeterministic* program, or a deterministic one that is
exponentially slower. Naming depth is squeezed between the
nondeterministic and the deterministic running-time depth. The budget is
rescaled by the factors `6` and `c·log b` that appear throughout the
project.

**Corollary 5. [paper, modulo A4]** If P = NP, then
`τ_k(c·b·log₂ b + c·log₂ t + c_T) ≤ q(t_k(b))` for a polynomial `q`: the
naming profile and the running-time profile agree up to polynomials and
the rescaling of the budget. Consequently, exhibiting numbers whose
naming profile is super-polynomially below their running-time profile at
these budgets would prove P ≠ NP.

*Proof.* "Some naming proof for `φ` of size at most `t` extends this
prefix" is an NP question (with `t` in unary). If P = NP, a
deterministic program builds a proof symbol by symbol in polynomial
time. ∎

This is the depth form of Corollary 6 of the proof-budgets note. There
the cost was `|φ| + log |π|` and the relevant collapse was
NEXP ⊆ EXP/poly (Allender and Spakowski). Here the size and the time are
separate axes and the relevant collapse is P = NP. We do not get a
converse in either place, for the same reason: a naming proof must show
that *no other* number fits, and short proofs of such universal
statements are what may not exist.

## 4. The slow-growth law

**Lemma 6 (composition). [paper, modulo A4]** Let `f` be computable,
computed by a machine in `time_f(k)` steps on input `k`. There are a
constant `C_f` and a polynomial `q_f` such that, for every `k` and every
`b ≥ D_T(k)`,

    t_{f(k)}(b + C_f)  ≤  c·t_k(b) + q_f(time_f(k) + log₂ k).

*Proof.* Let `φ` name `k` with proof `π`, `|φ| ≤ b`. Let `Run_f(u, z, x)`
be the Δ₀ formula "`z` codes a halting run of the machine on input `u`
with output `x`", and put

    φ′(x) :≡ ∃u ( φ(u) ∧ ∃z Run_f(u, z, x) ),       |φ′| = |φ| + C_f.

A naming proof for `(φ′, f(k))`: from `π`, the line `φ(u) ↔ u = bin(k)`.
By Lemma A4, a proof of `Run_f(bin(k), bin(r), bin(f(k)))` of length
polynomial in `time_f(k) + log₂ k`, where `r` codes the run. From
`IΣ₁`, the fixed lemma that two runs on the same input have the same
output. Existence: `∃u (u = bin(k))`, and under `u = bin(k)` both
conjuncts hold. Uniqueness: under `φ(u)` and `Run_f(u, z, x)`, we get
`u = bin(k)`, so the fixed lemma against the exhibited run gives
`x = bin(f(k))`. Each step is linear in the formulas already present,
and `|π|` is at least `2|φ| + log₂ k`. ∎

This is the slow-growth law in its exact form: **a short proof for a
name of `k` becomes a short proof for a name of `f(k)` that is `C_f`
symbols longer.** It involves no comparison with shortest names. Since
`t_k(b) ≥ log₂ k`, for polynomial-time `f` the right-hand side is
polynomial in `t_k(b)`.

**Theorem 7 (slow growth, slack form). [paper, modulo A4]** With `f`,
`C_f`, `q_f` as in Lemma 6,

    depth_T^{s′}(f(k))  ≤  c·depth_T^s(k) + q_f(time_f(k) + log₂ k),

    where  s′ = s + C_f + ( D_T(k) − D_T(f(k)) ).

*Proof.* Lemma 6 at `b = D_T(k) + s`. The budget `b + C_f` is
`D_T(f(k)) + s′`. ∎

The term `D_T(k) − D_T(f(k))` is the information that `f` discards at
`k`, measured in symbols. It is at least `−C_f`, so `s′ ≥ s`.

**Corollary 8 (when little is lost). [paper, modulo A4]**

- (a) If `f` has a computable left inverse `h` (`h(f(k)) = k`), then
  `s′ ≤ s + C_f + C_h`. A fast reversible recoding cannot make a shallow
  number deep. Applied to `h`, it cannot make a deep number shallow
  either, if `h` is also fast.
- (b) If every value of `f` has at most `m` preimages, then
  `s′ ≤ s + C_f + 6·log₂ m`.

*Proof.* (a) Lemma 6 without the proof lengths gives
`D_T(k) ≤ D_T(f(k)) + C_h`. (b) `k` is computable from `f(k)` and the
position `i ≤ m` of `k` among the preimages of `f(k)` in increasing
order, so `D_T(k) ≤ D_T(f(k)) + 6 log₂ i + C`. ∎

**How this compares with the published laws. [classical, cited]**

- Bennett's Theorem 1 (the slow growth law) is probabilistic. For
  `s₂ > s₁`, a random program has probability less than
  `2^{-(s₂−s₁)+O(1)}` of transforming `x` into an output whose depth at
  significance `s₂` exceeds the depth of `x` at significance `s₁` plus
  the run time plus a constant. He states the deterministic case only
  in words: fast deterministic processes are "unable to transform a
  shallow object into a deep one". It follows from Theorem 1, because
  one program `q` has probability `2^{-|q|}`: the significance goes
  from `s` to `s + |q| + O(1)`, with no term for information loss.
- The reason there is no loss term is Definition 1. If `p` is a program
  for `x` that is incompressible by `s` bits, then "`p`, then apply `q`"
  is incompressible by `s + |q| + O(1)` bits and computes the output,
  whatever the complexity of the output is. The combined program may be
  far longer than the shortest program for the output, and it still
  counts.
- For the `K^t − K` style of definition, Antunes, Fortnow, van Melkebeek
  and Vinodchandran prove a slow-growth law only for a variant
  (distinguishing depth), for `f` polynomial-time, honest and at most
  `m`-to-one, with an additive loss `2·log m + O(log n)` (their Theorem
  14), dropping to `O(1)` for one-to-one `f`. They state no law for
  basic depth `K^t − K`. Corollary 8(b) has the same shape as their
  theorem.

So Theorem 7 is what one should expect for a definition of the
tentative-0.2 kind, and the loss term is not an artifact of proofs.
Theorem 16 in §6 is the loss-free law for the Definition 1 kind.

**Is the loss term needed? [open]** I could not show it is, and could
not remove it. The natural test, `k = ⟨z, r⟩` with `z` deep and `r`
random padding, fails as a counterexample: every name of `k` yields a
name of `z`, so a short-proof name of `k` close to the shortest would
make `z` shallow at a slack of about `D_T(k) − D_T(z)`, which is where
Theorem 7 puts it.

**Absolute, not relative.** The law bounds proof lengths, not proof
lengths divided by the length of the number. A projection can turn a
number that is shallow relative to its length into one that is deep
relative to its length. Example: let `z` be a deep number from Theorem 3
and let `k` code `z` together with the full trace of the computation
that finds `z`. Then `k` has a name of about `log n` symbols whose proof
just checks the trace, polynomial in the length of `k`, while `z`, its
first component, is deep relative to its own much smaller length. In
absolute terms nothing went wrong: the proof for `z` is no longer than
the proof for `k`, as Lemma 6 says. The same is true of Bennett's law.

## 5. Dependence on the theory

Write `t^T_k` and `t^U_k` for the profiles in two theories.

**Proposition 9. [paper]** If `T ⊆ U` then `t^U_k(b) ≤ t^T_k(b)` for all
`b ≥ D_T(k)`. Every `T`-proof is a `U`-proof.

The slack form does not follow, because `D_U(k) ≤ D_T(k)`: the stronger
theory may also have a new, shorter name with a long proof, which moves
the baseline. Comparisons across theories are made on the profile.

**The tempting argument, and where it stops. [classical]** Gödel's
speed-up theorem: for `U = T + Con(T)` and any computable `g` there are
sentences `τ_n` of size `O(log n)` with `U`-proofs of length `O(log n)`
whose shortest `T`-proofs are longer than `g(n)`. (Take `τ_n` to say
"I have no `T`-proof of length below `g(n)`".) So for the formulas

    φ_n(x) :≡ (x = 1 ∧ τ_n) ∨ (x = 0 ∧ ¬τ_n)

the naming proof for `(φ_n, 1)` is short in `U` and longer than `g(n)`
in `T`. **For a fixed name, the speed-up from a stronger theory exceeds
every computable function.** But `1` is not a deep number. Depth
minimises over names, and `T` has other names for `1`.

**Theorem 10 (the ceiling is exponential). [paper, modulo A4]** Let `T`
and `U` be any two consistent theories containing `IΣ₁` with
polynomial-time decidable axioms. Neither need contain the other. There
are constants `c`, `c_U` and a polynomial `q` such that for all `k`, `b`:

    t^T_k(c·b·log₂ b + c_U)  ≤  q( 2^{c·ℓ·log₂ ℓ} ),     ℓ = t^U_k(b).

*Proof.* Proposition 4(c) for `U`, then Proposition 4(a) for `T`. In
words: if `φ` names `k` in `U` with a proof of length `ℓ`, the program
"search the `U`-proofs for one saying what `φ` names" prints `k` within
`2^{O(ℓ log ℓ)}` steps, and `T` can name the output of any program by
checking its run. `T` never has to believe `U`. ∎

So, up to an exponential and the usual rescaling of the budget, naming
depth does not depend on the axioms. In particular a number that is deep
beyond every computable threshold in one theory (Theorem 3) is so in
every theory. This is Corollary 7 of the Report again, one level up:
there the choice of axioms was absorbed by a constant in the budget,
here by an exponential in the proof length.

**Lemma 11 (collision). [paper; checked on instances]** There is a
constant `c` such that for every theory `U` whose axioms include those
of `PA⁻` and every formula `φ`: if `π` and `π′` are `U`-proofs, each of
length at most `ℓ`, that `φ` names `k` and that `φ` names `k′`, with
`k ≠ k′`, then `U` has a proof of a contradiction of length at most
`c·ℓ²`. (If `U` only proves the axioms of `PA⁻`, their fixed proofs are
added once, and the bound is `c·ℓ² + c_U`.)

*Proof.* The last lines are `N = ∀x (φ(x) ↔ x = bin(k))` and
`N′ = ∀x (φ(x) ↔ x = bin(k′))`.

1. From the two, by propositional steps under the quantifier,
   `∀x (x = bin(k) ↔ x = bin(k′))`. A fixed number of lines, each of
   size `O(|N| + |N′|)`. Note that `φ` is never instantiated or opened,
   so no formula grows.
2. Instantiate at `bin(k)` and use `bin(k) = bin(k)`:
   `bin(k) = bin(k′)`. Size `O(L)`, where `L ≤ ℓ` bounds the number of
   digits of `k` and `k′`. (Both numerals occur in the given proofs.)
3. `PA⁻ ⊢ bin(k) < bin(k′)` in `O(L²)` symbols, taking `k < k′` (the
   other case is symmetric). Write `k′ = d + k` with `d ≥ 1`. First
   `0 < bin(d)`, by recursion on the digits of `d` (`0 < 1`, and `0 < s`
   gives `0 < (1+1)·s` and `0 < (1+1)·s + 1`), `O(L)` steps of size
   `O(L)`. Then `0 + bin(k) < bin(d) + bin(k)` by monotonicity of `+`,
   and `bin(d) + bin(k) = bin(k′)` by schoolbook addition (Lemma A3 of
   the proof-budgets note), `O(L²)`.
4. Steps 2 and 3 give `bin(k′) < bin(k′)` by an equality axiom, and `<`
   is irreflexive.

Total `2ℓ + O(|N| + |N′|) + O(L²) ≤ c·ℓ²`. ∎

**Written out and checked.** The script
`naming-depth/collision_check.py` makes this proof concrete. It fixes a
Hilbert system `H`: the propositional schemes `A → (B → A)`,
`(A → (B → C)) → ((A → B) → (A → C))`, `(¬A → ¬B) → (B → A)`, three
schemes for `∧`, the scheme `∀x A → A[t/x]`, modus ponens and
generalisation, the usual equality schemes, and ten axioms of `PA⁻` as
closed sentences. A proof is a bare list of formulas, and the checker
decides from the list alone whether each line is an axiom or follows
from earlier lines. The script then contains the functions that build
the derivations: `Z(d)` for `0 < bin(d)`, `Inc(a)` for
`bin(a) + 1 = bin(a+1)`, `Add(a, b)` and `Add⁺(a, b)` for
`bin(a) + bin(b) = bin(a+b)` and `bin(a) + bin(b) + 1 = bin(a+b+1)`,
`Lt(k, k′)` for `bin(k) < bin(k′)`, and `H(π, π′)`, which appends steps
1 to 4 to the two given proofs. Run of 2026-11-24:

- 25,200 arithmetic derivations pass the checker: every pair of numbers
  below 70, 150 random pairs of up to 128 digits, and carry chains of up
  to 200 digits.
- 953 collision derivations pass: every pair `k ≠ k′` below 28 with the
  formula `x = bin(k)`, named honestly by a `PA⁻` proof, against one
  false axiom; and 197 random pairs of up to 128 digits with a random
  formula `φ` of arbitrary shape, both naming sentences taken as axioms
  of `U`. Each result ends in the fixed contradiction `¬ 0 = 0`, and
  fails the checker when the extra axioms are withdrawn.
- Lengths: the lines added to `π` and `π′` total at most
  `40·(|N| + |N′|) + 3000·(L+1)²` nodes in every case, and the whole is
  at most `23·ℓ²`. The script asserts `c = 30` for this system.
- Every builder adds at most 276 lines per binary digit, and no line is
  larger than 10 times the numerals in play. These two facts are what
  make the bound quadratic.
- The checker rejects the wrong lines it is offered: a modus ponens
  without its premise, a substitution that captures a variable,
  misapplied equality schemes, and a correct addition with one numeral
  changed.

The script checks instances. It is not a proof for all inputs. What it
does establish is that the blocks of lines exist, in a named proof
system, with no axiom forgotten. `H` has no `∃` or `∨`. The derivation
never looks inside `φ`, so it is unaffected if they are added. Another
Hilbert system changes the constants only, since each scheme of `H` has
a fixed derivation there.

**Naming-consistency.** Fix a polynomial-time machine `C_U` that
checks naming proofs: it accepts `(p, f, x, y)` when `p` codes a
`U`-proof of length `y` whose last line is the naming sentence for the
formula coded by `f` and the binary numeral of `x`. Let

    NP_U(p, f, x, y) :≡ ∃w Run_C(p, f, x, y, w),

where `Run_C` is the Δ₀ description of an accepting computation of
`C_U`, as in Lemma A4. True instances have proofs of polynomial length,
already in Robinson arithmetic. **[classical: Pudlák, Handbook ch. VIII,
Theorem 6.1.4. His proof builds exactly a formula of this shape: "We
formalize computations of a Turing machine defining R", with a formula
saying that a string "codes an accepting computation", and "to prove
[it] by a polynomial proof in Q, transform it into statements about
single bits of the string"; the numerating formula is its existential
closure.]** Define, with `m` written in binary,

    NCon_U(m) :≡ ∀p ∀p′ ∀f ∀x ∀x′ ∀y ∀y′ ( y ≤ m ∧ y′ ≤ m
                    ∧ NP_U(p, f, x, y) ∧ NP_U(p′, f, x′, y′)  →  x = x′ ).

In words: no two `U`-proofs of length at most `m` name different numbers
with the same formula. Lemma 11 says `NCon_U(m)` is true whenever `U`
has no proof of a contradiction of length `c·m²`.

**Proposition 12 (when the gap is only polynomial). [paper, plus the
cited Theorem 6.1.4]** Suppose `T` proves `NCon_U(m)` with proofs of
length at most `P(m)`. Then for a polynomial `q`,

    t^T_k(c·b·log₂ b + c_U)  ≤  q(ℓ) + P(ℓ),     ℓ = t^U_k(b).

*Proof.* Let `φ` name `k` in `U` with proof `π`, `|φ| ≤ b`, `|π| = ℓ`,
and let `f₀ = bin(⌜φ⌝)` with `φ` coded compactly (`O(b log b)` bits,
Report Theorem 6(b)). The `T`-name is

    ψ(x) :≡ ∃p ∃y ( NP_U(p, f₀, x, y)
                    ∧ ∀p′ ∀x′ ∀y′ ( y′ ≤ y ∧ NP_U(p′, f₀, x′, y′) → x′ = x ) ).

In words: `x` is named by `φ` through some `U`-proof that no `U`-proof
of at most the same length contradicts. `|ψ| ≤ c·b·log₂ b + c_U`, and
`ψ` does not mention `ℓ`.

- *Uniqueness is free*, as in Lemma A of the Report. Suppose `(p, y, x)`
  and `(p₁, y₁, x₁)` both satisfy the body. The order is total. If
  `y₁ ≤ y`, the second clause for `(p, y, x)` applied to
  `(p₁, x₁, y₁)` gives `x₁ = x`; otherwise the same with the roles
  exchanged. This is a fixed proof in `PA⁻`, with no property of `NP_U`
  used.
- *Existence, first clause.* `NP_U(bin(π), f₀, bin(k), bin(ℓ))` is a
  true instance, so it has a proof of length polynomial in `ℓ`.
- *Existence, second clause.* Instantiate `NCon_U(bin(ℓ))` at
  `p = bin(π)`, `f = f₀`, `x = bin(k)`, `y = bin(ℓ)`, leaving `p′`,
  `x′`, `y′` as variables. With the first clause and `bin(ℓ) ≤ bin(ℓ)`
  this is exactly `∀p′ ∀x′ ∀y′ (y′ ≤ bin(ℓ) ∧ NP_U(p′, f₀, x′, y′) →
  x′ = bin(k))`. The cost is the proof of `NCon_U(bin(ℓ))`, at most
  `P(ℓ)`, plus instantiations linear in the numerals.

Total: polynomial in `ℓ`, plus `P(ℓ)`. Nothing is asserted about what
`T` can formalise: the proof uses only that true instances of `NP_U`
have short proofs, the hypothesis, and logic. ∎

**Lemma 12a (naming-consistency against consistency). [paper; the
derivations are checked on instances; modulo (F) below]** Let `P_U` be
a polynomial-time machine that accepts `(p, y)` when `p` codes a
`U`-proof of length `y` whose last line is the contradiction, and let
`Con_U(m) :≡ ∀p ∀y ( y ≤ m → ¬ ∃w Run_P(p, y, w) )`: no `U`-proof of a
contradiction has length at most `m`. Assume

- **(F)** `IΣ₁` proves that the two checkers are correct: `C_U` accepts
  `(p, f, x, y)` exactly when `p` is a sequence of formulas of total
  size `y`, each an axiom of `U` or obtained from earlier ones by a
  rule, ending in the naming sentence for `(f, x)`; and likewise for
  `P_U`. Here "is a sequence of formulas, each an axiom or obtained by a
  rule" is the usual primitive recursive predicate.

Then every `T ⊇ IΣ₁` proves

- (i) `∀m ( Con_U(c·m²) → NCon_U(m) )`;
- (ii) `∀m ( NCon_U(m + c) → Con_U(m) )`.

(Primitive recursive arithmetic proves both for the primitive recursive
predicate. (F) carries them over to the run formulas.)

So `T` proves `NCon_U(m)` with proofs of polynomial length exactly when
it proves `Con_U(m)` with proofs of polynomial length.

*Proof.* By (F) it is enough to argue about the primitive recursive
predicate.

(ii) Given a `U`-proof of a contradiction of length at most `m`, append
`0 = 0` and five lines that derive `A` from `0 = 0` and `¬ 0 = 0`, for
`A` the sentence `∀x (x = 0 ↔ x = bin(0))` and again for
`∀x (x = 0 ↔ x = bin(1))`. These are two proofs of length at most
`m + c` in which the formula `x = 0` names `0` and names `1`. (This is
`Explode` in the script. In the system `H`, `c = 137`.)

(i) This is Lemma 11 carried out inside the theory. Lemma 11's proof is
a construction, and it is formalised by naming the functions that build
the proofs and stating, for each, the property proved by induction. The
functions are the ones in the script.

- `Z(d)`, for `d ≥ 1`: the derivation of `0 < bin(d)`. Defined by
  recursion on the digits of `d`: `Z(1)` is the axiom `0 < 1`, and
  `Z(2d′ + β)` is `Z(d′)` followed by one of two fixed blocks of lines
  in which the term `bin(d′)` is plugged in. Property: "`Z(d)` is a
  `PA⁻`-derivation with last line `0 < bin(d)` and length at most
  `c·|d|²`".
- `Inc(a)`, `Add(a, b)`, `Add⁺(a, b)`: the derivations of
  `bin(a) + 1 = bin(a+1)`, `bin(a) + bin(b) = bin(a+b)` and
  `bin(a) + bin(b) + 1 = bin(a+b+1)`. `Add` and `Add⁺` are defined by
  simultaneous recursion on digits: each calls exactly one of the two on
  the numbers with their last digits removed, and appends one of eight
  fixed blocks, chosen by the two last digits and the carry. When one
  argument is `0` or `1` they call `Inc` at most twice and stop.
  Property: each is a `PA⁻`-derivation with the stated last line and
  length at most `c·L²`.
- `Lt(k, k′)`, for `k < k′`: `Z(d)` and `Add(d, k)` for `d = k′ − k`,
  followed by a fixed block (monotonicity of `+`, two rewritings).
  Property: a derivation of `bin(k) < bin(k′)` of length at most
  `c·L²`.
- `H(p, p′)`: `p`, then `p′`, then a fixed block built from their last
  lines (steps 1 and 2 of Lemma 11), then `Lt` for the smaller and the
  larger number, then a fixed block ending in the contradiction.
  Property: if `p` and `p′` are `U`-proofs of the naming sentences for
  the same formula and for `k ≠ k′`, then `H(p, p′)` is a `U`-proof of a
  contradiction of length at most `c·(Len(p) + Len(p′))²`.

Each function is primitive recursive, and each property is a primitive
recursive predicate of the arguments. Each inductive step has the same
form: appending a fixed block of lines to derivations that have the
stated last lines gives a derivation with the stated last line. That
holds because every line of the block is an instance of an axiom scheme
or follows from two earlier lines by a rule, and this depends only on
the shape of the block, not on the terms plugged in. So each property is
proved by induction on a primitive recursive predicate, which is the
induction primitive recursive arithmetic has. The length bounds are sums
of polynomials. `IΣ₁` proves every theorem of primitive recursive
arithmetic. **[classical: Parsons 1970; Hájek and Pudlák 1993, ch. I;
from memory]** Statement (i) is the property of `H` read
contrapositively. ∎

**What the script settles and what it does not.** In the third pass the
fixed blocks were described and not written. They are now written, as
the bodies of the builder functions, and the checker confirms on some
26,000 inputs that each block does what its property says. The step
"this depends only on the shape of the block" is visible in the code:
each builder emits a pattern of lines chosen by at most two digits and a
carry, with the numerals passed through as opaque terms. The induction
inside primitive recursive arithmetic is still an argument on paper, as
any such formalisation is short of a proof assistant.

**About (F), and the formula in the cited theorems. [checked against
the source as far as it could be read]** Proposition 12 needs true
instances of `NP_U` to have short proofs. Lemma 12a needs the theory to
reason about `NP_U` as "is a proof". The third pass left open whether
one formula does both. Reading Pudlák's proof of Theorem 6.1.4 settles
the first half: his numerating formula is the existential closure of a
description of an accepting computation, which is the formula `NP_U`
above, and his `Con_T` is defined from a formula obtained the same way
(Corollary 6.1.6: "there exists formalization `Pr_T` … such that
whenever it is true … [it] has a proof of polynomial length"). The
second half is (F): that `IΣ₁` proves a machine built from a primitive
recursive definition computes what the definition says. This is
standard and is how primitive recursive predicates are shown to be
provably Δ₁ in `IΣ₁`, but it is not written out here, and I did not find
it stated in the part of Pudlák's chapter that could be read verbatim
(to its p. 581). His lower-bound lemma (6.2.1) states its requirements
on `Pr_T` as hypotheses. The section with the upper bound (6.3) was
available only in summary.

Two formalisations of "is a proof" that `T` proves equivalent give
finite consistency statements that `T` proves equivalent with `O(log m)`
extra symbols, so polynomial bounds pass from one to the other. Hence
the cited bounds below apply to `Con_U` as defined here provided `T`
proves Pudlák's proof predicate equivalent to this one, which (F) for
both machines gives. Pudlák measures proof length in symbols over a
finite alphabet, which differs from node count by at most a logarithmic
factor, so polynomial bounds are unaffected.

**What is known about the hypothesis. [classical, cited]**

- `T` proves `Con_T(m)` with proofs polynomial in `m`, for finitely
  axiomatised sequential theories and for schematic ones such as PA and
  ZFC, and not with proofs shorter than `m^ε` (Pudlák 1986; Friedman;
  stated as Theorem 3.1 of Pudlák 2017). So, through Lemma 12a(i),
  Proposition 12 applies to every `U ⊆ T`.
- Whether `T` proves `Con_{T+Con(T)}(m)` with polynomial proofs is
  Pudlák's Problem I (1986), open. The expected answer is no, and a
  negative answer would imply NP ≠ coNP (Pudlák 1986, Proposition 6.2,
  as quoted by Freund and Pakhomov). Pudlák's conjecture CON^N says that
  for every `S` there is a `T` whose finite consistency statements have
  no polynomial `S`-proofs. It is equivalent to the non-existence of an
  optimal proof system.
- Freund and Pakhomov: PA has polynomial proofs of
  `Con_{PA + Con*(PA)}(m)`, where `Con*(PA)` is the slow consistency
  statement, a true sentence that PA does not prove. Hrubeš
  (unpublished, in Pudlák 2017, Theorem 3.4) has a similar example for
  finitely axiomatised theories.

**Corollary 13. [Proposition 12 and Lemma 12a(i), so modulo (F), plus
cited results]**

- (a) There is a strictly stronger theory, `PA + Con*(PA)`, whose naming
  profile is polynomially related to that of PA at the rescaled budget.
  Extra strength need not buy depth.
- (b) If some numbers are super-polynomially shallower in `U = T +
  Con(T)` than in `T`, at the budgets of Proposition 12, then `T` has no
  polynomial-length proofs of `NCon_U(m)`. This much needs only
  Proposition 12. By Lemma 12a(i) it then has none of `Con_U(m)`
  either, so Pudlák's Problem I has a negative answer, and so
  NP ≠ coNP.

So the honest summary of "does depth see the strength of the theory?"
is: at most exponentially (Theorem 10), provably not at all for some
natural strengthenings (Corollary 13(a)), and for `T + Con(T)` proving
that it does is at least as hard as separating NP from coNP (Corollary
13(b)). I do not have a converse: a negative answer to Problem I is not
shown to produce numbers with a depth gap. **[open]**

## 6. Charging names in bits: Bennett's own definition

§§1 to 5 use node count. This section changes the size measure so that
additive slack means something, and then copies Bennett's Definition 1.
Assume in addition that `T` is Σ₁-sound (as in the proof-budgets note,
§3).

**The format.** Fix a universal self-delimiting (prefix) machine `M₀`.
Two things are asked of it beyond universality, both standard: it
simulates any other prefix machine with polynomial overhead in time, and
it has a literal print routine, so that every `k` has a program of
length `log₂ k + 2·log₂ log₂ k + c` that prints it in time polynomial in
`log₂ k`. Let `Run₀(u, z, y)` be the Δ₀ formula "`z` codes a halting run
of `M₀` on program `u` with output `y`", as in Appendix A.3 of the
proof-budgets note, and put

    μ(u, y) :≡ ∃z Run₀(u, z, y).

So `μ(bin(p), x)` names the output of a halting program `p` by a true
Σ₁ sentence for existence and, for uniqueness, the fixed lemma of `IΣ₁`
that two runs on the same program have the same output. (This is the
form used in Proposition 5 of the proof-budgets note. The wrapped form
of the Report's Lemma A would also name the output, in `PA⁻`, but its
bounded-universal clause has no short proof in general, and the
proof-length statements below need short proofs.)

Fix a binary code `e` for formulas `χ(y, x)` with two free variables,
and a stop word `■`, such that the code words `e(χ)` together with `■`
form one prefix-free set and `|e(χ)| ≤ c·|χ|·log₂|χ|`. (Write the
formula in a fixed self-terminating syntax, with variable indices in
binary, and reserve one opening pattern for `■`.) A **bit name** is a
binary string

    n = e(χ_j) … e(χ_1) ■ p,        j ≥ 0,   p a program on which M₀ halts.

It stands for the formula `Φ_n` defined by recursion on the number of
stages:

    Φ_{■p}(x)    :≡ μ(bin(p), x),
    Φ_{e(χ)n}(x) :≡ ∃y ( Φ_n(y) ∧ χ(y, x) ).

(Here `bin(p)` is the numeral of the number whose binary expansion is
`1p`, and each stage uses a fresh bound variable.) So a bit name is a
program that supplies data, followed by a pipeline of formulas applied
to it, the first code word being the last stage applied. `n` **names**
`k` when `T` proves that `Φ_n` names `k`. Its cost is its length `|n|`
in bits.

Bit names form a prefix-free set. If `n` is a prefix of `n′`, both parse
into the same code words up to and including `■`, because those code
words form a prefix-free set. The remainders are two programs on which
`M₀` halts, one a prefix of the other, so they are equal. If `T` proves
that `Φ_n` names something, then `T` proves `M₀` halts on `p`, and by
Σ₁-soundness it does. So the strings with a naming proof are bit names.

Every formula `φ(x)` is a bit name at cost `|e(φ)| + O(1)`: one stage
that ignores its input, on a fixed trivial program. Every program for
`M₀` is a bit name at cost `|p| + O(1)`: no stages.

Definitions, with `K` the prefix Kolmogorov complexity:

- `B_T(k)` = the length of the shortest bit name of `k`.
- A bit name `n` is **`s`-incompressible** when `K(n) > |n| − s`.
- **Depth, Bennett's Definition 1:**
  `depth*_T^s(k) = min { |π| : π is a naming proof for (n, k), n is s-incompressible }`.
- Depth, tentative definition 0.2: the same minimum over names with
  `|n| ≤ B_T(k) + s`.

**Theorem 14 (calibration). [paper]** `K(k) − c_T ≤ B_T(k) ≤ K(k) + c`
for all `k`, where `c` does not depend on `T`.

*Proof.* Right: if `p` is a shortest program for `k`, then `■p` names
`k`: `∃z Run₀(bin(p), z, bin(k))` is a true Σ₁ sentence, so provable,
and uniqueness is the fixed lemma of `IΣ₁`. The constant is `|■|`.
Left: the map from a bit name to the number it
names is partial computable (search the proofs of `T`) with a
prefix-free domain. ∎

Compare Report §8, where naming complexity and Kolmogorov complexity
agree only up to a constant factor and a logarithm. The factor came from
writing data inside a formula at about six symbols per bit, and the
logarithm from variable names. A raw data part removes both. The theory
still enters only through a constant.

**Proposition 15 (basic facts). [paper; (c) modulo A4]**

- (a) A shortest bit name of `k` is `c_T`-incompressible. So
  `depth*_T^s` is defined for `s ≥ c_T`.
- (b) Every bit name of `k` of length at most `B_T(k) + s` is
  `(s + c_T)`-incompressible. So `depth*_T^{s+c_T}(k)` is at most the
  tentative-0.2 depth at slack `s`. Definition 1 admits more names.
- (c) Random numbers are shallow at small significance. Let `ℓ(k) ≤
  log₂ k + 2·log₂ log₂ k + c` be the length of the literal
  self-delimiting program for `k`. If `K(k) ≥ ℓ(k) − s`, then
  `depth*_T^{s+c}(k) ≤ q(log₂ k)` for a polynomial `q`. All but a
  fraction `2^{-j}` of the numbers with `m` digits satisfy this with
  `s = j + 2·log₂ m + c`.

*Proof.* (a), (b) If a bit name `n` of `k` had a description `d` with
`M₀(d) = n` and `|d| < B_T(k) − c_T`, then one stage `χ_V` saying "`x`
is the number named by the bit name `y`" applied to `d` would be a bit
name of `k` shorter than `B_T(k)`. (`χ_V(y, x)` is `∃z Run_V(y, z, x)`
for the machine `V` that searches the proofs of `T`. The run on `n`
exists, so `T` proves it, and its output is unique by the fixed lemma.
No bound on the proof length is needed here. The constant is
`|e(χ_V)| + |■|`, which depends on `T` through `V`.) So
`K(n) ≥ B_T(k) − c_T`. (c) The name is `■` followed by the literal
program. It is `(s + c)`-incompressible because `k` is recoverable from
it, and its naming proof verifies a run of `M₀` that takes time
polynomial in `log₂ k` (Lemma A4). ∎

This is the statement that failed in §1: with node count one cannot show
that typical numbers are shallow at small additive slack.

**Theorem 16 (slow growth, no loss term). [paper, modulo A4]** Let `f`
be computable, and let `χ_f(y, x)` say "the machine for `f` on input `y`
halts with output `x`". There are a constant `c` and a polynomial `q_f`
such that for all `k` and `s`,

    depth*_T^{s + |e(χ_f)| + c}(f(k))  ≤  c·depth*_T^s(k) + q_f(time_f(k) + log₂ k).

*Proof.* Let `n` be an `s`-incompressible name of `k` with naming proof
`π` of minimal length. Put `n′ = e(χ_f) n`, which appends the stage
`χ_f` to the pipeline. By the recursive definition, `Φ_{n′}(x)` is
literally `∃y (Φ_n(y) ∧ χ_f(y, x))`, the formula `φ′` of Lemma 6 with
`φ = Φ_n`, and Lemma 6 gives a naming proof for `(n′, f(k))` of the
stated length. `n` is obtained from `n′` by deleting
the first code word, so `K(n) ≤ K(n′) + c`. Hence

    K(n′) ≥ K(n) − c > |n| − s − c = |n′| − |e(χ_f)| − s − c. ∎

This is Bennett's deterministic law with proof length for time: the
significance goes from `s` to `s` plus the description length of `f`
plus a constant, whatever `f` does to the information in `k`.
**[expected]** The probabilistic form (a stage drawn at random with
probability `2^{-|e(χ)|}` raises depth from significance `s₁` to `s₂`
with probability at most about `2^{-(s₂−s₁)}`) should follow by
Bennett's argument. Not written out.

**Theorem 17 (deep numbers). [paper]** Let `g` be computable. There are
a constant `c_g` and numbers `k_N < 2^N` with `K(k_N) ≤ K(N) + c_g` such
that every bit name of `k_N` with a naming proof of length at most
`g(N)` is compressible by at least `N − K(N) − c_g` bits. Hence

    depth*_T^s(k_N) > g(N)      for all s ≤ N − K(N) − c_g.

*Proof.* For a number `k` let `W(k)` be the sum of `2^{-|n|}` over the
bit names `n` of `k` that have a naming proof of length at most `g(N)`.
The strings with naming proofs form a prefix-free set, and each names
one number, so the `W(k)` sum to at most 1 and some `k < 2^N` has
`W(k) ≤ 2^{-N}`. Let `k_N` be the least. It is computable from `N`:
a proof of length `t` only concerns names of length `O(t log t)`. The
set `F` of names of `k_N` with such proofs is computable from `N` and
has `Σ_{n∈F} 2^{-(|n| − N)} ≤ 1`. By the Kraft–Chaitin construction each
`n ∈ F` has a description of `|n| − N` bits given `N`, so
`K(n) ≤ |n| − N + K(N) + c_g`. ∎

Bennett's diagonal strings are deep "at significance level
`n − H(T) − O(log n)`", by the same argument. Here the range is
`N − O(log N)`. By Proposition 15(b) the same numbers are deep in the
tentative-0.2 sense.

**Theorem 18 (naming depth against Bennett's depth, and across
theories). [paper, modulo A4]** Let `D_s(k)` be Bennett's depth
(Definition 1) for the machine `M₀`. There are constants `c`, `c_T` and
a polynomial `q` such that, writing `ℓ = depth*_T^s(k)`:

- (a) `depth*_T^{s+c}(k) ≤ q(D_s(k))`;
- (b) `D_{s + 3·log₂ ℓ + c_T}(k) ≤ 2^{c·ℓ·log₂ ℓ}`;
- (c) for a second Σ₁-sound theory `U`, with `ℓ = depth*_U^s(k)`:
  `depth*_T^{s + 3·log₂ ℓ + c_U}(k) ≤ q(2^{c·ℓ·log₂ ℓ})`.

*Proof.* (a) An `s`-incompressible program `p` for `k` running in time
`τ` gives the bit name `■p`, which is `(s+c)`-incompressible, with a
naming proof that verifies the run. (b) Let `n` be an `s`-incompressible
name with a naming proof of length `ℓ`. The program "read the length of
`n` (in `2·log₂|n| + 1` self-delimiting bits), read `n`, search the
proofs of `T` for the number `Φ_n` names" halts within
`2^{O(ℓ log ℓ)}` steps, and `n` is recoverable from it, so it is
incompressible by `s + 2·log₂|n| + c_T` bits. And `|n| = O(ℓ log ℓ)`:
the proof contains `Φ_n`, which contains every stage and the numeral
`bin(p)`, and `|e(χ)| ≤ c·|χ|·log₂|χ|`. So
`2·log₂|n| ≤ 3·log₂ ℓ + c`. (c) Apply (b) to `U` and
then (a) to `T`. ∎

So in bits there is no rescaling of the budget, only a logarithmic loss
of significance. Whether the loss is necessary is open, but it has a
definite source. A bit name is
valid only if its data program halts. A machine reading a bit name
cannot tell where the data ends without running the data program, and
the theory may have proved that program halts without running it (this
is the function `G_T` of the proof-budgets note, §3, which does depend
on the strength of the theory). Writing the length of the name in front
avoids running anything, at the cost of `2·log₂|n|` bits.

**Why the data must be self-delimiting. [paper]** If the data part were
an arbitrary string, its length would be a free channel. A random string
of length `k`, with a stage that outputs the length of its input, would
be an incompressible name of `k` with a proof polynomial in `k`. Every
number would then have Definition-1 depth at most polynomial in itself,
and the diagonal numbers of Theorem 17 could not exist beyond
exponential thresholds. Bennett's programs are self-delimiting for the
same reason.

**What carries over from §§2 to 5. [expected]** Proposition 12 should
carry over with the same logarithmic loss of significance as Theorem
18(b). The uncomputability statements carry over unchanged. The
node-count results of §§2 to 5 remain as stated for the size measure the
Lean development uses.

## 7. Examples

Budgets are in symbols, proofs in total size. "Length" is `log₂ k`.

| number | budget | proof length | verdict | status |
|---|---|---|---|---|
| any `k` | `6·log₂ k + 3` (literal name) | `≤ c·log₂ k` | every number is shallow at its literal budget | [paper] Prop. 1 |
| `2^{2^j}` | `c₀·j + c₀` | `≤ C·8^j = C·(log₂ k)³` | shallow relative to length | [paper] proof-budgets, App. A.2 |
| output of program `d` after `τ` steps | `6·|d| + c` | `≤ q(τ + |d|)` | as shallow as the program is fast | [paper, modulo A4] Prop. 4(a) |
| `2^h`, `h` = halting time of program `e` | `C + 6·log₂ e` | polynomial in `h = log₂ k` | enormous, yet shallow relative to length | [paper, modulo A4] |
| the record `Big_T(n)` | `n + s` | between `log₂ Big_T(n)` and `Big_T(C + c(n+s)·log(n+s))` | deep in absolute terms; relative to length not settled | [paper] / [open] |
| diagonal `k_n` (Theorem 3) | every `b ≤ n` | `> g(n)`, with only `c·n·log n` digits | deep relative to length, in every theory | [paper] |
| halting table `H_N = Σ 2^e` over halting `e ≤ N` | well below `N` | beyond every computable function of `N` | deep relative to length | [expected] |

Notes on the rows.

- **`2^h`.** The name says "`x` is `2` to the length of the halting run
  of program `e`". The proof exhibits the run, which has `h` steps, and
  the numeral has `h` digits. If `e` is a Busy Beaver champion this
  number is far beyond anything computable in its budget, and its proof
  is still polynomial in its own length. Hugeness does not force depth
  relative to length. (Whether its budget is within a small additive
  slack of `D_T(2^h)` cannot be checked, per §1.) Bennett makes the
  matching remark about the halting probability Ω: it is "ambitious but
  shallow".
- **Records.** Any proof naming `Big_T(n)` contains its numeral, so it
  is longer than every computable function of `n`. That is forced by
  length alone. The upper bound holds because "the length of the
  shortest naming proof for `φ`" is a partial computable function of
  `φ`, so its values are named within `O(n log n)` symbols (Report,
  Theorems 2 and 6(b)). Whether the shortest proof is polynomial in
  `log₂ Big_T(n)` or much longer is not settled here. The remark in
  `COMPLEXITY-AND-ENTROPY.md` §4, that such numbers are "the deepest
  objects there are at their description length", is right for absolute
  depth and unproved for depth relative to length.
- **Halting table.** `H_N` has `N + 1` digits and a name of `O(log N)`
  symbols (from `N` and the count of halting programs, by Theorem 2 of
  the Report). The classical analogue is that initial segments of the
  halting sequence are deep at every computable time bound. Bennett
  (1988, §3) puts the depth of the first `2^n` bits of the halting set
  at Busy Beaver values of about `n`, and calls the sequence strongly
  deep (see also Juedes, Lathrop and Lutz). The time-bounded
  incompressibility behind this is Barzdin's lemma: for each
  computable `t` some computably enumerable set has initial segments of
  time-`t` complexity linear in their length. Transferring this through
  Proposition 4(c) should give the row, for a program numbering in which
  hard-wiring an input costs its bit length. Not written out.

## 8. Summary

| statement | form | status |
|---|---|---|
| profile floor and literal ceiling | `log₂ k ≤ t_k(b)`; `t_k(6 log₂ k + 3) ≤ c log₂ k` | [paper] |
| depth is not computable, is approximable from below | Prop. 2 | [paper] |
| deep numbers at every computable threshold | Theorem 3 | [paper] |
| program fast ⇒ proof short | `t_k(6b+c) ≤ q(τ_k(b)+b)` | [paper, modulo A4] |
| proof short ⇒ nondeterministic program fast | Prop. 4(b) | [paper] |
| proof short ⇒ program at most exponentially slow | Prop. 4(c) | [paper] |
| P = NP ⇒ naming depth ≈ running-time depth | Cor. 5 | [paper, modulo A4] |
| slow growth, profile form | `t_{f(k)}(b+C_f) ≤ c·t_k(b) + q_f(…)` | [paper, modulo A4] |
| slow growth, slack form | slack grows by `C_f + D_T(k) − D_T(f(k))` | [paper, modulo A4] |
| loss term necessary (node count, tentative-0.2 form)? | | [open] |
| bit names: cheapest name costs `K(k) + O(1)` | Theorem 14 | [paper] |
| bit names: random numbers shallow at small significance | Prop. 15(c) | [paper, modulo A4] |
| bit names, Definition 1: slow growth with no loss term | Theorem 16 | [paper, modulo A4] |
| bit names, Definition 1: diagonal numbers deep up to significance `N − K(N) − c` | Theorem 17 | [paper] |
| bit names against Bennett's `D_s` | polynomial one way, exponential the other, `O(log)` significance | [paper, modulo A4] |
| stronger theory, fixed name | speed-up beyond every computable function | [classical] |
| any two theories, same number | at most exponential apart | [paper, modulo A4] |
| two short naming proofs for different numbers give a contradiction of length `c·ℓ²` | Lemma 11 | [paper; checked on instances] |
| polynomial apart if `T` feasibly proves that short `U`-proofs never name two numbers with one formula | Prop. 12 | [paper + cited] |
| inside `T`, that statement and `Con_U(m)` imply each other up to squaring `m` | Lemma 12a | [paper; derivations checked on instances; modulo (F)] |
| super-polynomial gap for `T + Con(T)` | would imply NP ≠ coNP | [Prop. 12, Lemma 12a(i), modulo (F), + cited] |

## 9. What might be new, and what to check

Literature check (2026-11-24, web search; sources read through extracted
quotations, as listed under References). Logical depth has many variants
built on running time: Bennett's, basic and distinguishing computational
depth, depth as randomness deficiency, dimensional and feasible depth. I
found none built on proof length in a formal theory, and nothing
relating depth to finite consistency statements. Bennett motivates depth
as "the amount of mathematical or other work plausibly done by its
originator" but does not define it through proofs. The search was short,
and "not found" is weak evidence.

Candidates for something of our own, all modest:

1. The definition (profile and depth for provable naming) and the
   sandwich between nondeterministic and deterministic running-time
   depth (Proposition 4, Corollary 5). The sandwich is the proof-budgets
   Proposition 5 with two axes kept apart.
2. Theorem 10 with the contrast to Gödel speed-up: unbounded speed-up
   for a name, at most exponential for a number. Short once seen.
3. Lemma 11, Proposition 12 and Corollary 13, the link from
   theory-dependence of depth to Pudlák's Problem I. This is the least
   expected item.
4. Theorem 7 with Corollary 8. Routine, and parallel to Antunes et al.,
   Theorem 14.
5. §6: bit names, the calibration `B_T = K + O(1)`, and the transfer of
   Bennett's Definition 1, his deterministic law and his diagonal
   example to proof length. The proofs are Bennett's with one extra
   ingredient each (Lemma C of the Report, Lemma 6). The remark that
   name validity is a halting fact, which theories certify at different
   speeds, and the resulting logarithmic loss in Theorem 18, seem to be
   specific to proofs.

Done in the second pass (2026-11-24):

- Lemma A4 has a citation: Pudlák, "The lengths of proofs", Theorem
  6.1.4 (a relation is NP exactly when some formula numerates it in
  Robinson arithmetic with polynomial-length proofs), Lemma 6.1.5 and
  Corollary 6.1.6. The proof given there is a sketch, and the theorem
  is stated for *some* numerating formula. The uses here need the
  formula to be a Δ₀ description of the computation, which is what the
  sketch constructs.
- Bennett (1988) read. His definitions and Theorem 1 are quoted in §1
  and §4. Two corrections to the first pass: the definition of §1 is
  his tentative definition 0.2, not something he never considered, and
  his slow growth law is stated probabilistically, with the
  deterministic case as a consequence.
- Proposition 12 written out, with Lemma 11 proved.

Done in the third pass (2026-11-24):

- Proposition 12 restated with naming-consistency `NCon_U` as its
  hypothesis. Its proof now asserts nothing about formalisation.
- Lemma 12a added: inside `T`, `NCon_U` and `Con_U` imply each other up
  to squaring the length. The formalisation of Lemma 11 is laid out as
  four recursive constructions with their induction properties.

Done in the fourth pass (2026-11-24):

- §6 re-read sceptically. Six repairs, none changing a statement beyond
  a constant: `μ` is now the plain run formula with the `IΣ₁` uniqueness
  lemma (the wrapped form of the Report has no short proofs, which
  Proposition 15(c) and Theorem 18(a) need); `Φ_n` is defined by
  recursion in nested form, so Theorem 16 applies Lemma 6 literally; the
  stage code and the stop word are required to form one prefix-free set,
  with `|e(χ)| ≤ c·|χ|·log₂|χ|`; `M₀` is required to simulate with
  polynomial overhead and to have a literal print routine; the constants
  of Proposition 15(a), (b) depend on `T`; and the logarithmic loss in
  Theorem 18 is no longer called necessary. The Kraft–Chaitin step of
  Theorem 17 and the prefix-freeness of bit names were rechecked and
  stand.
- Lemma 11 and Lemma 12a: a proof system fixed, the derivations written
  as `naming-depth/collision_check.py`, and checked on instances (§5).
  Lemma 11's step 3 now derives `bin(k) < bin(k′)` directly, which
  avoids a contraposition.
- Pudlák's Theorem 6.1.4 re-read with its proof: the numerating formula
  is the run formula used here. What remains is assumption (F) of Lemma
  12a.

To check before any public use:

- Assumption (F) of Lemma 12a: that `IΣ₁` proves the proof-checking
  machines correct against the primitive recursive definition of "is a
  proof", and with it that Pudlák's proof predicate and ours are
  provably equivalent. Standard, not written out. Corollary 13 depends
  on it. Proposition 12 and Lemma 11 do not.
- Lemma 12a(i): the induction inside primitive recursive arithmetic is
  argued on paper. The script checks instances of every block, not the
  induction.
- Pudlák's upper bound for `Con_T(m)` (his §6.3) was read only in
  summary, and two summaries disagreed on details. The statement used
  here is the one quoted as Theorem 3.1 of Pudlák 2017.
- That `IΣ₁` contains primitive recursive arithmetic is cited from
  memory (Parsons).
- Lemma 6: the bookkeeping is claimed to be linear and is not written
  line by line.
- §6 has had two passes by the same author. A reader who did not
  write it has not checked it.
- Pudlák's Problem I and its link to NP ≠ coNP are quoted from Freund
  and Pakhomov's introduction. The part of the Handbook chapter read in
  full (to its p. 581) does not state it. The equivalence of CON^N with
  optimal proof systems is from a summary of Pudlák (2017).
- Gödel speed-up in the form used in §5 is Pudlák's Handbook Theorem
  7.1.1 and Corollary 7.1.2 (Ehrenfeucht and Mycielski), read only in
  summary.
- The halting-table row of §7 is expected, not proved.

Open questions, in rough order of interest:

- A converse to Corollary 13(b): does a negative answer to Problem I
  give numbers with a super-polynomial depth gap?
- Is the logarithmic loss of significance in Theorem 18 necessary?
- The probabilistic slow growth law for bit names (after Theorem 16).
- Is the loss term in Theorem 7 necessary?
- Are the records `Big_T(n)` deep relative to their length?
- Instability in the slack: Antunes, Souto and Vitányi show Bennett's
  depth can drop from incomputable to computable between consecutive
  significance levels. Does the naming profile have such cliffs?

## References

- C. H. Bennett, "Logical depth and physical complexity", in *The
  Universal Turing Machine: A Half-Century Survey* (1988), pp. 227–257.
  [read through extracted quotations: §3 definitions, Lemma 3, Theorem
  1, the examples on pp. 18–21; the scan is garbled in places]
- L. Antunes, A. Souto, P. Vitányi, "On the logical depth function",
  arXiv:1301.4451; later version "On logical depth and the running time
  of shortest programs", arXiv:1310.6976. [read via summary]
- L. Antunes, L. Fortnow, D. van Melkebeek, N. V. Vinodchandran,
  "Computational depth: concept and applications", *Theoretical Computer
  Science* 354 (2006). [read via summary: Definitions 4, 13, Theorem 14]
- L. Antunes, A. Matos, A. Souto, P. Vitányi, "Depth as randomness
  deficiency", arXiv:0809.2546. [read via summary]
- D. Juedes, J. Lathrop, J. Lutz, "Computational depth and
  reducibility", *Theoretical Computer Science* 132 (1994). [memory]
- J. Barzdin, "Complexity of programs to determine whether natural
  numbers not greater than n belong to a recursively enumerable set",
  *Soviet Math. Dokl.* 9 (1968); see also E. Daylight, W. Koolen,
  P. Vitányi, "Time-bounded incompressibility of compressible strings
  and sequences", arXiv:0809.2965. [memory; second item found by search,
  not read]
- P. Pudlák, "The lengths of proofs", in *Handbook of Proof Theory*
  (1998), ch. VIII. [read through extracted quotations to p. 581:
  Definition 6.1.3, Theorem 6.1.4 with its proof sketch, Lemma 6.1.5,
  Corollary 6.1.6, the definition of `Con_T`, Lemma 6.2.1; later
  sections, including the upper bound of §6.3, in summary only. The
  extracted text drops most mathematical symbols.]
- P. Pudlák, "On the length of proofs of finitistic consistency
  statements in first order theories", Logic Colloquium '84 (1986).
  [via the items before and after]
- P. Pudlák, "Incompleteness in the finite domain", arXiv:1601.01487
  (2017). [read via summary: Theorem 3.1, conjectures CON^N, CON^{N+},
  Theorem 3.4]
- A. Freund, F. Pakhomov, "Short proofs for slow consistency",
  arXiv:1712.03251. [read via summary]
- C. Parsons, "On a number-theoretic choice schema and its relation to
  induction", in *Intuitionism and Proof Theory* (1970); P. Hájek,
  P. Pudlák, *Metamathematics of First-Order Arithmetic* (1993), ch. I.
  [memory]
- J. Krajíček, P. Pudlák, "Propositional proof systems, the consistency
  of first order theories and the complexity of computations", *JSL* 54
  (1989). [memory]
- E. Allender, H. Spakowski, "Avoiding simplicity is complex", ECCC
  TR10-055. [abstract read, for the proof-budgets note]
- This project: `PROOF-BUDGETS-AND-COMPLEXITY.md` (Propositions 1, 2, 5,
  Appendix A), `PROVABLE-NAMING-REPORT.md` (Theorems 1, 2, 6, Lemmas A
  and C, Corollary 7), `COMPLEXITY-AND-ENTROPY.md` §4.
