# Proof budgets and complexity classes

*Written 2026-11-24. A sequel to `COMPLEXITY-AND-ENTROPY.md` §5.3 and
`PROVABLE-NAMING-REPORT.md`. Question: if we cap how long a proof may
be, does provable naming line up with P, NP, EXP and the polynomial
hierarchy?*

Tags as elsewhere: **[Lean]** machine-checked here; **[paper]** argued
here, not machine-checked (full proofs of Propositions 2 and 5 are in
Appendix A); **[checked]** written out as a Hilbert-style proof and
checked line by line by a script, for the instances stated;
**[classical]** textbook, cited; **[analogy]** a resemblance, not a
theorem. Nothing here is Lean-checked.

---

## 0. The answer in plain language

The idea was: unbounded proof search is what makes `Big_T` a Busy Beaver
function, so cap the proof length and you should get computable
functions sorted by complexity class, with P versus NP showing up
somewhere. Working it out, three things happen, none of them quite the
expected one.

1. **If the proof has to write the number down, the budget is the
   ceiling.** Boolos-style naming asks for a proof of
   `∀x (φ(x) ↔ x = k̄)`, and that sentence contains the numeral for `k`.
   A proof of length `t` therefore names numbers of size at most about
   `t` (unary numerals) or `2^t` (binary numerals). With a proof budget
   the formulas stop mattering; the budget does all the work. The
   capped function is roughly the budget itself, so it does not give a
   ladder of growth rates matching P, EXP and so on. Short proofs do
   reach the ceiling, up to a constant factor (unary) or a constant
   factor in the exponent (binary), using lemmas with variables that
   are proved by doubling. **[paper; checked for instances]**

2. **If the proof only has to show that the number exists, the old ε₀
   guess comes back.** Ask instead for a short proof that a Σ₁ formula
   picks out exactly one number, and read the number off by computing
   it. That function is computable and outgrows everything the theory
   can prove total. For PA that is the ε₀ level the project first
   guessed for `Big_PA`. Here, unlike before, stronger axioms give a
   genuinely faster function. This is close to Simmons's `f_A{n}`.
   **[paper]** But drop the Σ₁ restriction and even tiny proofs reach
   Busy Beaver values and beyond, because classical logic can prove
   "the maximum exists" without finding it. **[paper]**

3. **P versus NP lives in the *complexity measure*, not the big-number
   function.** Read backwards, item 1 gives a complexity measure: the
   cost of naming `k` is the size of the formula plus the logarithm of
   the proof length. That measure sits between Levin's `Kt` (programs
   charged for log running time) and its nondeterministic version
   `KNt`. Allender and Spakowski showed that `Kt` and `KNt` are
   polynomially related exactly when NEXP ⊆ EXP/poly. So showing that
   proof-charged naming is ever substantially cheaper than `Kt` would
   prove NEXP ⊄ EXP/poly, an open separation. **[paper, modulo one
   cited lemma, plus a cited theorem]**

And the polynomial hierarchy: bounding the quantifiers in a naming
formula does not cap the size of the number named, because the named
number is itself the free variable and can be as large as it likes. A
Δ₀ formula already names Busy Beaver values when truth is the judge.
The exact match between bounded quantifiers and the polynomial
hierarchy (Wrathall, Buss) is about *sets of inputs*, and naming has no
input. **[paper for the first part, classical for the match]**

**What this says about P versus NP: nothing new.** It gives one more
reformulation of an open exponential-time question (item 3), and an
honest account of why the large-number ladder and the polynomial
hierarchy look alike but do not line up.

---

## 1. Setting

As in `PROVABLE-NAMING-REPORT.md` §2: language `0, 1, +, ·, =, <`, base
theory `PA⁻`, size `|φ|` = number of syntax-tree nodes. `T ⊇ PA⁻` is
consistent and computably axiomatized, with a fixed proof system (say
Hilbert-style), and `|π|` is the number of symbols in the proof `π`.
Proofs are checked in time polynomial in `|π|`.

Two naming relations. Both name at most one number when `T` is
consistent (Report, Theorem 1, which only uses that distinct numerals
are provably distinct).

- **Unary target:** `π ⊢ ∀x (φ(x) ↔ x = k̄)`, with `k̄` the unary numeral
  (size about `2k`). This is the relation used in the Lean development
  (`NamesIn`, `AnyTheory.lean`).
- **Binary target:** `π ⊢ ∀x (φ(x) ↔ x = bin(k))`, with `bin` as in
  `Binary.lean` (size at most `6·log₂ k + 1`).

Without a proof budget these give the same function `Big_T`, since
`PA⁻ ⊢ bin(k) = k̄` (`val_bin` plus completeness). **[paper, from Lean
facts]** With a budget they differ, and the binary one is the
interesting one.

For a budget function `t : ℕ → ℕ`, define

    Big_T^t(n) = the largest k such that some φ with |φ| ≤ n
                 has a proof π with |π| ≤ t(n) naming k   (0 if none).

## 2. Writing the answer caps the answer

**Proposition 1 (budget is the ceiling). [paper]** For every `n`:

- unary target: `Big_T^t(n) ≤ t(n)/2`;
- binary target: `Big_T^t(n) < 2^{t(n)}`.

*Proof.* The last line of `π` is the naming sentence, which contains the
numeral, so `|π| ≥ |k̄| ≈ 2k`, respectively `|π| ≥ |bin(k)| ≥ log₂ k`. ∎

**Proposition 2 (and the ceiling is reached up to a constant). [paper;
checked for instances]** There is a constant `C` such that for every
`T ⊇ PA⁻` and every `n` with `t(n) ≥ C`:

- unary target: if `n ≥ 4·log₂ t(n) + 3`, then `Big_T^t(n) ≥ t(n)/C`;
- binary target: if `n ≥ 10·log₂ t(n) + 5`, then
  `Big_T^t(n) ≥ 2^{t(n)/C}`.

*Proof.* Appendix A.2a. The tool is a lemma with free variables, proved
by *doubling*: from `∀z ∀u (z + Sⁿ(u) = Sⁿ(z + u))`, where `Sⁿ(u)` is
`u + 1 + … + 1`, the same statement for `2n` follows by instantiating it
twice and chaining, a fixed number of lines of size `O(n)`. So the
lemmas for `n = 1, 2, 4, …, 2^a` cost `O(2^a)` together. Unary: with them
`PA⁻` proves `bin(2^a) = (2^a)‾` in `O(2^a)` symbols, so the formula
`x = bin(2^a)`, of size `4a + 3`, names `2^a` (Lemma A6). Binary: the
same trick for `∀w ∀z (Dⁿ(w)·z = Dⁿ(w·z))`, where `D(s) = (1+1)·s`,
gives each squaring `bin(2^{2^i})·bin(2^{2^i}) = bin(2^{2^{i+1}})` in
`O(2^i)` symbols, and a formula `χ_j(x)` of size `10j + 5` saying "`x` is
2 squared `j` times" names `2^{2^j}` with a proof of length `O(2^j)`
(Lemma A7). No induction is used, so the bounds hold for every
`T ⊇ PA⁻`. The script `proof-budgets/doubling_check.py` writes these
proofs out in a fixed Hilbert system and checks every line, for
`a ≤ 20` and `j ≤ 16`. The measured lengths are about `662·2^a` (unary)
and `10,900·2^j` (binary). ∎

So `Big_T^t(n)` is pinned between `t/C` and `t/2` (unary), or between
`2^{t/C}` and `2^t` (binary), once `n` is a constant multiple of
`log t(n)`. The formulas stop mattering and the budget decides
everything. In particular there is no family "P-naming, EXP-naming, ..."
whose growth rates are separated the way the classes are; the growth is
whatever budget you feed in.

**Remark (what the first version had, and what the toy shows). [paper]**
The first version of this proposition gave only `√(t/C)` and
`2^{(t/C)^{1/3}/2}`. Its proofs were equations between closed numerals,
proved one binary digit at a time (Lemmas A1 to A3, which are still
used by Lemma A4). A proof that states no lemma with a free variable
pays for every doubling separately. The toy computations in
`NAMING-RECORDS-SMALL-SYSTEM.md`, whose proofs are rewriting chains with
no variables, show exactly this: records near `0.7·√t` (unary) and
`2^{0.29·√t}` (binary). The gap between `√t` and `t` there is the value
of quantified lemmas, not a property of the budget.

**Where the Busy Beaver behaviour went. [paper]** It is in the budget.
Lacerda (arXiv:1406.1808) bounds the shortest proof of a provable
sentence of length `n` by a Busy Beaver function of `O(n)`. Combined
with Proposition 1, `Big_T(n) = Big_T^{t}(n)` for a budget
`t(n) = BB(O(n log n) + c_T)`. The unbounded function is a capped
function whose cap is itself Busy Beaver sized. Proofs that name
Busy Beaver values are, necessarily, Busy Beaver long.

**The decision problem. [paper]** For a polynomial budget `p`, the
question "is `Big_T^p(n) ≥ k`?" (input `1^n` and `k` in binary) is in
NP: guess `φ` and `π`, check. The function `n ↦ Big_T^p(n)` is computable
in polynomial time with an NP oracle (binary search on `k`), and in
exponential time without one. But this problem is **not NP-hard unless
the polynomial hierarchy collapses**: an input of length `L` only
involves `n ≤ L`, and the `L` values `Big_T^p(1..L)`, each of `O(p(L))`
bits, are polynomial advice that decides it. So it is in P/poly, and
NP-hardness would put NP in P/poly, collapsing the hierarchy to its
second level (Karp–Lipton). The NP-completeness sits one level down, in
the bounded-provability problem "does `ψ` have a proof of length
`≤ m`?" with `m` in unary, which is NP-complete for any reasonable proof
system. **[classical]** That problem is the one Gödel described to
von Neumann in 1956, asking whether it could be solved in time linear
or quadratic in `m`; it is the earliest known statement of the P versus
NP question.

## 3. Proving existence only: provable totality and ε₀

Change what the proof has to show. Assume now that `T` is Σ₁-sound
(true Σ₁ sentences it proves are true; PA and ZFC qualify, granting
their soundness). For a Σ₁ formula `φ(x)`, say `φ` **defines** a
number if `T ⊢ ∃!x φ(x)`. The number is the unique `x` with `ℕ ⊨ φ(x)`:
existence by Σ₁-soundness, uniqueness because a false Π₁ sentence
provable in `T` would make `T` inconsistent. Put

    G_T(m) = the largest number defined by a Σ₁ formula of size ≤ m
             whose ∃! has a T-proof of length ≤ m.

**Proposition 3. [paper]**

- (a) `G_T` is computable.
- (b) For every function `f` that `T` proves total (via a Σ₁ graph
  `θ` with `T ⊢ ∀n ∃!y θ(n, y)`), there is `C` with
  `G_T(C + C·log₂ n) ≥ f(n)` for all `n`.
- (c) `T` does not prove `G_T` total.
- (d) If `T ⊆ U`, both Σ₁-sound, and `U` proves that `T` is Σ₁-sound,
  then `U` proves `G_T` total, so `G_U(C + C·log₂ n) ≥ G_T(n) + 1`.

*Proof.* (a) List the proofs of length `≤ m`; for each Σ₁ formula
`φ` with a proof of `∃!x φ(x)`, search for the witness, which exists.
(b) Instantiate the proof of `∀n ∃!y θ(n,y)` at `bin(n)`: a proof of
length `C + O(log n)` that `θ(bin(n), y)` defines `f(n)`. (c) If it did,
apply (b) to `G_T + 1`: `G_T(C + C log n) ≥ G_T(n) + 1`, contradicting
monotonicity once `C + C log n ≤ n`. (d) `U` can run the procedure of
(a) and prove it halts; then (b) for `U`. ∎

For PA, the functions PA proves total are exactly those eventually
dominated by some level `F_α`, `α < ε₀`, of the fast-growing hierarchy.
**[classical: Kreisel, Wainer]** So by (b) `G_PA` outgrows every `F_α`
with `α < ε₀`: this is the **ε₀ rung** the project first expected for
`Big_PA`. It exists, but it belongs to existence-only naming with a
proof budget, not to Boolos naming.

**Proposition 3′ (upper bound for PA). [paper, assembled from cited
results]** There is a constant `c` with `G_PA(m) ≤ F_{ε₀}(c·m)` for all
`m`.

*Proof.* This is the embed, cut-eliminate, bound argument of Buchholz
and Wainer (1987), with the inputs measured by proof size. A PA proof of
`∃x φ(x)` with `|π| ≤ m` uses at most `m` induction axioms, each of
formula size at most `m`. It embeds into infinitary ω-arithmetic with
height below `ω·O(m)` and cut rank `O(m)` (their Embedding Lemma 2).
Eliminating cuts costs one exponential of height per rank (their
Theorem 4), leaving a cut-free derivation of height below `ω_{O(m)}`,
a tower of `ω`s of height `O(m)`. A cut-free derivation of height `β`
of a Σ₁ sentence has a witness below `F_β` of its numerical parameters
(their Bounding Lemma 5). With the standard fundamental sequence
`ε₀[n] = ω_n`, `F_{ω_{cm}}(cm) = F_{ε₀}(cm)`. Numerical parameters
in the proof are at most `2^m` (binary numerals), and
`F_β(2^{cm}) ≤ F_{β+1}(cm)` for `β ≥ 2`, so they only shift the
constant. ∎

The paper states the steps with the height and cut rank as parameters
of the proof, not as functions of `|π|`. That both are linear in `|π|`
is the standard reading, and it is the only step added here.
Freund ("Proof lengths for instances of the Paris–Harrington principle",
APAL 2017, arXiv:1601.08185) gives the same picture measured by the
Gödel number of the proof, and shows it is sharp. His Lemma 1.2 bounds
witnesses by a provably total function of the proof's code. His
Theorem 2.3 says that for large `n`, no `IΣ_n`-proof of "`F_{ε₀}(n)` is
defined" has code at most `F_{ε₀}(n−1)`.

So `G_PA` sits exactly at the ε₀ level. From below, it outgrows every
`F_α` with `α < ε₀` after a logarithmic rescaling (Proposition 3(b)).
From above, it is at most `F_{ε₀}` after a linear rescaling. We found
nobody who defines `G_T` itself under a name.

Part (d) is the important contrast with the report's Corollary 7. There,
changing the axioms only rescales the argument. Here, a stronger theory
gives a function that beats the weaker one by more than any rescaling
the stronger theory can prove total, so `G_ZFC` sits far above `G_PA`.
This is in line with Simmons (arXiv:1809.08676), whose `f_A{n}` is "the
largest number which is the output of an algorithm that can be proven
to halt via a proof in A of length at most n" (his Theorem 1.5, which
also shows a program of length `O(log n)` computes it), and whose
Corollary 1.6 says a stronger axiom system wins. `G_T` and `f_T` should
agree up to rescaling the argument. **[expected]** From the full text
(read for `LITERATURE-SURVEY.md` §8), Simmons does not relate `f_A` to
provably total functions or to ε₀, and his comparisons (Corollary 1.6 /
C.6, Corollary 2.5, Theorem 5.2) say when one system's strategy *beats*
another's, not by how much. His §5 argues that consistency strength is
the wrong ordering for these comparisons and uses ω-consistency instead.
That agrees with the hypothesis of Proposition 3(d), which needs `U` to
prove that `T` is Σ₁-sound (1-consistent), not merely consistent. His
Theorem 1.8 / C.11 is a different kind of statement: the `n`th case of
his Theorem 1.5 has a PA or ZFC proof of `O(n² log n)` characters, via
partial truth predicates.

**Proposition 4 (dropping Σ₁ breaks it). [paper]** Without the Σ₁
restriction, short existence proofs already reach every arithmetic
rung. For each `k`, there are `C` and Σ_{k+1} formulas `φ_m` of size
`C + 6 log₂ m` such that PA proves `∃!y φ_m(y)` in `C + O(log m)`
steps, and the defined number is the largest halting time of the
halting `k`-th-oracle programs with code at most `m`.

*Proof.* Let `φ_m(y)` say "`y` is the least number bounding the halting
time of every halting program with code `≤ m`" (with `k−1` nested
halting oracles; for `k = 1`, plain programs). For each `e ≤ m`, PA
proves classically that some `z` bounds `e`'s halting time if it halts.
Collection for the relevant formula class (provable in `IΣ_{k+1}`, so in
PA) gives one bound for all `e ≤ m`, and the least-number principle
gives a least one. Prove this for general `m` once, then instantiate at
`bin(m)`. ∎

So "the proof only shows the number exists, truth decides which number"
is a truth-naming scheme in disguise: the proof budget only certifies
well-definedness, and classical logic certifies it cheaply. The Σ₁
restriction is exactly what makes the value *computable from the proof*.

## 4. The complexity measure: between Kt and KNt

Use the binary target. Charge a name for both its formula and its proof,
the way Levin charges a program for both its length and its running
time:

    D_T(k) = min { |φ| + log₂|π| : π proves ∀x (φ(x) ↔ x = bin(k)) }.

Recall, for strings (numbers in binary) **[classical]**. Fix universal
deterministic and nondeterministic machines.

- `Kt(x)` (Levin): the minimum of `|d| + log₂ t` over programs `d` that
  print `x` and halt within `t` steps.
- `KNt(x)`: the same with a nondeterministic machine, every accepting
  computation printing `x`.

Allender and coauthors use a *bit-access* form instead: `d` answers
queries "is bit `i` of `x` equal to `b`?" within time `t`. Call these
`Kt'` and `KNt'`. They differ from the printing forms only by the time
needed to print every bit (Lemma A5):

    Kt'(x) ≤ Kt(x) + c,    Kt(x) ≤ Kt'(x) + log₂|x| + c,    Kt(x) ≥ log₂|x|,

and the same for `KNt`. The printing form is the right one here, since a
naming proof writes `bin(k)` in full, so `D_T(k) ≥ log₂ log₂ k` just as
`Kt(k) ≥ log₂ log₂ k`.

**Proposition 5. [paper, modulo Lemma A4]** Let `T ⊇ IΣ₁` have a
polynomial-time decidable set of axioms (PA, IΣ_k and ZFC do). There
are constants with

    KNt(k) ≤ c·D_T(k)·log₂ D_T(k) + c_T      and      D_T(k) ≤ c·Kt(k) + c.

*Proof.* Appendix A, §A.4. Left: a nondeterministic program holding `φ`
and `|π|` guesses a proof of that length, checks it in `poly(|π|)`
steps, and prints the `k` written on its last line. Right: if `d`
prints `k` in `t` steps, the formula "`x` is the output of program
`bin(d)`" has size `O(|d|)`, and a proof that it names `k` consists of
one general uniqueness lemma of `IΣ₁` and a verification of the `t`-step
run of length `poly(t + |d|)` (Lemma A4). ∎

Lemma A4, that a true instance of "this run is correct" has a proof of
polynomial length in a weak arithmetic with binary numerals, is a
standard tool of proof complexity, the same fact that makes
bounded-provability NP-hard. We cite it rather than re-prove it; it is
the one step of this section not written out here.

**Theorem (Allender and Spakowski, ECCC TR10-055). [classical]** For all
strings, `Kt(x) ≥ KNt(x)`, and the two are polynomially related if and
only if NEXP ⊆ EXP/poly.

**Corollary 6. [paper, modulo Lemma A4, + cited theorem]**

- If NEXP ⊆ EXP/poly then `D_T` and `Kt` are polynomially related.
- Contrapositive: exhibiting numbers whose proof-charged naming cost is
  super-polynomially below their `Kt` would prove NEXP ⊄ EXP/poly.

*Proof.* By Lemma A5 the theorem transfers to the printing forms: if
`Kt' ≤ poly(KNt')` then `Kt ≤ poly(KNt) + log₂|x| ≤ poly(KNt)`, using
`KNt ≥ log₂|x|`. Then `Kt ≤ poly(KNt) ≤ poly(D_T)` by Proposition 5,
and `D_T ≤ c·Kt + c` always. ∎

The unbudgeted measure (formula size only) is already in the literature as
a provability-based Kolmogorov complexity (Kikuchi, Kurahashi and Sakai
2012, per `LITERATURE-SURVEY.md`; full text not read). Charging
`log₂|π|` is the addition here.

We do not get the converse. `D_T` is not obviously as small as `KNt`:
to name `k` with a proof, the theory has to *prove* that no other number
fits, which is a universal statement over all computation paths, and
short proofs of such statements are exactly what may not exist (an
NP versus coNP flavoured question). So `D_T` is a "proof-certified"
middle ground. Since P = NP implies NEXP = EXP by padding, P = NP would
also make `D_T` and `Kt` polynomially related; nothing here goes in the
other direction.

This is the precise version of "bounding the proof is NP-type": the
proof is a nondeterministic certificate, and the gap between finding
it and checking it is the gap between `Kt` and `KNt`.

## 5. Bounded quantifiers and the polynomial hierarchy

**The classical match. [classical]** Bounded quantifiers correspond to
resource-bounded alternation, *for sets of inputs*:

- Δ₀ formulas (bounded quantifiers, `+`, `·`) define exactly the sets in
  the linear-time hierarchy (Bennett 1962, Wrathall 1978).
- With Buss's language (adding `|x|`, `⌊x/2⌋`, and the smash `x # y`),
  the `Σ^b_k` formulas define exactly the `Σ^p_k` sets, level by level
  of the polynomial hierarchy, and the functions `S^1_2` proves total
  via `Σ^b_1` formulas are exactly the polynomial-time functions
  (Buss 1986).

So the ladder "add one alternation" really does become the polynomial
hierarchy once quantifiers are bounded by the input length.

**Why it does not transfer to naming. [paper]** A naming formula has no
input. Its free variable *is* the answer, and bounding the other
quantifiers by `x` does not bound `x`. For example "`x` codes a complete
halting run of program `e`" is Δ₀ in `x`: every quantifier ranges over
pieces of `x`. Judged by truth in ℕ, it names the code of that run, so
Δ₀ truth-naming already reaches Busy Beaver values. It also stops there:
a program that searches for the least `x` satisfying a given Δ₀ formula
halts exactly on the formulas that define a number, so Δ₀ truth-naming
is rung 1 of `THE-LADDER.md`, the same rung as provable naming.

Bounding everything by explicit terms (no free unbounded variable) gives
the opposite failure: the answer is at most the largest value of a term
of size `n`, about `2^{2^{n/c}}` using chained squaring, at every level
of the hierarchy alike. In neither version does the level `k` of the
polynomial hierarchy change the growth of `Big`. Where alternation level
could matter is again the complexity measure: which numbers are cheap to
name with `Σ^b_k` formulas under a proof budget, a relativized form of
§4 with a `Σ^p_k` oracle. **[analogy; not worked out]**

## 6. "No top" and the hierarchy theorems

What is the same. **[classical]** The Berry argument behind Theorem 9 of
the report (no scheme names its own record plus one within budget) and
the diagonal proof of the time hierarchy theorem are one argument:
simulate everything at the lower level and do one better. In both cases
the diagonal object needs slightly more resources than the level it
beats: a slightly larger budget there, a `log` factor of time here.

What is different.

- In the unbounded world every rung is provably above the one below
  (Busy Beaver beats every computable function; the `k`-th oracle level
  beats level `k−1`). In the polynomial world the corresponding rungs
  are not known to differ at all: P versus NP, NP versus the second
  level, and so on.
- Diagonal arguments relativize: they work just as well when every
  machine has the same oracle. Baker, Gill and Solovay (1975) gave
  oracles relative to which P = NP and others relative to which
  P ≠ NP, so no relativizing argument can settle the question. The
  Berry and Tarski arguments in this project relativize. **[classical]**
  So nothing of the "no top" kind can prove P ≠ NP.
- Gödel's speed-up theorem (1936; Pudlák's Handbook chapter "The lengths
  of proofs" for the modern form) says adding `Con(T)` shortens some
  proofs by more than any computable factor. This is why theory strength
  matters with a proof budget (§3, Proposition 3(d)) and washes out
  without one (Report, Corollary 7). **[classical, applied]**

A related, finer point, for anyone continuing this: Pudlák showed
(1986) that statements `Con_T(m)` ("no contradiction has a proof of
length `≤ m`") have `T`-proofs of length polynomial in `m` and no shorter
than `m^ε`. Whether a theory has short proofs of "no short proof of `ψ`"
for other `ψ` is tied to the existence of optimal proof systems
(Krajíček and Pudlák 1989), which is in the NP versus coNP circle. A
Berry-style hierarchy for the capped functions of §2 would need exactly
such proofs. We did not pursue it, because Proposition 2 already shows
the capped functions are governed by the budget.

## 7. Summary table

| variant | proof must show | growth of the record | theory strength | status |
|---|---|---|---|---|
| Boolos, no budget | `∀x(φ ↔ x = k̄)` | Busy Beaver | rescaling only | [Lean] (Report) |
| Boolos, budget `t` | same, numeral written | between `t/C` and `t/2` (unary); `2^{t/C}` to `2^t` (binary) | marginal | [paper]; lower bound checked for instances |
| existence only, Σ₁, budget `m` | `∃!x φ` | dominates T's provably total functions; exactly the ε₀ level for PA | matters (Prop. 3d) | [paper]; upper bound from Buchholz–Wainer |
| existence only, any φ | `∃!x φ` | every arithmetic rung, with log-size proofs | — | [paper] |
| truth, Δ₀ φ | nothing | Busy Beaver (rung 1) | — | [paper] |

| complexity measure | relation | status |
|---|---|---|
| `D_T` (formula + log proof length) | `KNt ≲ D_T ≲ Kt` | [paper, modulo Lemma A4] |
| `Kt` vs `KNt` | polynomially related iff NEXP ⊆ EXP/poly | [classical] Allender–Spakowski |
| hence | `D_T` ≪ `Kt` somewhere ⇒ NEXP ⊄ EXP/poly | [paper, modulo Lemma A4] |

## 8. What might be new, and what to check

Probably folklore, stated here because we found it written nowhere in
this form:

1. Proposition 1 and 2: a proof budget on Boolos naming makes the
   budget the ceiling, and the ceiling is reached up to a constant.
   Trivial once said; it explains why "bound the proof, get
   P/EXP-indexed growth rates" does not work. The doubling lemmas of
   Proposition 2 are a standard speed-up device; we have not found this
   use of them stated.
2. Proposition 3 with Proposition 4: the ε₀ rung exists for
   existence-only Σ₁ naming with short proofs, and disappears without the
   Σ₁ restriction. Part (b) is the standard instantiation argument;
   Simmons has the closest prior statement.
3. The `KNt ≲ D_T ≲ Kt` placement and Corollary 6. The placement is a
   short argument; the content of Corollary 6 is Allender and
   Spakowski's theorem.
4. The non-NP-hardness of the capped threshold problem (Karp–Lipton
   applied to a function with one value per length).

To check before any public use:

- Proposition 3′ rests on Buchholz–Wainer read from a partly garbled
  scan, plus the standard reading that height and cut rank are linear in
  proof size. Fairtlough–Wainer (Handbook ch. III) or Schwichtenberg–Wainer,
  *Proofs and Computations* ch. 4, would give a cleaner citation; neither
  was reachable.
- Lemma A4 (polynomial-size proofs of correct runs) is the one step of
  Proposition 5 not written out. Citation found 2026-11-24: Pudlák,
  Handbook ch. VIII, Theorem 6.1.4 (see §A.3).
- Allender–Spakowski's exact statement was read from the abstract only.

Done 2026-11-24 (second pass): Propositions 2 and 5 now have full proofs
in Appendix A, with the explicit exponents `1/2` and `1/3` for
Proposition 2. Third pass, same day: Proposition 2 sharpened to `t/C`
and `2^{t/C}` with doubling lemmas (Appendix A.2a), and those proofs are
checked line by line by `proof-budgets/doubling_check.py`. Proposition 5 now uses Levin's printing form of `Kt`
(Lemma A5 explains why). The ε₀ upper bound is Proposition 3′.

## Appendix A. Proofs of Propositions 2 and 5

### A.0 Conventions

Proofs are Hilbert-style: a list of formulas, each an axiom (an instance
of a logical axiom scheme, an equality axiom, or an axiom of the theory)
or obtained by modus ponens or generalization. `|π|` is the sum of the
sizes of its formulas. `PA⁻` is axiomatized by finitely many universally
closed sentences: associativity and commutativity of `+` and `·`,
`x + 0 = x`, `x·1 = x`, `x·0 = 0`, distributivity, and the order axioms.

Unary numerals are `0̄ = 0`, `1̄ = 1`, `(m+1)‾ = m̄ + 1` (left-nested),
of size `2m − 1` for `m ≥ 1`. (The Lean development uses Foundation's
numeral. A different unary convention changes only constants below.)
Binary numerals `bin(m)` are as in `Binary.lean`: `bin(0) = 0`,
`bin(1) = 1`, `bin(2m) = (1+1)·bin(m)` and `bin(2m+1) = (1+1)·bin(m) + 1`
for `m ≥ 1`. For `m ≥ 1` with `L` binary digits, `|bin(m)| ≤ 6L`.

Three bookkeeping facts, all immediate from the axioms of equality.
Write `s ≡ t` for syntactic identity.

- **(F1) Instances.** If `∀x̄ ψ(x̄)` is an axiom of `PA⁻`, then
  `ψ(t̄)` has a proof of length `O(|ψ(t̄)|)`: one quantifier axiom
  instance per variable and modus ponens.
- **(F2) Chains.** Proofs of `s₁ = s₂` and `s₂ = s₃` give a proof of
  `s₁ = s₃` with `O(|s₁| + |s₂| + |s₃|)` extra symbols.
- **(F3) Congruence.** A proof of `s = s'` gives a proof of
  `C[s] = C[s']`, for a term context `C` of depth `h`, with
  `O(h·(|C[s]| + |C[s']|))` extra symbols. All contexts below have
  depth at most 3.

### A.1 Unary arithmetic

**Lemma A1.** `PA⁻ ⊢ ā + b̄ = (a+b)‾` with a proof of length
`O((a+b+1)²)`, and `PA⁻ ⊢ (1+1)·ā = (2a)‾` with a proof of length
`O((a+1)²)`.

*Proof.* Addition, by recursion on `b`. For `b = 0` this is an axiom.
For `b = 1` both sides are `ā + 1`. For `b → b+1`:
`ā + (b̄ + 1) = (ā + b̄) + 1` by associativity (F1), then
`(ā + b̄) + 1 = (a+b)‾ + 1` by congruence on the recursive proof (F3),
and `(a+b)‾ + 1 ≡ (a+b+1)‾`. Each step costs `O(a+b)` symbols, and
there are `b` steps.
Doubling: `(1+1)·ā = ā·1 + ā·1 = ā + ā` by commutativity, distributivity
and `x·1 = x` (a constant number of F1/F2/F3 steps of size `O(a)`), then
addition. ∎

**Lemma A2.** `PA⁻ ⊢ bin(m) = m̄` with a proof `P_m` of length
`O(m²)`.

*Proof.* For `m ≤ 1` both sides coincide. For `m = 2j + β` with
`j ≥ 1`: from `P_j`, congruence gives `(1+1)·bin(j) = (1+1)·j̄`
(`O(j)`), Lemma A1 gives `(1+1)·j̄ = (2j)‾` (`O(j²)`), and if `β = 1`
congruence adds `+ 1` on both sides, using `(2j)‾ + 1 ≡ (2j+1)‾`. So
`|P_m| ≤ |P_{⌊m/2⌋}| + C·m²`, and summing the geometric series,
`|P_m| ≤ 2C·m²`. ∎

Lemma A2 gives the first version's unary bound `√(t/C)`, from the
formula `x = bin(m)` for any `m`. Proposition 2 now uses Lemma A6
instead.

### A.2 Binary arithmetic

**Lemma A3.** For numbers below `2^L`, `PA⁻` proves

- `bin(a) + 1 = bin(a+1)` with a proof of length `O(L²)`;
- `bin(a) + bin(b) = bin(a+b)` and `bin(a) + bin(b) + 1 = bin(a+b+1)`
  with proofs of length `O(L²)`;
- `bin(a)·bin(b) = bin(ab)` with a proof of length `O(L³)`.

*Proof.* All by recursion on binary digits. Write `2·s` for `(1+1)·s`.

Increment: if `a` is even, `bin(a) + 1 ≡ bin(a+1)`. If `a = 2a' + 1`,
then `2·bin(a') + 1 + 1 = 2·(bin(a') + 1)` by a constant number of
semiring steps of size `O(L)`, and congruence on the recursive proof
for `a'` gives `2·bin(a'+1) ≡ bin(a+1)`. One level costs `O(L)`, and
there are `L` levels.

Addition, with and without carry, by simultaneous recursion: if
`a = 2a' + α` and `b = 2b' + β`, then
`bin(a) + bin(b) (+1) = 2·(bin(a') + bin(b')) + (α + β (+1))`, by a
constant number of semiring steps. The last summand is 0, 1, 2 or 3.
For 2 or 3 rewrite `2·s + 1 + 1` as `2·(s + 1)` (plus `+ 1` for 3) and
use the carry version at the level below. Congruence on the recursive
proof for `a', b'` finishes. Cases where `a` or `b` is below 2 reduce
to the increment lemma. Each level costs `O(L)`, and there are `L`.

Multiplication: if `b = 2b' + β`, then
`bin(a)·bin(b) = 2·(bin(a)·bin(b')) + β·bin(a)` by distributivity. Then
apply the recursive proof for `b'` (congruence), `2·bin(ab') ≡ bin(2ab')`
(or `2·0 = 0` if `ab' = 0`), and the addition lemma for numbers below
`2^{2L}`. One level costs `O(L²)`, and there are `L`. ∎

Lemma A3 gave the first version's binary bound `2^{(t/C)^{1/3}/2}`, by
squaring `2` `j` times with general multiplication. It is still what
Lemma A4 uses.

### A.2a Proposition 2 by doubling

For a term `s` write `S(s) = s + 1` and `D(s) = (1+1)·s`, and `Sⁿ`, `Dⁿ`
for `n`-fold application. Then `(m+1)‾ = Sᵐ(1)` for `m ≥ 0`, so
`(2n)‾ ≡ Sⁿ(n̄)`, and `bin(2^a) ≡ Dᵃ(1)`. For this subsection the proof
system is that of A.0 with the usual quantifier axiom
`∀v (A → B) → (A → ∀v B)` (`v` not free in `A`) added. It is used only
to eliminate an existential, written `∃v A` for `¬∀v¬A`.

**Lemma A6 (unary doubling).** For `n` a power of two, `PA⁻` proves

- `C_n`: `∀a ∀b (a = b → Sⁿ(a) = Sⁿ(b))`,
- `T_n`: `∀z ∀u (z + Sⁿ(u) = Sⁿ(z + u))`,
- `R_n`: `∀z (z + n̄ = Sⁿ(z))`,

and all of `C_n, T_n, R_n` for `n = 1, 2, 4, …, N` together have a proof
of length `O(N)`. Consequently `PA⁻ ⊢ bin(2^a) = (2^a)‾` with a proof of
length `O(2^a)`.

*Proof.* `n = 1`: `C_1` is an equality axiom, `T_1` is associativity of
`+`, and `R_1` is `z + 1 = z + 1`. From `n` to `2n`, using
`S²ⁿ(s) ≡ Sⁿ(Sⁿ(s))`:

- `C_2n`: instantiate `C_n` at `a, b` and at `Sⁿ(a), Sⁿ(b)`, chain the
  two implications, generalize.
- `T_2n`: `z + Sⁿ(Sⁿ(u)) = Sⁿ(z + Sⁿ(u))` is `T_n` at `u := Sⁿ(u)`.
  `C_n` applied to `T_n` at `u` gives `Sⁿ(z + Sⁿ(u)) = Sⁿ(Sⁿ(z + u))`.
  Chain and generalize.
- `R_2n`: `z + Sⁿ(n̄) = Sⁿ(z + n̄)` is `T_n` at `u := n̄`, and `C_n`
  applied to `R_n` gives `Sⁿ(z + n̄) = Sⁿ(Sⁿ(z))`. Chain and generalize.

Each step is a bounded number of lines (56 in the checked system), each
of size `O(n)`, so the sum over `n = 1, 2, …, N` is `O(N)`. Then
`bin(2^k) = (2^k)‾` by recursion on `k`: with `m = 2^{k−1}`,
`(1+1)·bin(m) = (1+1)·m̄` by congruence, `(1+1)·m̄ = m̄ + m̄` as in
Lemma A1, and `m̄ + m̄ = Sᵐ(m̄) ≡ (2m)‾` is `R_m` at `z := m̄`. Step `k`
costs `O(2^k)`, so the total is `O(2^a)`. ∎

**Lemma A7 (binary doubling).** For `n` a power of two, `PA⁻` proves

- `B_n`: `∀a ∀b (a = b → Dⁿ(a) = Dⁿ(b))`,
- `A_n`: `∀w ∀z (Dⁿ(w)·z = Dⁿ(w·z))`,

all of them up to `n = N` with a proof of length `O(N)`. With
`w_i := bin(2^{2^i}) ≡ D^{2^i}(1)`, `PA⁻ ⊢ w_i·w_i = w_{i+1}` with a
proof of length `O(2^i)`, given `A_{2^i}` and `B_{2^i}`.

*Proof.* `B_1` is an equality axiom and `A_1` is associativity of `·`.
From `n` to `2n` exactly as for `C` and `T`: `A_2n` chains `A_n` at
`w := Dⁿ(w)` with `B_n` applied to `A_n`. (38 lines per step in the
checked system.) For the squaring, with `M = 2^i`: `A_M` at `w := 1`,
`z := w_i` gives `D^M(1)·w_i = D^M(1·w_i)`, and `1·w_i = w_i` by
commutativity and `x·1 = x`, so `B_M` gives `D^M(1·w_i) = D^M(w_i)
≡ w_{i+1}`. ∎

**Proof of Proposition 2.** *Unary.* By Lemma A6 and equality logic,
`∀x (x = bin(2^a) ↔ x = (2^a)‾)` has a proof of length at most
`C₀·2^a`. Given `t = t(n) ≥ 2C₀`, take `a = ⌊log₂(t/C₀)⌋`. Then
`2^a > t/(2C₀)`, and the formula `x = bin(2^a)` has size
`4a + 3 ≤ 4·log₂ t + 3 ≤ n`.

*Binary.* Let `χ_0(u) :≡ u = 1+1` and
`χ_i(u) :≡ ∃y (u = y·y ∧ χ_{i−1}(y))`, with a fresh bound variable at
each level. In ℕ, `χ_j` holds exactly of `2^{2^j}`, and `|χ_j(x)| =
10j + 5`. A proof of `∀x (χ_j(x) ↔ x = w_j)`:

- *Existence*, `χ_i(w_i)` for `i < j`: `χ_0(w_0)` is `(1+1)·1 = 1+1`, an
  axiom instance. From `χ_{i−1}(w_{i−1})` and `w_i = w_{i−1}·w_{i−1}`
  (Lemma A7) form the conjunction and introduce `∃y`. Lines of size
  `O(2^i + i)`, a bounded number of them.
- *Uniqueness*, `∀u (χ_i(u) → u = w_i)` for `i ≤ j`: for `i = 0` by
  `x·1 = x`. For the step, under the hypothesis `u = y·y ∧ χ_{i−1}(y)`
  (kept as an antecedent, so no deduction theorem is needed), the
  previous lemma gives `y = w_{i−1}`, congruence gives
  `y·y = w_{i−1}·w_{i−1}`, and Lemma A7 gives `= w_i`. Generalize over
  `y` and eliminate the existential (this is where the extra quantifier
  axiom is used). Again a bounded number of lines of size `O(2^i + i)`.
- *The naming sentence*: `→` is uniqueness at `i = j`. `←`: under
  `x = w_j`, the witness `w_{j−1}` gives `x = w_{j−1}·w_{j−1} ∧
  χ_{j−1}(w_{j−1})`, then `∃`-introduction. The hypothesis `x = w_j`, of
  size `O(2^j)`, occurs in a bounded number of lines only, because `x`
  is the outermost variable of `χ_j`.

The total is at most `C₀·2^j` for a constant `C₀`. Given `t ≥ 2C₀`, take
`j = ⌊log₂(t/C₀)⌋`, so `2^j > t/(2C₀)` and the number named is
`2^{2^j} > 2^{t/(2C₀)}`. The formula has size `10j + 5 ≤ 10·log₂ t + 5
≤ n`. Take `C = 2C₀`. ∎

**The check. [checked for instances]** `proof-budgets/doubling_check.py`
builds these proofs, as lists of formulas with no justifications, in the
Hilbert system `H` of `naming-depth/collision_check.py`, plus the
quantifier axiom above and associativity of `·`. It reuses that file's
checker, which accepts a line only if it is an axiom instance or follows
by modus ponens or generalization. Every proof for `a = 1, …, 20` and
`j = 1, …, 16` passes. 80 random one-line corruptions are all rejected.
Measured lengths (full table in `proof-budgets/doubling_check_out.md`):

| | `a` or `j` | number named | size of `φ` | proof length | length ÷ (`2^a` or `2^j`) |
|---|---|---|---|---|---|
| unary | 10 | 1,024 | 43 | 691,427 | 675 |
| unary | 20 | 1,048,576 | 83 | 694,189,901 | 662 |
| binary | 10 | `2^{1024}` | 105 | 11,707,592 | 11,433 |
| binary | 16 | `2^{65536}` | 165 | 714,245,924 | 10,899 |

The ratio settles, as the fixed shape of the doubling steps predicts.
Over these instances `C₀ ≤ 1,029` (unary) and `C₀ ≤ 19,450` (binary).
The constants are large because the propositional steps are written out
in a three-axiom Hilbert system; nothing was done to shrink them.

### A.3 Verifying a run

Fix a universal machine `U`, single tape, programs given by their code
number `d` with `|d| = ⌊log₂ d⌋ + 1` bits. Let `Run(e, c, y)` be a Δ₀
formula saying "`c` codes a halting computation of `U` on program `e`
with output `y`", arranged in the usual way: configurations are rows of
a tableau, and all bounded quantifiers range over row and column
indices, not over the values of the codes.

**Lemma A4. [classical, cited]** There is a polynomial `q` such that,
whenever `U` on program `d` halts in `t` steps with output `k`, and `c`
is the code of that run, `PA⁻ ⊢ Run(bin(d), bin(c), bin(k))` with a
proof of length at most `q(t + |d|)`.

This is the standard fact that true instances of a polynomial-time
relation have polynomial-size proofs in a weak arithmetic with binary
numerals. It is the reason the problem "does `ψ` have a proof of length
`≤ m`?" is NP-hard. It is used in this form in Pudlák's work on
finitistic consistency statements (Logic Colloquium '84, 1986, and
Handbook of Proof Theory ch. VIII). *Outline:* each of the `poly(t)`
bounded universal quantifiers ranges over indices `≤ bin(t²)`, and
`PA⁻ ⊢ ∀i ≤ bin(N) (i = bin(0) ∨ … ∨ i = bin(N))` in `O(N²·log N)`
symbols by discreteness. Each resulting instance is an equation between
binary numerals, settled by Lemma A3. **[cited, checked 2026-11-24:**
Pudlák, "The lengths of proofs", Handbook of Proof Theory ch. VIII,
Theorem 6.1.4: a relation is in NP exactly when some formula numerates
it in Robinson arithmetic `Q` with proofs of length polynomial in the
binary lengths of the arguments. Lemma 6.1.5 and Corollary 6.1.6 there
are the forms for bounded formulas and for "`φ` has a proof of length at
most `n`". The proof of 6.1.4 is a sketch along the lines of the outline
above, and the theorem is stated for *some* numerating formula, not for
a given `Run`.**]**

**Lemma (uniqueness of output). [classical]**
`IΣ₁ ⊢ ∀e ∀c ∀c' ∀y ∀y' (Run(e,c,y) ∧ Run(e,c',y') → y = y')`, by
induction on the step number: two runs agree on each configuration.
This is one fixed proof, of length `c_T`.

### A.4 Proof of Proposition 5

*Right inequality.* Suppose `d` prints `k` in `t` steps, so
`Kt(k) ≤ |d| + log₂ t`. Let `φ(x) :≡ ∃z Run(bin(d), z, x)`, of size
`≤ 6|d| + c`. In `T ⊇ IΣ₁`:

- `φ(bin(k))`: Lemma A4 and ∃-introduction, length `q(t + |d|) + O(|d| + log k)`.
- `φ(x) → x = bin(k)`: the uniqueness lemma instantiated at
  `bin(d), z, bin(c), x, bin(k)`, together with the line above, length
  `c_T + O(|Run|·(|d| + log c))`.

Here `log k ≤ log c ≤ O(t²)`. So `|π| ≤ q'(t + |d|)`, and

    D_T(k) ≤ 6|d| + c + log₂ q'(t + |d|) ≤ c·(|d| + log₂ t) + c.

*Left inequality.* Let `φ` and `π` attain `D_T(k)`, with `ℓ = |π|`. A
nondeterministic program is given `φ` (written in
`O(|φ|·log |φ|)` bits: a tree with `|φ|` nodes, each labelled by a
symbol or a variable index below `|φ|`) and `ℓ` (`O(log ℓ)` bits),
together with a fixed program of `c_T` bits. It guesses a string of
length `≤ ℓ`, checks in `poly(ℓ)` steps that it is a `T`-proof (the
axioms are polynomial-time decidable) whose last line has the form
`∀x (φ(x) ↔ x = bin(k'))`, and if so prints `k'`. Every accepting
computation prints `k`, by the uniqueness of named values (Report,
Theorem 1). So

    KNt(k) ≤ c·(|φ| log |φ| + log ℓ) + c_T + log₂ poly(ℓ)
           ≤ c·D_T(k)·log₂ D_T(k) + c_T. ∎

### A.5 Printing versus bit access

**Lemma A5. [paper]** `Kt'(x) ≤ Kt(x) + c`,
`Kt(x) ≤ Kt'(x) + log₂|x| + c`, `Kt(x) ≥ log₂|x|`, and likewise for
`KNt`, `KNt'`.

*Proof.* A printing program answers a bit query by printing everything,
in the same time. A bit-access program prints `x` by querying
`i = 1, 2, …` until it is told the position is past the end, in time
`O(|x|·t)`. In the nondeterministic case, guess each bit and run an
accepting computation confirming it, so wrong guesses reject. Printing
`x` takes at least `|x|` steps. ∎

## References

- G. Boolos, "A new proof of the Gödel incompleteness theorem", *Notices
  AMS* 36 (1989).
- D. Simmons, "Naming the largest number", arXiv:1809.08676v2. [read in full; see `LITERATURE-SURVEY.md` §8]
- G. Lacerda, "Upper-bounding proof length with the Busy Beaver",
  arXiv:1406.1808. [read, see `LITERATURE-SURVEY.md`]
- L. Levin, "Universal sequential search problems", *Problems of
  Information Transmission* 9 (1973). [memory]
- E. Allender, M. Koucký, D. Ronneburger, S. Roy, "The pervasive reach
  of resource-bounded Kolmogorov complexity in computational complexity
  theory", *JCSS* 77 (2011). [Definitions 3 and 8 read]
- E. Allender, H. Spakowski, "Avoiding simplicity is complex", ECCC
  TR10-055. [abstract read]
- M. Kikuchi, T. Kurahashi, H. Sakai, "On proofs of the incompleteness
  theorems based on Berry's paradox by Vopěnka, Chaitin, and Boolos",
  *MLQ* 58 (2012). [not read; see `LITERATURE-SURVEY.md`]
- S. Buss, *Bounded Arithmetic*, Bibliopolis 1986. [memory]
- C. Wrathall, "Rudimentary predicates and relative computation", *SIAM
  J. Comput.* 7 (1978). [memory]
- P. Pudlák, "On the length of proofs of finitistic consistency
  statements in first order theories", Logic Colloquium '84 (1986); and
  "The lengths of proofs", in *Handbook of Proof Theory* (1998). [memory]
- J. Krajíček, P. Pudlák, "Propositional proof systems, the consistency
  of first order theories and the complexity of computations", *JSL* 54
  (1989). [memory]
- T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP
  question", *SIAM J. Comput.* 4 (1975). [memory]
- R. M. Karp, R. J. Lipton, "Some connections between nonuniform and
  uniform complexity classes", STOC 1980. [memory]
- K. Gödel, letter to J. von Neumann, 20 March 1956. [memory]
- W. Buchholz, S. Wainer, "Provably computable functions and the fast
  growing hierarchy", *Contemporary Math.* 65 (1987), 179–198. [read,
  partly garbled scan]
- A. Freund, "Proof lengths for instances of the Paris–Harrington
  principle", *APAL* 168 (2017), arXiv:1601.08185. [read]
- M. Fairtlough, S. Wainer, "Hierarchies of provably recursive
  functions", in *Handbook of Proof Theory* (1998). [memory]
