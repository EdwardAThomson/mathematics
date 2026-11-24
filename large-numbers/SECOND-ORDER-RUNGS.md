# The rungs above arithmetic truth: naming in second-order arithmetic

Written 2026-11-24. It continues `MIDDLE-RUNGS.md` (the finite rungs) and
`GENERAL-NAMING-THEOREM.md` (provable naming in any theory, and true
arithmetic as a limit, its Theorem 8). The question here: what happens when
the naming formula may also talk about **sets** of whole numbers, and how does
that compare with Busy Beaver functions that consult infinite oracles such as
the hyperarithmetic sets or Kleene's `O`?

Tags as in the rest of the project: **[Lean]** machine-checked, **[paper]**
proved here on paper and not independently checked, **[classical]** a known
result we cite, **[expected]** believed but not proved here. Nothing in this
note is machine-checked.

## 0. In plain language

Allow the naming formula to say "for every set of numbers" or "there is a set
of numbers". Logicians sort such formulas by how the set quantifiers start:
`Π¹₁` formulas begin with one block of "for every set", `Σ¹₁` with one block of
"there is a set", `Σ¹₂` with "there is a set such that for every set", and so
on. Ordinary arithmetic formulas, which the earlier notes used, have no set
quantifiers at all.

1. **One block of set quantifiers already beats all of arithmetic truth.**
   Naming by true `Π¹₁` formulas outgrows naming by true arithmetic formulas,
   by more than any computable rescaling (Theorem 4(b)). This is the rung
   directly above the "rung ω" of `THE-LADDER.md`.

2. **"There is a set" and "for every set" give the same rung.** Naming by
   `Σ¹₁` and by `Π¹₁` formulas differ by a constant number of symbols
   (Proposition 2). In arithmetic, by contrast, a "for all numbers" block
   costs a whole oracle level (`MIDDLE-RUNGS.md`). The difference: once a
   formula has a set quantifier, extra quantifiers over *numbers* are free.

3. **The matching Busy Beaver is over the sets that both kinds of formula can
   describe.** A set is `Δ¹₁` if a `Π¹₁` formula describes it and another
   `Π¹₁` formula describes its complement. By a classical theorem of Kleene
   these are exactly the *hyperarithmetic* sets: what you get by iterating the
   halting problem along any computable well-ordering. Naming by `Π¹₁` truth
   is the Busy Beaver function for machines that may consult any such set,
   with the description of the set counted in the size (Theorem 3). It
   therefore beats Busy Beaver with every single hyperarithmetic oracle, and
   is a limit of all of them, the way arithmetic truth was a limit of the
   finite jumps.

4. **Busy Beaver with oracle Kleene's `O` is one jump too high.** `O` (the
   set of notations for computable ordinals) is the natural "top" of the
   hyperarithmetic sets, but it is not hyperarithmetic itself. Busy Beaver
   with oracle `O` beats `Π¹₁` naming, and is itself beaten by `Σ¹₂` naming
   (Theorem 4(d), (e)). This is the same one-jump overshoot found in
   `GENERAL-NAMING-THEOREM.md` §7.

5. **The pattern continues and never stops.** For every `k`, `Σ¹_k` and `Π¹_k`
   naming share a rung, it is the Busy Beaver over `Δ¹_k` oracles, and the
   rung for `k + 1` strictly beats the rung for `k` (Theorem 4(f)). The Busy
   Beaver for infinite-time Turing machines, which `THE-LADDER.md` placed
   only roughly, sits strictly between the `Π¹₁` and `Σ¹₂` rungs
   (Proposition 6).

6. **All of this comes from one short argument.** Theorem 1 is a general
   statement about any class of formulas that can say "there is a number":
   naming by that class equals Busy Beaver over oracles the class can describe
   both ways. It is nearly a tautology. The content is in identifying those
   oracles in each case and in the comparisons, which use classical facts
   from higher recursion theory.

What you must accept for these numbers to be definite also rises slowly here:
`Π¹₁` and `Σ¹₂` truth do not depend on which universe of sets you work in, but
`Σ¹₃` truth can (§7).

## 1. Setting

**Language.** `ℒ₂` is the language of second-order arithmetic: number
variables, set variables `X, Y, …`, the symbols `0, 1, +, ·, <`, and atoms
`t ∈ X`. Size `|φ|` is node count, as in `MIDDLE-RUNGS.md` §1; numerals are the
short binary terms `bin(n)` with `|bin(n)| ≤ 6·log₂(n+2)`. Formulas are in
negation normal form (negation only on atoms, the duals `∧/∨`, `∀/∃`
exchanged), so `|¬φ| = |φ|` for the dual `¬φ`. (Under a convention with `¬`
as a node, `|¬φ| ≤ |φ| + 1`; only constants change.)

**Semantics.** Truth is in the standard model `(ℕ, 𝒫(ℕ))`: number variables
range over `ℕ` and set variables over *all* subsets of `ℕ`. The metatheory is
ZFC.

**Liberal classes.** `Σ¹₀ = Π¹₀` is the class of arithmetic formulas (any
number quantifiers, no set quantifiers). `Σ¹_{k+1}` is the smallest class
containing `Π¹_k` and closed under `∧`, `∨`, number quantifiers `∃y`, `∀y`
(bounded or not) and set quantifiers `∃X`; `Π¹_{k+1}` is the dual, with `∀X`.
So `Σ¹_k ∪ Π¹_k ⊆ Σ¹_{k+1} ∩ Π¹_{k+1}` at no cost in size, and the dual of a
`Σ¹_k` formula is `Π¹_k`. Every liberal `Σ¹_k` formula is equivalent in the
standard model to a prenex one `∃X₁ ∀X₂ … (arithmetic)`, using countable
choice to pull number quantifiers inside set quantifiers **[classical: the
normal form theorem; Rogers §16, Sacks *Higher Recursion Theory* I.1]**. All
results below are for the liberal classes; the remark at the end of §3 says
why the prenex classes give the same rungs.

**Truth naming.** For a class `Γ`, a formula `φ(x) ∈ Γ` with one free number
variable *names* `m` if `m` is the only number it is true of, and

```
N_Γ(n) := max { m : some φ ∈ Γ with |φ| ≤ n names m }       (0 if none).
```

`N_TA` denotes naming by arithmetic formulas, the "rung ω" function of
`GENERAL-NAMING-THEOREM.md` Theorem 8. Since arithmetic formulas are in every
class `Σ¹_k, Π¹_k`, `N_TA(n) ≤ N_{Π¹₁}(n)` trivially.

**Machines.** `U` is the universal oracle machine of `MIDDLE-RUNGS.md` §1;
`U^Y(p)↓t` means `U` on program `p` with oracle `Y` halts after exactly `t`
steps; `BB^Y(ℓ) := max { t : |p| ≤ ℓ, U^Y(p)↓t }`. We use (F2) of
`MIDDLE-RUNGS.md` §2: a `Δ₀` formula `H(e, t, σ, c)` saying that `c` is the
trace of `U` on `e` with the `i`-th query answered by the `i`-th answer listed
in the record `σ`, that the queries are those listed in `σ`, and that the run
halts after exactly `t` steps; if every answer in `σ` is correct for `Y`, then
`σ`, `c`, `t` are the actual record, trace and running time of `U^Y(e)`.
Codes are injective, and the Cantor pairing `⟨t, σ, c⟩` is at least `t`.

We use the classical fact that `BB^Y` eventually dominates every
`Y`-computable function, in the Berry form: if `f` is computable from `Y`,
there is `c_f` with `BB^Y(log₂(n+2) + c_f) > f(n)` for all `n` (the program
with `n` hard-wired computes `f(n)` and idles that long). **[classical]**

## 2. The abstract theorem

Fix a class `Γ` of `ℒ₂` formulas. Say `Γ` is **admissible for naming** if

- (i) it contains the `Δ₀` formulas,
- (ii) it is closed under `∧`, `∨` and bounded number quantifiers,
- (iii) it is closed under unbounded `∃y` over numbers, and under renaming
  of free number variables.

Every `Σ_k` (`k ≥ 1`) of arithmetic, and every `Σ¹_k`, `Π¹_k` (`k ≥ 1`), is
admissible. `Π_k` of arithmetic is not, because of (iii).

**`Γ`-bidefinable sets.** A pair `(θ⁺, θ⁻)` of `Γ` formulas with one free
number variable *describes* `Y ⊆ ℕ` if `θ⁺` defines `Y` and `θ⁻` defines
`ℕ ∖ Y`. Let

```
BB_Γ(ℓ) := max { t : |θ⁺| + |θ⁻| + |p| ≤ ℓ, (θ⁺, θ⁻) describes some Y, U^Y(p)↓t }.
```

This is finite: there are finitely many triples, and each pair describes at
most one `Y`. It is the analogue of `BB^{[T]}` in `GENERAL-NAMING-THEOREM.md`
§1, with "`T` decides" replaced by "true in the standard model".

**Theorem 1.** There are absolute constants `C, c` such that for every
admissible `Γ` and all `ℓ, n`:

```
BB_Γ(ℓ)  ≤  N_Γ(6ℓ + C),          N_Γ(n)  ≤  BB_Γ(2n + c).
```

So `N_Γ` and `BB_Γ` are one growth class, up to a *linear* rescaling.

*Proof of the first inequality.* Let `(θ⁺, θ⁻)` describe `Y` and
`U^Y(e)↓t`. Write `qᵢ`, `aᵢ` for the `i`-th query and answer listed in `σ`
(`Δ₀` functions of `σ, i`). Put

```
χ(z, x) :≡ ∃t, σ, c ≤ x [ x = ⟨t, σ, c⟩ ∧ H(z, t, σ, c)
              ∧ ∀i < len(σ) ∃q ≤ σ ( q = qᵢ ∧ (aᵢ = 0 ∨ θ⁺(q)) ∧ (aᵢ = 1 ∨ θ⁻(q)) ) ]
φ(x)    :≡ ∃z ( z = bin(e) ∧ χ(z, x) ).
```

By (i)–(iii), `φ ∈ Γ`. If `φ(x)` holds, every listed answer is correct for
`Y` (a "yes" makes `θ⁺(qᵢ)` true, so `qᵢ ∈ Y`; a "no" makes `θ⁻(qᵢ)` true, so
`qᵢ ∉ Y`), so by (F2) `σ`, `c`, `t` are the actual record, trace and time, and
by injectivity `x = ⟨t, σ, c⟩`. Conversely the actual triple satisfies `φ`.
So `φ` names `⟨t, σ, c⟩ ≥ t`, and
`|φ| ≤ |θ⁺| + |θ⁻| + 6·log₂(e+2) + C₀`. A program of `|p|` bits has code
`e < 2^{|p|+1}`, so `6·log₂(e+2) ≤ 6|p| + 12`. ∎

*Proof of the second inequality.* Let `φ ∈ Γ`, `|φ| ≤ n`, name `m`. Put
`θ⁺ := φ` and `θ⁻(x) :≡ ∃y (y ≠ x ∧ φ(y))`. Then `θ⁻ ∈ Γ` by (iii), and it is
true exactly of the `x ≠ m`. So `(θ⁺, θ⁻)` describes `{m}`, with
`|θ⁺| + |θ⁻| ≤ 2n + 4`. The fixed program `p₀`, "for `i = 0, 1, 2, …` ask
whether `i` is in the oracle; halt at the first yes", runs at least `m`
steps with oracle `{m}`. ∎ **[paper]**

Theorem 1 says nothing yet about how fast `N_Γ` grows; that depends on which
sets are `Γ`-bidefinable, which is where the classical theory enters.

*Remark (consistency with the finite rungs).* For `Γ = Σ_{k+1}` of
arithmetic the describable sets are those computable from `0^(k)` (Post's
theorem), and `BB_{Σ_{k+1}}` is in the growth class of `BB^{(k)}` up to an
`n log n` rescaling (a `0^(k)`-machine answers a query to `Y` by searching for
a witness to `θ⁺(q)` or to `θ⁻(q)`, checking the `Π_k` remainder with its
oracle). So Theorem 1 recovers the `Σ_{k+1}` half of `MIDDLE-RUNGS.md`
Theorem 3. **[paper]**

## 3. Second-order rungs

**Proposition 2 (`Σ¹_k` and `Π¹_k` naming coincide).** For every `k ≥ 1` there
is a constant `c` with

```
N_{Π¹_k}(n) ≤ N_{Σ¹_k}(n + c),          N_{Σ¹_k}(n) ≤ N_{Π¹_k}(n + c).
```

*Proof.* If `φ ∈ Σ¹_k` names `m`, then `ψ(x) :≡ ∀y (y = x ∨ ¬φ(y))` names
`m` too, and `ψ ∈ Π¹_k` because `¬φ` is `Π¹_k` and `Π¹_k` is closed under
number quantifiers. The other direction is the same with the classes
exchanged. ∎ **[paper]**

In arithmetic the same `ψ` would add a "for all" block and so climb a rung;
in second-order arithmetic number quantifiers are absorbed. This is why the
second-order rungs are indexed by `k` alone, with no `Σ`/`Π` shift.

**Which oracles.** For `Γ = Σ¹_k` or `Π¹_k`, a pair describes `Y` exactly when
`Y` is `Δ¹_k` (both `Y` and its complement are `Σ¹_k`, equivalently both are
`Π¹_k`). For `k = 1`:

- **(K1) Suslin–Kleene.** The `Δ¹₁` sets of numbers are exactly the
  hyperarithmetic sets: those computable from some `H_b`, `b ∈ O`, where `O`
  is Kleene's set of notations for computable ordinals and `H_b` is the
  halting problem iterated along `b`. **[classical: Kleene 1955; Sacks,
  *Higher Recursion Theory*, II.1]**
- **(K2)** `O` is `Π¹₁`-complete: every `Π¹₁` set many-one reduces to it,
  uniformly in the formula. So `O` is not `Δ¹₁` (not hyperarithmetic), and
  `O` decides the truth of every `Π¹₁` and every `Σ¹₁` sentence. **[classical:
  Kleene; Rogers §16.4]**
- **(K3)** For `b ∈ O` there is exactly one set `X` with `Hset(X, b)` ("`X` is
  the `H`-set along `b`"), an arithmetic condition, and it is `H_b`. Hence
  `H_b` is described by the pair
  `θ⁺_b(i) :≡ ∀X (Hset(X, b̄) → i ∈ X)`, `θ⁻_b(i) :≡ ∀X (Hset(X, b̄) → i ∉ X)`,
  both `Π¹₁`, of size `C + 6·log₂(b+2)`. **[classical: Spector 1955; Sacks
  II.2]**
- **(K4)** True arithmetic `TA` is `Δ¹₁`, described by
  `∀S (Sat(S) → i ∈ S)` and `∀S (Sat(S) → i ∉ S)`, where `Sat(S)` (arithmetic)
  says `S` is a set of sentence codes obeying Tarski's clauses; exactly one
  such `S` exists, namely `TA`. **[classical]**
- **(K5)** For each `k` there is a universal `Σ¹_k` formula; the set `V_k` of
  true `Σ¹_k` sentences is `Σ¹_k`, its complement (true `Π¹_k` sentences and
  non-codes) is `Π¹_k`, so `V_k ∈ Δ¹_{k+1}` with fixed describing formulas.
  `V_k` decides every `Σ¹_k` and `Π¹_k` sentence. **[classical]**

**Theorem 3 (the `Π¹₁` rung).** With absolute constants,

```
BB_{Π¹₁}(ℓ) ≤ N_{Π¹₁}(6ℓ + C) ≤ N_{Σ¹₁}(6ℓ + C'),     N_{Σ¹₁}(n) ≤ N_{Π¹₁}(n + c) ≤ BB_{Π¹₁}(2n + c').
```

So `Σ¹₁` naming, `Π¹₁` naming and Busy Beaver over hyperarithmetic oracles
(each oracle paid for by a `Π¹₁` description of it and of its complement) are
one growth class, up to linear rescaling. In particular, for every `b ∈ O`,

```
BB^{H_b}(ℓ)  ≤  N_{Π¹₁}( 6ℓ + 6·log₂(b+2) + C ).
```

The same holds at every level: `N_{Σ¹_k} ≈ N_{Π¹_k} ≈ BB_{Π¹_k}`, Busy Beaver
over `Δ¹_k` oracles.

*Proof.* Theorem 1 and Proposition 2; the display is Theorem 1 applied to the
pair of (K3). ∎ **[paper, using (K1), (K3) classical]**

So the `Π¹₁` rung is the diagonal over the hyperarithmetic hierarchy: it beats
the Busy Beaver of each level `H_b`, and by (K1) every oracle it uses lives at
some level. This is the transfinite analogue of `GENERAL-NAMING-THEOREM.md`
Theorem 8, where arithmetic truth is the diagonal over the finite levels
`0^(k)`.

*Remark (prenex classes).* If `N` is computed over prenex formulas only, the
upper bounds still hold (prenex formulas are liberal). The lower bound of
Theorem 1 inserts the describing formulas `θ±` into a fixed frame; pulling the
frame's number quantifiers inside the set quantifiers of `θ±` replaces each
atom `t ∈ X` by `⟨y, t⟩ ∈ X`, a linear increase in size. So the prenex rungs
are the same, up to a linear rescaling. **[paper]**

## 4. Comparisons

**Theorem 4.** Let `h` be any computable function. With constants depending
only on `h`:

- (a) `N_TA(n) ≤ N_{Π¹₁}(n)`.
- (b) **`Π¹₁` naming strictly beats arithmetic truth:**
  `N_{Π¹₁}(6·log₂(n+2) + C_h) > N_TA(h(n))` for all `n`.
- (c) **It beats every hyperarithmetic Busy Beaver:** for each `b ∈ O`,
  `N_{Π¹₁}(6·log₂(n+2) + C_{h,b}) > BB^{H_b}(h(n))`.
- (d) **Busy Beaver with oracle `O` beats `Π¹₁` naming:**
  `BB^O(log₂(n+2) + c_h) > N_{Π¹₁}(h(n))`.
- (e) **`Σ¹₂` naming beats Busy Beaver with oracle `O`:**
  `BB^O(ℓ) ≤ N_{Σ¹₂}(6ℓ + C)`, hence with (d),
  `N_{Σ¹₂}(6·log₂(n+2) + C_h) > N_{Π¹₁}(h(n))`.
- (f) **The rungs are distinct at every level:**
  `N_{Σ¹_{k+1}}(6·log₂(n+2) + C_{h,k}) > N_{Σ¹_k}(h(n))` for every `k ≥ 0`
  (with `Σ¹₀` naming meaning `N_TA`).

*Proof.* (a) Arithmetic formulas are `Π¹₁`.

(f) first, since (b) and the second half of (e) are cases of it. `N_{Σ¹_k}` is
computable from `V_k` of (K5): "`φ` names something" is
`∃x φ(x) ∧ ∀x ∀y (¬φ(x) ∨ ¬φ(y) ∨ x = y)`, a `Σ¹_k` sentence and a `Π¹_k`
sentence (number quantifiers absorbed), both decided by `V_k`; given a yes,
ask `φ(0̄), φ(1̄), …` until one is true. So the program "compute
`B := N_{Σ¹_k}(h(n))` with oracle `V_k`, idle `B + 1` steps, halt", with `n`
hard-wired, has `log₂(n+2) + c_{h,k}` bits and runs more than
`N_{Σ¹_k}(h(n))` steps. `V_k` is `Δ¹_{k+1}` with fixed describing formulas,
so this run time is at most `BB_{Σ¹_{k+1}}(log₂(n+2) + c'_{h,k})`, and
Theorem 1 converts that into `N_{Σ¹_{k+1}}(6·log₂(n+2) + C_{h,k})`. For
`k = 0`, `V_0 = TA` and `N_{Σ¹₀} = N_TA` is computable from `TA` in the same
way (`GENERAL-NAMING-THEOREM.md` Theorem 8(b)); `TA` is `Δ¹₁` by (K4), which
gives (b) with `Π¹₁` in place of `Σ¹₁` (Proposition 2).

(c) `BB^{H_b}(h(n))` is computable from `H_{b+1}` (decide which short
programs halt, run those), and `H_{b+1}` is `Δ¹₁` with describing formulas of
size `C + 6·log₂(b+3)` by (K3). Argue as in (f).

(d) By (K2), `O` decides every `Π¹₁` and `Σ¹₁` sentence, so the argument of
(f) shows `N_{Π¹₁}` is computable from `O`; apply the Berry form of
domination (§1).

(e) `O` is `Π¹₁ ⊆ Σ¹₂` and its complement is `Σ¹₁ ⊆ Σ¹₂`, with fixed
formulas, so `BB^O(ℓ) ≤ BB_{Σ¹₂}(ℓ + C) ≤ N_{Σ¹₂}(6ℓ + C')` by Theorem 1.
Combine with (d), taking the `h` of (d) to absorb the constants. ∎ **[paper]**

The picture so far, each step strict:

```
N_TA  <  N_{Π¹₁} ≈ N_{Σ¹₁} ≈ BB over Δ¹₁ (hyperarithmetic) oracles
      <  BB^O
      <  N_{Π¹₂} ≈ N_{Σ¹₂} ≈ BB over Δ¹₂ oracles
      <  N_{Π¹₃} ≈ N_{Σ¹₃}  <  …
```

**Why `BB^O` overshoots, in one line.** The oracles that `Π¹₁` formulas can
*describe* are the hyperarithmetic sets; `O` is the set that *decides* `Π¹₁`
truth. Deciding a class's truth is one jump above what the class can use, just
as the theorems of PA are one jump above what PA can use for naming
(`GENERAL-NAMING-THEOREM.md` §7).

*Remark (a one-formula instance of Claim B).* For (b) there is also a direct
formula, with no oracle machine in between: `∃S (Sat(S) ∧ x = 1 + N_TA(n̄)
computed inside S)`, where "computed inside `S`" says that `x − 1` is the
largest number named by an arithmetic formula of size `≤ n`, reading truth off
`S`. It is `Σ¹₁`, has size `C + 6·log₂(n+2)`, and names `N_TA(n) + 1`. So
`N_{Σ¹₁}(C + 6·log₂(n+2)) > N_TA(n)`: Claim B of `THE-LADDER.md` §3 for the
step from arithmetic to second-order truth. (Suggested by the "one scale for
the whole ladder" thread.) **[paper]**

## 5. Is the `Π¹₁` rung a single oracle Busy Beaver?

Not for a hyperarithmetic oracle (Theorem 4(c)), and not for any oracle that
computes `O` (Theorem 4(d)). Whether some `Y` strictly between (non-
hyperarithmetic, not above `O`) has `BB^Y` in the growth class of `N_{Π¹₁}`
is open here; it is the transfinite version of Open Question 1 in
`GENERAL-NAMING-THEOREM.md` §11. **[open]**

A related open question: does `N_{Π¹₁}` compute `O`? (`BB` computes the
halting problem because a halting time bounds the search; a true `Π¹₁`
sentence is witnessed by an ordinal rank, not a number, so the same trick
does not apply directly.) **[open]**

*Remark (notations instead of formulas).* One can charge an oracle `H_b` by
the length of a program that outputs `b`, instead of by a `Π¹₁` description.
The lower bound is unchanged (the named tuple can include the program's
halting trace). For the upper bound, given `φ ∈ Π¹₁` naming `m`, the
computable trees `T_i` (well-founded iff `φ(i)`) and `S_i` (well-founded iff
`¬φ(i)`, from `θ⁻` of Theorem 1) give a single well-founded computable tree
`⋃ᵢ ⟨i⟩⌢(T_i × S_i)`, of rank at least that of `T_m`, computable from `φ`; a
notation for its rank is then computable from `φ` (Kleene), and an `H`-set a
few levels above it decides which `T_i` have rank below that notation. That
would make `N_{Π¹₁}` equal, up to `n log n` rescaling, to Busy Beaver over
pairs (program for a notation `b ∈ O`, program run with oracle `H_b`).
**[expected; sketch only, relies on the effective form of Suslin–Kleene]**

## 6. Where infinite-time Turing machines sit

`THE-LADDER.md` §5a placed the Busy Beaver of infinite-time Turing machines
(ITTMs) on the "richer languages" rung, approximately. Let `Σ_∞(n)` be the
largest number written on the output tape by an ITTM with at most `n` states
that halts on blank input (Long and Stanley's definition, arXiv:1401.2187).

**Proposition 6.** `Σ_∞` eventually dominates `BB^O`, hence `N_{Π¹₁}`; and
`N_{Σ¹₂}(6·log₂(n+2) + C_h) > Σ_∞(h(n))` for every computable `h`.

*Proof.* Lower: `O` is ITTM-decidable (every `Π¹₁` set is, Hamkins–Lewis
Corollary 2.3), and an ITTM with `O` on its tape can decide in `ω` more steps
whether `U^O(p)` halts, so `BB^O` is ITTM-computable; Long–Stanley Theorem 1
says `Σ_∞` eventually dominates every total ITTM-computable function.
Upper: the sets `h_∞ = {p : p halts on blank input}` and
`G = {(p, k) : p halts on blank input with output k}` are ITTM-semi-decidable,
hence `Δ¹₂` (Hamkins–Lewis Theorem 2.5); `Σ_∞` is computable from `h_∞ ⊕ G`
(for each `n`-state `p`, ask whether it halts; if so, find its output in `G`).
Argue as in Theorem 4(f). ∎ **[paper, using classical Hamkins–Lewis 2000,
Corollary 2.3 and Theorem 2.5, and Long–Stanley 2013, Theorem 1]**

So the placement is now exact up to growth class:
`N_{Π¹₁} < BB^O < Σ_∞ < N_{Σ¹₂}`.

## 7. What must be accepted

- **`Π¹₁` and `Σ¹₁`.** A `Π¹₁` sentence is true iff a certain computable tree
  is well-founded, and this does not depend on the universe of sets (Mostowski
  absoluteness). **[classical]** So the `Π¹₁` rung needs only that
  "this computable tree has no infinite branch" is definite, which is much
  less than a completed power set of `ℕ`.
- **`Σ¹₂` and `Π¹₂`.** Truth is the same in `L` as in `V` (Shoenfield
  absoluteness). **[classical]** So these values too are fixed by any
  universe of sets, without settling questions like the continuum hypothesis.
- **`Σ¹₃` and above.** Truth can differ between universes (for example
  between `L` and a forcing extension). **[classical]** From here on the named
  numbers are definite only if one accepts a single intended `𝒫(ℕ)`.

This matches the proposal in `THE-LADDER.md` §4 to price rungs by what must be
assumed: the first two second-order rungs are cheap, and the price jumps at
`Σ¹₃`.

## 8. Is this known?

Checked on 2026-11-24: `LITERATURE-SURVEY.md`; Googology Wiki
"Second-order arithmetic" and "Busy beaver function"; Munafo's large-numbers
pages (mrob.com, page 9, on Rayo/FOST); Aaronson's "The Busy Beaver Frontier";
Goucher's Ξ function; Simmons arXiv:1809.08676; Hamkins–Lewis arXiv:math/9808093;
Long–Stanley arXiv:1401.2187; web searches for second-order or hyperarithmetic
naming and Busy Beaver with oracle `O`.

- **Classical ingredients:** Suslin–Kleene (K1), `Π¹₁`-completeness of `O`
  (K2), uniqueness of `H`-sets (K3), universal `Σ¹_k` formulas (K5), Mostowski
  and Shoenfield absoluteness, Hamkins–Lewis on ITTMs, Long–Stanley's ITTM
  Busy Beaver.
- **Not found:** a naming (largest definable number) function for
  second-order arithmetic in the googology sources we read (they discuss
  `Z₂` only for proof-theoretic ordinals, and Rayo's function for first-order
  set theory); any statement that `Σ¹₁` and `Π¹₁` naming coincide, that `Π¹₁`
  naming is Busy Beaver over hyperarithmetic oracles, or that `BB^O` sits
  strictly between the `Π¹₁` and `Σ¹₂` rungs. Long–Stanley compare `Σ_∞` with
  ordinary `BB` and with `Π¹₁`-recursive functions, not with definability.
- **Closely related, not checked:** Kolmogorov complexity for `Π¹₁` machines
  (Hjorth and Nies, "Randomness via effective descriptive set theory", 2007,
  and later work on `Π¹₁`-randomness). By Theorem 1, the shortest `Π¹₁`
  definition of a number should be within a linear factor of a `Δ¹₁`-oracle
  description length; whether something like this is stated there we did not
  check.

**Suggested wording:** "Naming by `Σ¹₁` or `Π¹₁` formulas of second-order
arithmetic is the Busy Beaver function over hyperarithmetic oracles (counting
the oracle's description); it strictly beats naming by arithmetic truth, and
Busy Beaver with oracle Kleene's `O` lies strictly between it and `Σ¹₂`
naming. The ingredients are classical; we found no earlier statement." Do not
call Theorem 1 deep: it is a short observation, and its value is in the
comparisons.

## 9. Status and what would make it solid

All theorems here are **[paper]**, written in one pass by the thread that
proposed them, not yet re-read or refereed. The steps most worth a second
read: the closure properties used for (iii) in each class (in particular
number `∀` over `∃X` needs countable choice in the metatheory), the claim in
Theorem 4(f) that `V_k` decides the "names something" sentence, and the
ITTM step "decide in `ω` more steps whether `U^O(p)` halts".

Lean: none. Mechanizing even Theorem 1 needs second-order formulas and oracle
machines, neither of which the project's Lean development has
(`GENERAL-NAMING-THEOREM.md` §10). Theorem 1 for first-order `Γ = Σ_k`
would be the realistic first target, once oracle machines exist.

Open questions: §5 (single oracle for the `Π¹₁` rung); the §5 remark (prove
the notation form); and the full second-order truth function `N_{Z₂}`, which
by the argument of Theorem 4(f) dominates every rung `N_{Σ¹_k}` and is beaten
by `BB` with the second-order truth set as oracle, a limit and not a rung,
like `N_TA` one level down. **[paper, same argument; not written out]**
