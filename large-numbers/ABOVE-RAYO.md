# Above Rayo: the map, the fine ladder between heights, and where Fish number 7 really sits

Written 2026-11-25. This is the third note on second-order Rayo, after
`SECOND-ORDER-RAYO.md` and `SECOND-ORDER-RAYO-II.md` ("note II"). It settles
three open items of note II, corrects one of its placements, and puts
everything above Rayo on one map. `THE-LADDER.md` §2 ("Above Rayo") and §5
are updated to match.

Tags as elsewhere: **[paper]** argued here and not independently checked,
**[classical]** known, cited from memory or the named source, **[expected]**
believed but not proved here, **[open]**. Nothing here is machine-checked.

## 0. In plain language

1. **Giving Rayo's language a symbol for a function never reaches the next
   truth step.** In arithmetic, handing Busy Beaver an oracle for its own
   function climbs a rung, because a whole function on the numbers is a new
   kind of object for arithmetic. In set theory it is not new: every function
   on the numbers is already a set. So a function symbol is the same as being
   allowed to mention one particular set. Truth about *all* sets cannot be
   packed into one set (Tarski), so this never reaches "Rayo plus a truth
   predicate" (Proposition 1).

2. **So Fish number 7 sits lower than we thought.** Fish's hierarchy feeds
   Rayo's function back in as an oracle, again and again, along a countable
   ordinal. By point 1 the *whole* hierarchy sits strictly between Rayo and
   the first Rayo+ step (Theorem 2). Note II and `THE-LADDER.md` placed it on
   the Rayo+ steps themselves. That was too high.

3. **Between "Rayo" and "second-order Rayo" there is a fine ladder, and we
   can name its rungs.** Restrict the classes to those definable after `β`
   rounds of adding truth. Second-order naming then gives exactly Rayo+
   stage `β + 1` (Theorem 3). In set-theory terms, these rungs are the
   constructible hierarchy built on top of the universe: `L_β(V)`.
   Full second-order Rayo sits above every one of them. Weak class theories
   such as minimal Morse–Kelley models land at particular rungs of this fine
   ladder (§3).

4. **A taller universe does not automatically win.** A small universe `V_κ`
   can have a faster Rayo function than the real universe `V`, even with
   `κ` below `ω₂`, as long as `κ` is not definable in `V` (Proposition 4).
   The rule "bigger universe beats" from note II needs the smaller universe
   to be *describable* from inside the bigger one. This is the ladder's
   general rule again: one rung is only comparable with another when it can
   describe the other.

5. **The map.** Above Rayo, every known step is one of three kinds: a
   *parameter* step (adds a set; stays below the next truth step), a *truth*
   step (the fine ladder, `L_β(V)`), or a *height* step (one more powerset
   level, i.e. one more order of logic, or a taller universe that can be
   described). Belief costs start only at the height steps (§5).

## 1. Parameters never reach the next truth step

Write `L₁[p]` for Rayo's language with one extra constant symbol denoting the
set `p`. A function symbol `f : ω → ω` is the special case `p = f`, since
`f(a) = b` iff `(a, b) ∈ f`. Each occurrence costs a constant number of
symbols either way. Write `N₁[p]` for its naming function, and `N_Tr` for
naming in `L₁ + Tr` (Rayo+ stage 1), as in note II.

**Proposition 1.** If `p` is definable in `L₁ + Tr` by a formula of size
`d`, there is `c` (independent of `p`) with

```
N_Tr( c + d + 6·log₂(n+2) )  >  N₁[p](n)      for every n.
```

*Proof.* "`k` is named by the `L₁[p]` formula `φ`" is
`Tr(⌜∀x (φ(x, y) ↔ x = z)⌝, {y ↦ p, z ↦ k})`: truth with `p` passed as the
value of a variable. Tarski's satisfaction relation handles parameters
because assignments are arbitrary. So "one more than the largest number named
by an `L₁[p]` formula of size `≤ n`" is an `L₁ + Tr` formula of the stated
size. ∎ **[paper]**

Conversely, `L₁[p]` never defines `Tr`, for any set `p`. A definition of
truth with a parameter is still a first-order definition with a parameter,
and Tarski's theorem rules those out. **[classical]** So parameter
extensions, however clever, sit strictly between Rayo and stage 1.

*Why arithmetic is different.* In arithmetic the universe is `ω`. A function
`ω → ω` is not an element of it, so an oracle for it is genuinely new
information, and `BB` with a `BB` oracle climbs a rung (`MIDDLE-RUNGS.md`).
In set theory the universe already contains every such function.
**[paper; the comparison is the point of this section]**

## 2. Fish number 7

Fish's definition (Googology Wiki, read 2026-11-24; see note II §6):
`R_0(n) = n`, `R_{α+1} = RR(R_α)`, where `RR(f)` is Rayo's function for the
language with a symbol for `f`, `R_λ(n) = R_{λ[n]}(n)` at limits, and
Fish number 7 `= F7^{63}(10^100)` with `F7 ≈ R_{ζ₀}`.

**Theorem 2.** There is a constant `c` with
`N_Tr(c + 6·log₂(n+2)) > R_{ζ₀}(n)` for every `n`. Fish number 7 is below
`N_Tr(c′)` for a modest constant `c′`. **[paper]**

*Proof.* Let `Φ(f, g)` be the `L₁ + Tr` formula "`g(n)` is the largest
number named by an `L₁[f]` formula of size `≤ n`, for every `n`", written as
in Proposition 1. It has fixed size and defines `g = RR(f)`. Consider:

> there is a function `s` on `ζ₀ + 1` such that `s(0)` is the identity, for
> all `α < ζ₀` we have `Φ(s(α), s(α+1))`, at limits `s(λ)(n) = s(λ[n])(n)`,
> and `x = s(ζ₀)(n)`.

Here `ζ₀` and its fundamental sequences are given by a fixed `L₁` formula.
The sequence `s` exists and is unique by transfinite recursion along the
countable ordinal `ζ₀`. This uses replacement for formulas that mention
`Tr`, which holds under the full-semantics reading that makes `Tr` definite
in the first place (Morse–Kelley proves it). So `R_{ζ₀}(n)` is defined by an
`L₁ + Tr` formula of size `c + 6·log₂(n+2)`. Add one and apply Claim B. For
the number itself, iterate `F7` 63 times inside the same formula. ∎

The same proof works for any definable ordinal in place of `ζ₀`, and for any
"feed the function back in" scheme whose recursion has set length. All of
them stay below stage 1. **[paper]**

*Correction.* Note II §6 placed `R_α` near Rayo+ stage `α`, and
`THE-LADDER.md` listed Fish number 7 under Rayo+. Both were too high. Fish
number 7 sits strictly between Rayo and Rayo+ stage 1. It is still far above
Rayo: `R_2` already beats every fixed iterate of Rayo's function.

*The Arias function* (Zenodo 18421517, 2026; only the abstract is readable,
the PDF was rate-limited) "corresponds to a functional iteration of Rayo₂".
If "Rayo₂" is second-order Rayo and the iteration is a recursion of set
length, then Proposition 1 one level up puts it strictly between
second-order Rayo and the first truth step above it. In particular it is
below third-order Rayo. **[expected; conditional on its definition]**

## 3. The fine ladder between Rayo and second-order Rayo

Let `S` be the ramified truth hierarchy of note II §1.2. `S↾β` is stages
below `β`, and `S↾1` is first-order truth. Rayo+ stage `β` is naming in
`L₁ + S↾β`. Call its naming function `N^{<β}`, so `N^{<1} = N_Tr`. Let

```
C_β := classes first-order definable over (V, ∈, S↾β) with set parameters.
```

`C_0 = Def(V)`, the range of note II's Theorem A.

**Theorem 3.** For each ordinal `β` defined by an `L₁` formula `δ`, there is
`c_δ` with

```
N₂^{C_β}(n) ≤ N^{<β+1}(c_δ·n + c_δ)    and    N^{<β+1}(n) ≤ N₂^{C_β}(c_δ·n + c_δ).
```

*Proof sketch.* As for Theorem A of note II, one stage up.

(Down.) A class in `C_β` is `{x : (V, S↾β) ⊨ θ(x, p)}`. Membership
`x ∈ X` becomes `S(β, e, ⟨x, p⟩)`, which is stage `β`, inside `S↾(β+1)`.

(Up.) The class `S↾β` lies in `C_β`. It is pinned down among *all* classes by
one `L₂` formula `IterSat_δ(Y)`, unique by the least-disagreement argument of
note II §1.2. Stage `β` itself is not in `C_β`, but its size-bounded pieces
are: `PartSat` for `L₁ + S↾β` formulas of size `≤ k` is definable over
`(V, S↾β)`. So `S(b, e, s)` becomes
`∃Y (IterSat_δ(Y) ∧ (b, e, s) ∈ Y)` for `b < β`, and
`∃Y ∃T (IterSat_δ(Y) ∧ PartSat^Y(T, size(e)) ∧ (e, s) ∈ T)` for `b = β`. ∎
**[paper]**

So the class ranges `C_0 ⊂ C_1 ⊂ C_2 ⊂ …` give exactly the Rayo+ stages
`1, 2, 3, …`, and so on transfinitely. The same works along any class
well-order definable in `L₂` (note II §1.2). **[paper]**

**In set-theory terms.** Picture `V` as `V_κ` inside a bigger universe. The
classes definable over `(V_κ, S↾β)` are, up to re-indexing of `β`, the
subsets of `V_κ` that appear in the constructible hierarchy built over
`V_κ`: `L_1(V_κ) = Def(V_κ)`, and so on. Each `L`-step adds the subsets
definable from the previous level, which is one more truth step. Class
well-orders over `V_κ` have length below `κ⁺`, so the fine ladder runs
through `L_β(V_κ)` for `β < κ⁺`. Naming over `L_β(V_κ)` climbs in step with
Rayo+ stage `β`. **[expected; the indexing between `L`-levels and `S`-stages
is not worked out, and limit stages may need a factor `ω`]**

**Where class theories land.** A model of a class theory whose sets are
`V_κ` has a range of classes `C`. When `C` is of the form
`P(V_κ) ∩ L_θ(V_κ)`, as for the minimal models of GBC + `ETR`, of
GBC + `Π¹₁`-CA, or of KM when these exist, second-order naming with range
`C` is first-order naming over `L_θ(V_κ)`, a rung of the fine ladder.
**[expected]** Full second-order Rayo (all of `P(V_κ) = V_{κ+1}`) beats
every rung `L_β(V_κ)` with `β` definable. That is Theorem 2 of the first
note, since such an `L_β(V_κ)` is coded by one class. **[paper]** If
`V_{κ+1} ⊆ L(V_κ)`, for example under `V = L`, full second-order Rayo sits
just above the whole fine ladder. Otherwise it also sees subsets that the
fine ladder never builds.

## 4. A taller universe does not automatically win

Note II Corollary C2: if `V_κ` is defined in `W` by a short formula, then
first-order Rayo in `W` beats every finite-order Rayo over `V_κ`. Open item 1
asked about undefinable `κ`.

**Lemma 4a (only the theory matters).** The naming record of `V_κ` at size
`n` depends only on which sentences of size about `n` are true in `V_κ`.
So if `W` defines some `κ₀` with `V_{κ₀}` and `V_κ` satisfying the same
sentences, `N₁^{V_κ} = N₁^{V_{κ₀}}`, and `W` wins. The same holds for
`k`-th order. **[paper]**

**Proposition 4 (it can fail).** Assume `V = L`, to have a definable
well-order of the reals. Let `b : ω → ω` be any function, for example
`b(j) = N₁^V(j) + 1`. There is an ordinal `κ` with `ω₁ < κ < ω₂` and a
constant `c` such that

```
N₁^{V_κ}( c + 6·log₂(j+2) )  ≥  b(j)      for every j.
```

With `b = N₁^V + 1`, Rayo's function of the small universe `V_κ` is not
dominated by the real Rayo function, under any rescaling of the form
`c′ + 6·log₂`. **[paper; uses `V = L`, which I expect can be weakened]**

*Proof sketch.* Under `V = L` the reals are well-ordered in type `ω₁` by
`<_L`, which is definable over `V_κ` for `κ > ω₁` by a fixed formula. Let
`b` be the `δ`-th real and `κ := ω₁ + ω·(1+δ)`, a limit ordinal below `ω₂`.
Inside `V_κ` a fixed formula recovers `δ` from the height: `ω·(1+δ)` is the
supremum of the order types of the intervals `[ω₁, β)` for `β < κ`, and
`δ ↦ ω·(1+δ)` is injective. A fixed formula then gives the `δ`-th real
`b`. Writing `j` in binary, the formula "`x = b(j)`" has size
`c + 6·log₂(j+2)`. ∎

*Consistency check.* By Corollary C2 of note II, such a `κ` cannot be
definable in `V`. Indeed, `b = N₁^V + 1` is not definable in `V`, so neither
is `δ` or `κ`.

*Reading.* The height of a universe is not by itself a measure of naming
power. A small universe whose height encodes a fast function can name
faster. What makes the "taller universe" comparison work is that the
smaller universe can be described from inside the taller one. This is the
ladder's rule from `THE-LADDER.md` §1: two rulebooks compare up to a fixed
overhead only when each can describe the other. **[paper]**

## 5. The map above Rayo

Every step above Rayo considered in this project is one of three kinds.

| kind | what is added | example | where it lands | extra belief |
|---|---|---|---|---|
| parameter | a symbol for one set or function | Fish number 7 (`R_α`, any set-length recursion) | strictly between a truth stage and the next (Prop. 1, Thm 2) | none |
| truth | truth for the current language, iterated | Rayo+ stages; second-order Rayo with classes `C_β`; `L_β(V)` | the fine ladder (Thm 3); stage `β+1` = class range `C_β` | none: fixed by first-order truth (note II Prop. B) |
| height | one more powerset level, or a taller universe that can be described | full second-order Rayo = Rayo over `V_{Ord+1}`; `k`-th order = `V_{Ord+k−1}`; Rayo in `W` with `V` definable in `W` | above every fine-ladder rung below it (note II Thm C, Cor C2) | yes: which sub-collections exist, or which taller universe |

Above each height step a new fine ladder starts (truth for the new
language, iterated), and above that the next height step. Undescribable
heights are not on the map (Prop. 4). BIG FOOT tried to jump in height by
positing a taller universe without describing it, and its definition does
not determine a number (`phase0/e-foot.md`). **[paper; the map is a summary,
not a theorem]**

## 6. Theorem C of note II: the type-matching formulas written out

Note II left `Same_{i,j}` unwritten. Domains: type 1 is `D_1 = V_λ`, type
`j+1` is `D_{j+1} = P(D_j) = V_{λ+j}`. As sets `D_1 ⊂ D_2 ⊂ …`. A type-`j`
object's elements, read in `V`, are exactly its type-`(j−1)` members (for
`j = 2` these are elements of `V_λ`, type 1).

`Same_{i,i}(a, b) := a = b`. For `i < j`:

```
Same_{i,j}(a, b) := ∀u^{(j−1)} ( u ∈ b → ∃v^{(i−1)} ( v ∈ a ∧ Same_{i−1,j−1}(v, u) ) )
                  ∧ ∀v^{(i−1)} ( v ∈ a → ∃u^{(j−1)} ( u ∈ b ∧ Same_{i−1,j−1}(v, u) ) ),
```

with the convention that when `i = 1`, "type `0`" means type 1 under `∈`
between sets. Correctness is by `∈`-induction and extensionality. The size
is `O(2^j)`, a constant for fixed `k`.

*Up direction (first-order over `V_{λ+k}` into `(k+1)`-th order over
`V_λ`).* Every element of `V_{λ+k}` is a type-`(k+1)` object. Quantifiers
become type-`(k+1)` quantifiers. `x = y` stays. `x ∈ y` becomes
`∃u^{(k)} (u ∈ y ∧ Same_{k,k+1}(u, x))`. A named number `z` of type 1
corresponds to `x` via `Same_{1,k+1}(z, x)`.

*Down direction.* Define the levels inside `V_{λ+k}` by
`Lev_1(u) := ∀y (y ⊆ u)`, which gives `u = V_{λ+k−1}`, and
`Lev_{j+1}(u) := ∃w (Lev_j(w) ∧ u ∈ w ∧ ∀y ∈ w (y ⊆ u))`. Size grows
linearly in `j`. Type-`j` quantifiers become quantifiers bounded by the
matching level, and typed membership becomes `∈`. **[paper; this closes
note II open item 6, first half]**

## 7. Open items

1. The exact indexing between `L_β(V_κ)` and the `S`-stages (§3), including
   limits.
2. Remove `V = L` from Proposition 4. Any definable way to read a fast real
   off the height would do.
3. The Arias function: read the PDF (Zenodo rate-limited the download twice)
   and check the conditional placement in §2.
4. Where exactly do the minimal models of `ETR`, `Π¹₁`-CA and KM sit on the
   fine ladder (which `θ`)?
5. Re-read Theorems 2 and 3 independently.
