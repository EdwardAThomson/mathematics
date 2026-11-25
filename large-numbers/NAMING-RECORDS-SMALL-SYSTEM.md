# Naming records in a tiny system

*Written 2026-11-24. A computed companion to
`PROOF-BUDGETS-AND-COMPLEXITY.md` (§2 and §4). Question: in a formal
system small enough to search completely, what is the largest number you
can name with a name of size `n` and a proof of length `t`, and which
numbers are cheapest to name? Code and full tables are in
`naming-records/`. Second pass, same day: lemma proofs with reuse (§8),
larger sizes and a corrected binary growth law (§9), and naming by a
property (§10).*

Tags as elsewhere: **[computed]** produced by the script here and
reproducible in under a minute; **[observation]** a pattern in the
computed tables, not proved; **[paper]** argued here.

---

## 0. The answer in plain language

We took two toy arithmetics: one that writes numbers in unary
(`SSS0` is 3) and one that writes them in binary. In each, a *name* is a
closed term like `3^5` and a *proof* that it names 243 is the step-by-step
calculation that turns the term into the numeral for 243. We charge for
the proof by counting every symbol in every line of the calculation, the
way the proof-budgets note counts `|π|`. Then we listed every name up to
size 12 (unary) or 10 (binary), about 1.9 million names, and worked out
each one's proof.

1. **For small budgets the numeral is unbeatable.** Below a few hundred
   proof symbols, the largest number you can name is just the largest
   numeral that fits. Compound names like `5*2` or `24^2` start to win at
   227 symbols in unary and 742 in binary with our fixed proof format
   (220 and 741 with the best rewriting order), and not before.
   **[computed]**

2. **After that, the record grows far below the ceiling, because the
   toy has no variables.** The budget `t` caps the record at `t − 1`
   (unary) or `2^{t−1}` (binary) because the proof has to write the
   answer down (Proposition 1 of that note). The toy's records sit far
   lower: roughly `0.7·√t` in unary, and about `2^{0.29·√t}` in binary,
   carried by powers of two. (A first version of this note read
   `t^{1/3}` off names of size `≤ 10`. That was an artifact of the name
   size: see §9.) In `PA⁻` with ordinary first-order proofs the records
   are `t/C` and `2^{t/C}`, within a constant of the ceiling
   (Proposition 2 of the proof-budgets note, as revised after this
   note). The difference is lemmas with variables, which the toy cannot
   state. **[computed; the toy's growth laws are an observation over the
   range computed]**

3. **Cheapest names: in binary, almost every number is named best by its
   own numeral.** Among the numbers we can name, only 109 beat their own
   binary numeral on the combined cost `D(k) = size + log₂(proof
   length)`, the note's `D_T`. All of them are powers, such as `6^6 =
   46,656` (the smallest) or `3^31` (the biggest saving, 29 bits), or a
   power with one binary digit added. That is the Levin `Kt` picture in
   miniature: most numbers are incompressible, and the few that compress
   are the ones with a short *and fast* description. **[computed]**

4. **In unary it is the other way round.** A unary numeral costs about
   `k` symbols, so any power beats it once it is big enough: `4^5 = 1024`
   costs `D = 32` against 1,035 for its numeral. The 36 numbers that beat
   their numerals start at 15 (`5*3`). **[computed]**

5. **With proofs free, the picture changes completely.** Without charging
   for the proof, a size-10 binary name reaches `3^31 ≈ 6·10^14`, while
   with the proof charged (`D ≤ 14`, the range our search covers
   completely) the record is still the numeral 511. Charging for proofs
   is what makes "short name" mean "short name that is also quick to
   check". **[computed]**

6. **Reusing lemmas changes constants, not growth laws** (§8). In unary
   it saves under 2%. In binary it makes powers of two 2 to 3.5 times
   cheaper to prove, and other powers 15–30% cheaper. **[computed]**

7. **At larger sizes the toy's binary law is `2^{Θ(√t)}`** (§9). Powers
   of two are cheap to multiply, since only the digits shift, so
   `log₂(record) ≈ 0.29·√t` (chains) and `0.58·√t` (lemma proofs). This
   suggested raising Proposition 2's binary exponent from `1/3` to `1/2`.
   Checking it in `PA⁻` gave more: exponent `1`, that is `2^{t/C}`, from
   lemmas with variables proved by doubling (§9). **[computed;
   observation]**

8. **Naming by a property: overhead at small sizes, big savings later**
   (§10). Names `p(x) = c`, where the proof guesses `x` and checks it, never
   beat term names up to size 11. For numbers like `(4^j − 1)/3` that
   are easy to check but not a short calculation, they beat the numeral
   from about 30 bits on, by 100 bits at 127 bits. **[computed]**

**What the toy cannot show.** Its proofs are calculations, or a guess
followed by a calculation, so the measure behaves like Levin's `Kt`. It
cannot name a number by an arbitrary property and *prove* that only one
number has it. That is where the proof-budgets note's interesting
question lives: whether *guess-and-verify* proofs (`KNt`) are ever much
cheaper than calculations (`Kt`), which is tied to NEXP versus EXP/poly
(Corollary 6 there). §10 shows the guessing side of this. It cannot show
that a gap is unavoidable; see §6.

---

## 1. The two systems

Both are equational arithmetics with the defining equations as rewrite
rules, read left to right.

**System U (unary).** Symbols `0`, `S`, `+`, `·`, `^`. Rules:

    x+0 → x        x+Sy → S(x+y)
    x·0 → 0        x·Sy → x·y + x
    x^0 → S0       x^Sy → x^y · x

Numerals are `S…S0`; the numeral for `k` has size `k + 1`.

**System B (binary).** Constructors `0`, `D0`, `D1` with
`D0(x) = 2x` and `D1(x) = 2x + 1`, plus `S`, `+`, `·`, `^`. Rules:

    D0(0) → 0
    S(0) → D1(0)          S(D0 x) → D1 x           S(D1 x) → D0(S x)
    x+0 → x   0+x → x     D0x+D0y → D0(x+y)        D0x+D1y → D1(x+y)
                          D1x+D0y → D1(x+y)        D1x+D1y → D0(S(x+y))
    x·0 → 0   0·x → 0     D0x·y → D0(x·y)          D1x·y → D0(x·y) + y
    x^0 → D1(0)           x^D0(y) → x^y · x^y      x^D1(y) → (x^y · x^y)·x

Numerals are binary digits, least significant outermost, with no leading
zero; the numeral for `k ≥ 1` has size (number of binary digits) + 1.
So `D0(D1(D1(0)))` is 6.

**Size** of a term is its number of symbols (syntax-tree nodes). In the
tables a name is shown both as it is written and as it reads, e.g.
`(D0(D1(D1(0)))^D1(D1(0)))` = `6^3`, of size 8.

**Names and proofs.** A name for `k` is any closed term with value `k`.
A proof that it names `k` is a chain of terms `s = t₀ → t₁ → … → t_m`,
each step one rule applied somewhere inside the term, ending in the
numeral for `k`. Its **length** is the total number of symbols in the
chain, `|t₀| + |t₁| + … + |t_m|`. This mirrors the Hilbert-style count
in the proof-budgets note: the proof writes every intermediate term, and
its last line contains the numeral, so Proposition 1's ceiling applies
(a proof of length `t` names at most `t − 1` in unary and less than
`2^{t−1}` in binary). **[paper]**

**Which proof.** Every name has many chains, one per order of rewriting.
The tables use one fixed order, the **evaluation proof**: rewrite the
leftmost innermost spot first (evaluate arguments before using them),
except that a rule which throws an argument away (`x+0`, `x·0`, `x^0`,
`0+x`, `0·x`) fires as soon as it applies. This gives one definite proof
per name, computable exactly and quickly. It is not always the shortest
chain; §5 measures how far off it is.

**What was computed.** Every closed term of size up to 12 in U
(493,800 terms) and up to 10 in B (1,394,746 terms), with its value,
evaluation-proof length and number of rewrite steps. Every one of these
names has an evaluation proof under 10⁷ symbols, the cap used. From these:

- `record(n, t)`: the largest `k` named by a term of size `≤ n` with
  proof length `≤ t`;
- `K(k)`: the least size of a name for `k`, with the proof free;
- `D(k)`: the least `size + log₂(proof length)` over names for `k`. This
  is the proof-budgets note's `D_T(k)` for this toy.

---

## 2. Records

### 2.1 Unary

Largest `k` named with name size `≤ n` and proof length `≤ t`
**[computed]**:

| n \ t | 10 | 100 | 1,000 | 3,000 | 10⁴ | 3·10⁴ | 10⁵ | 10⁶ | 10⁷ | numeral alone |
|---|---|---|---|---|---|---|---|---|---|---|
| ≤ 7 | n−1 | n−1 | n−1 | n−1 | n−1 | n−1 | n−1 | n−1 | n−1 | n−1 |
| 8 | 7 | 7 | 9 | 9 | 9 | 9 | 9 | 9 | 9 | 7 |
| 9 | 8 | 8 | 16 | 27 | 27 | 27 | 27 | 27 | 27 | 8 |
| 10 | 9 | 9 | 17 | 32 | 81 | 81 | 81 | 81 | 81 | 9 |
| 11 | 9 | 10 | 18 | 36 | 82 | 125 | 256 | 256 | 256 | 10 |
| 12 | 9 | 11 | 20 | 37 | 83 | 128 | 257 | 729 | 1,024 | 11 |
| ceiling `t − 1` | 9 | 99 | 999 | 2,999 | 9,999 | 29,999 | 99,999 | 999,999 | 9,999,999 | |

Where compound names first win, and the best they can do
**[computed]**:

| n | best numeral | first beaten by | value | proof length | largest at size n, any budget | proof length |
|---|---|---|---|---|---|---|
| 8 | 7 | `3^2` | 9 | 412 | `3^2` = 9 | 412 |
| 9 | 8 | `3*3` | 9 | 238 | `3^3` = 27 | 1,664 |
| 10 | 9 | `5*2` | 10 | 227 | `3^4` = 81 | 9,572 |
| 11 | 10 | `S(5*2)` | 11 | 243 | `4^4` = 256 | 76,189 |
| 12 | 11 | `S(S(5*2))` | 12 | 259 | `4^5` = 1,024 | 1,141,980 |

Below size 8 nothing beats the numeral at any budget: the first
compound name worth more than every numeral of its size is `3^2`, of
size 8.

The staircase at size `≤ 12` (every budget where the record rises past
the numerals; full list in `naming-records/tables_U.md`):

| budget t | record | name |
|---|---|---|
| 259 | 12 | `S(S(5*2))` |
| 456 | 15 | `5*3` |
| 765 | 20 | `5*4` |
| 1,518 | 25 | `5^2` |
| 2,598 | 32 | `2^5` |
| 6,171 | 64 | `4^3` |
| 9,572 | 81 | `3^4` |
| 19,762 | 125 | `5^3` |
| 76,189 | 256 | `4^4` |
| 364,998 | 512 | `2^(3^2)` |
| 614,624 | 729 | `3^6` |
| 1,141,980 | 1,024 | `4^5` |

**Growth.** **[observation]** Over `10³ ≤ t ≤ 10⁶` the size-12 record is
`0.6√t` to `0.8√t` (20 at 10³, 83 at 10⁴, 257 at 10⁵, 729 at 10⁶). At
10⁷ it stops at 1,024 because no size-12 name is bigger with any
budget. The reason is the one in Lemma A1 of the proof-budgets note:
building a unary numeral of `k` takes about `k` steps through terms of
size about `k`, so roughly `k²` symbols. A first-order proof avoids this
with lemmas that have variables (Lemma A6 there), which the toy cannot
state.

### 2.2 Binary

Largest `k` named with name size `≤ n` and proof length `≤ t`
**[computed]**:

| n \ t | 10 | 100 | 1,000 | 3,000 | 10⁴ | 3·10⁴ | 10⁵ | 10⁶ | 10⁷ | numeral alone |
|---|---|---|---|---|---|---|---|---|---|---|
| ≤ 7 | 2^{n−1}−1 | same | same | same | same | same | same | same | same | 2^{n−1}−1 |
| 8 | 127 | 127 | 216 | 729 | 2,187 | 2,187 | 2,187 | 2,187 | 2,187 | 127 |
| 9 | 255 | 255 | 512 | 16,384 | 279,936 | ≈2^23.8 | ≈2^23.8 | ≈2^23.8 | ≈2^23.8 | 255 |
| 10 | 511 | 511 | 1,025 | 262,144 | ≈2^28.0 | ≈2^36.2 | ≈2^39.6 | ≈2^49.1 | ≈2^49.1 | 511 |
| ceiling `2^{t−1}` | 2^9 | 2^99 | 2^999 | 2^2999 | 2^9999 | … | … | … | … | |

Where compound names first win **[computed]**:

| n | best numeral | first beaten by | value | proof length | largest at size n, any budget | proof length |
|---|---|---|---|---|---|---|
| 8 | 127 | `6^3` | 216 | 879 | `3^7` = 2,187 | 4,167 |
| 9 | 255 | `8^3` | 512 | 842 | `3^15` ≈ 2^23.8 | 22,095 |
| 10 | 511 | `24^2` | 576 | 742 | `3^31` ≈ 2^49.1 | 216,059 |

The staircase at size `≤ 10` (selected rows; full list in
`naming-records/tables_B.md`):

| budget t | record | log₂ record | name |
|---|---|---|---|
| 742 | 576 | 9.2 | `24^2` |
| 1,027 | 4,096 | 12.0 | `16^3` |
| 2,882 | 262,144 | 18.0 | `8^6` |
| 4,020 | 2^21 | 21.0 | `8^7` |
| 7,013 | 2^24 | 24.0 | `4^12` |
| 11,433 | 2^30 | 30.0 | `4^15` |
| 27,998 | ≈2^36.2 | 36.2 | `6^14` |
| 37,947 | ≈2^38.8 | 38.8 | `6^15` |
| 106,275 | ≈2^42.1 | 42.1 | `7^15` |
| 216,059 | ≈2^49.1 | 49.1 | `3^31` |

**Growth.** **[observation]** At names of size `≤ 10`, `log₂(record)`
tracks `t^{1/3}` over `3·10³ ≤ t ≤ 3·10⁴`, but that is the name size
talking: the exponents these names can hold are at most 31. With larger
names (§9) the record holders become powers of two, and
`log₂(record) ≈ 0.29·√t`.

---

## 3. Cheapest names

`D(k) = size + log₂(proof length)`, minimised over names of `k`.
Compare it with the numeral's own cost `N(k) = |numeral| +
log₂|numeral|` (a numeral's proof is the one-line chain consisting of
itself).

### 3.1 Binary: the numeral almost always wins

Of all numbers named at size `≤ 10`, exactly **109** have a name that
beats their binary numeral on `D`. The smallest is `6^6 = 46,656`, and
every one is a power `a^b` (83 of them) or a power with a binary digit
or a successor around it (`D0(…)`, `D1(…)`: 20; `S(…)`: 6).
**[computed]** The largest
savings:

| k | numeral cost N(k) | D(k) | saving (bits) | best name | proof length |
|---|---|---|---|---|---|
| `3^31` ≈ 2^49.1 | 56.7 | 27.7 | 29.0 | `3^31` (size 10) | 216,059 |
| `3^30` ≈ 2^47.5 | 54.6 | 27.6 | 27.0 | `3^30` | 194,996 |
| `3^29` ≈ 2^46.0 | 52.6 | 27.4 | 25.2 | `3^29` | 173,098 |
| `7^15` ≈ 2^42.1 | 49.5 | 26.7 | 22.8 | `7^15` | 106,275 |
| `6^15` ≈ 2^38.8 | 45.3 | 25.2 | 20.1 | `6^15` | 37,947 |
| `2^18` = 262,144 | 24.3 | 21.5 | 2.8 | `8^6` (size 10) | 2,882 |
| `6^6` = 46,656 | 21.1 | 21.05 | 0.04 | `6^6` (size 9) | 4,243 |

The full list of 109 is in `naming-records/tables_B.md`. A counting
argument says this must happen: there are fewer than `2^d` names of cost
`≤ d`, so most numbers of `d` bits cannot have one. **[paper, standard]**
The table shows *which* numbers are the exceptions in this system: those
that are a small power, because exponentiation by squaring is the only
rule that turns a few symbols and a few thousand proof symbols into many
digits.

### 3.2 Unary: compound names win as soon as they can

A unary numeral costs about `k`, so compound names win early and by a
lot. 36 numbers beat their numerals, starting at 15 (`5*3`, size 11,
`D = 19.8` against `N = 20.0`). **[computed]**

| k | numeral cost N(k) | D(k) | best name | size | proof length |
|---|---|---|---|---|---|
| 15 | 20.0 | 19.8 | `5*3` | 11 | 456 |
| 16 | 21.1 | 18.7 | `4^2` | 9 | 822 |
| 27 | 32.8 | 19.7 | `3^3` | 9 | 1,664 |
| 81 | 88.4 | 23.2 | `3^4` | 10 | 9,572 |
| 256 | 265.0 | 27.2 | `4^4` | 11 | 76,189 |
| 512 | 522.0 | 30.5 | `2^(3^2)` | 12 | 364,998 |
| 1,024 | 1,035.0 | 32.1 | `4^5` | 12 | 1,141,980 |

### 3.3 Largest number per naming cost

For each cost `d`: the largest `k` with `D(k) ≤ d`, and the largest with
`K(k) ≤ d` (proof free). A name of size `s` has `D ≥ s + log₂ s`, so the
`D` column below is complete: no name larger than our search could get
in. **[computed]**

| d | unary, `D ≤ d` | unary, `K ≤ d` | binary, `D ≤ d` | binary, `K ≤ d` |
|---|---|---|---|---|
| 6 | 3 | 5 | 7 | 31 |
| 8 | 4 | 9 (`3^2`) | 15 | 2,187 (`3^7`) |
| 9 | 5 | 27 (`3^3`) | 31 | `3^15` ≈ 2^23.8 |
| 10 | 6 | 81 (`3^4`) | 63 | `3^31` ≈ 2^49.1 |
| 11 | 7 | 256 (`4^4`) | 127 | (beyond search) |
| 12 | 7 | 1,024 (`4^5`) | 127 | |
| 14 | 9 | | 511 | |
| 16 | 11 | | | |

In the complete range every `D` record is a plain numeral. Compound
names first enter the `D` records at `d = 19` in both systems (`4^2`,
`D = 18.7`, in unary; `8^3`, `D = 18.7`, in binary). That is past the
point where our search is exhaustive, so we only know these are lower
bounds for the true records at `d = 19`.

The `K` column is the "proof is free" world, the analogue of the
unbudgeted `Big_T`: there, size 10 already reaches `3^31`. The gap
between the columns is the whole effect of charging for proofs.

---

## 4. How this matches the proof-budgets note

| proof-budgets note | this toy |
|---|---|
| Prop. 1: the proof writes the numeral, so `Big^t ≤ t/2` (unary), `< 2^t` (binary) | same ceiling, `t − 1` and `2^{t−1}`; actual records far below it (§2) |
| Prop. 2 (revised): records at least `t/C` (unary) and `2^{t/C}` (binary), using lemmas with variables | unary records about `0.7√t`; binary records about `2^{0.29√t}`. The toy has no variables, so it pays for every doubling separately (§2, §9) |
| §4: `D_T(k) = |φ| + log₂|π|`, between `KNt` and `Kt` | `D(k)` computed exactly for the evaluation proof; behaves like `Kt` (§3) |
| Cor. 6: `D_T ≪ Kt` somewhere would separate NEXP from EXP/poly | not testable here: no quantifiers, so no guess-and-verify proofs (§6) |

The toy's proofs are much more restricted than the note's (no lemmas, no
quantifiers, no induction), so its records are lower bounds for what a
real theory with the same symbols could do in the same budget, and the
growth exponents are those of schoolbook arithmetic, not optimal ones.
The revised Proposition 2 shows how far from optimal: `√t` against `t`.

---

## 5. Evaluation proof against the shortest proof

The tables use the evaluation proof, one fixed rewriting order. A
shortest chain in *any* order can be shorter, because doing additions
earlier can keep the intermediate terms smaller. We measured the gap
with an exhaustive A* search (`astar_cost`, checked against a full
search on every name of size `≤ 6` in U and `≤ 5` in B). **[computed]**

- All names of size `≤ 8` (U) and `≤ 6` (B) with evaluation proof
  `≤ 500` (U) or `≤ 200` (B): the evaluation proof is shortest for 84%
  (U, 1,906 of 2,262) and 72% (B, 1,185 of 1,642). The big ratios are
  names like `0^S(1^1)`, where it pays to look at only part of an
  argument; none of these hold records.
- The record holders, where the search finishes (evaluation proof
  against shortest proof in any order):

  | name | value | evaluation proof | shortest proof |
  |---|---|---|---|
  | U: `5*2` (size 10) | 10 | 227 | 227 |
  | U: `S(S(5*2))` | 12 | 259 | 259 |
  | U: `7*2` | 14 | 363 | 363 |
  | U: `3*3` | 9 | 238 | 220 |
  | U: `3^2` | 9 | 412 | 384 |
  | U: `5*3` | 15 | 456 | 420 |
  | U: `6*3` | 18 | 592 | 544 |
  | U: `5*4` | 20 | 765 | 655 |
  | B: `24^2` | 576 | 742 | 741 |
  | B: `D1(8^3)` = 1,025 | 1,025 | 883 | 874 |
  | B: `16^3` | 4,096 | 1,027 | 1,021 |

  For `5^2` (U, evaluation proof 1,518) the search hit its limit of two
  million states.

So in binary the evaluation proof is within 1% of the shortest on every
record holder checked, and in unary within about 15%; with shortest
proofs the unary staircase in §2 moves left by up to that much. The
growth exponents and every qualitative statement above are unchanged.
The crossover budgets (227 and 742) are upper bounds for the
shortest-proof version, which has crossovers of at most 220 and 741.
Exact shortest proofs for the big witnesses (budgets of 10⁴ and up) are
out of reach of exhaustive search.

---

## 6. What the toy cannot show

- **No real quantifiers.** §10 adds one restricted form of naming by a
  property, `p(x) = c` with `p` increasing. That form gets its uniqueness
  for free. General names of the form "the unique `x` with property φ"
  need a proof that no other number fits, and that is where the
  `KNt`-versus-`Kt` question of the proof-budgets note lives. A
  first-order proof search is out of reach beyond a few dozen symbols.
- **No `KNt` gap.** Even with §10, every proof is a calculation plus a
  check. The toy cannot exhibit a number whose checked name is much
  cheaper than its computed one *and prove that nothing cheaper exists*.
- **Lemmas, but only one strategy.** §8 adds proofs that state a lemma
  once and reuse it, but they still follow one fixed evaluation order.
- **Small sizes.** The tables are complete for names of size `≤ 14`
  (unary) and `≤ 11` (binary). The growth laws are observations, not
  theorems.

---

## 8. Lemma proofs: stating a fact once and reusing it

*Added 2026-11-24, second pass.* A chain proof writes the whole term at
every step, and computes a repeated subterm twice. A **lemma proof**
(`lemmas.py`) is a list of equations instead, as in an equational-logic
or Hilbert proof. For each term `u` it meets, it proves one lemma
`u = numeral`:

- a congruence line `f(a₁,…) = f(n₁,…)`, from the arguments' lemmas
  `aᵢ = nᵢ` (left out if every argument is already a numeral);
- one rule-instance line `f(n₁,…) = r`;
- the lemma for `r`, and the conclusion `u = numeral`.

An erasing rule is used first when it applies, as before. A line `s = t`
costs `|s| + |t|`. We measure it two ways: **no reuse**, where every lemma
is proved again each time it is used, and **reuse**, where each distinct
lemma is proved once. `check_lemmas.py` writes out the full proof for
3,000 random names, checks that every line is a rule instance, a
congruence or a transitivity step from earlier lines, and confirms the
total. It found no problems. **[computed]**

**What reuse buys.** **[computed]**

| name | chain | lemmas, no reuse | lemmas, reuse |
|---|---|---|---|
| U: `3^4` = 81 | 9,572 | 26,422 | 25,998 |
| U: `4^5` = 1,024 | 1,141,980 | 3,399,816 | 3,385,628 |
| B: `3^7` = 2,187 | 4,167 | 6,099 | 4,264 |
| B: `2^20` | 12,546 | 10,366 | 2,919 |
| B: `2^31` | 23,336 | 20,998 | 8,463 |
| B: `3^31` | 216,059 | 189,800 | 151,857 |
| B: `2^(2^(2^3))` = 2^256 | 967,003 | 442,060 | 209,713 |
| B: `3^(2^(2^3))` = 3^256 | 363,265,053 | 59,151,184 | 49,354,880 |

- **Unary: reuse barely matters**, under 2%. A unary numeral has to be
  built one `S` at a time, and those steps never repeat. Lemma proofs
  are about 3 times longer than chains here, because every lemma
  restates a long numeral. The records shift right by that factor, and
  the `√t` law is unchanged (§9).
- **Binary: reuse matters for powers**, because `x^D0(y) → x^y · x^y`
  repeats a subterm at every level. Powers of two gain most, 2 to 3.5
  times, since their multiplications are cheap and the repeated work is
  most of the proof. For other bases the final big multiplications
  dominate, and reuse saves 15–30%.
- **Not writing the context matters more than reuse for big names.**
  For `3^256` the chain is 6 times longer than the lemma proof without
  reuse. The chain carries the rest of the term through every step of a
  long multiplication, and a lemma proof does not.

At name size `≤ 11` (binary), lemma proofs with reuse first beat the
numeral at 877 symbols (`32^2`, size 11). They name `2^48` within 10⁴
symbols, against `2^36` for chains. 570 numbers beat their numeral on
`D`, starting at `2^14` = 16,384 (`D = 20.0`), against 571 starting at
`6^6` for chains. Full tables: `naming-records/tables_B11L.md`,
`tables_U14L.md`.

---

## 9. Larger sizes, and the binary growth law

*Added 2026-11-24, second pass.* `big_run.py` keeps only the rows the
tables need, which takes the exhaustive search to **every name of size
`≤ 14` in unary (7.8 million) and `≤ 11` in binary (7.9 million)**, for
both proof formats, with proofs up to 10⁷ symbols. Full tables are
`tables_U14.md`, `tables_U14L.md`, `tables_B11.md` and `tables_B11L.md`.
**[computed]**

Records at the largest size, chain proofs:

| t | 10³ | 3·10³ | 10⁴ | 3·10⁴ | 10⁵ | 10⁶ | 10⁷ |
|---|---|---|---|---|---|---|---|
| unary, size ≤ 14 | 24 | 39 | 83 | 144 | 259 | 784 | 2,401 |
| binary, size ≤ 11 | 2,304 | 524,289 | 2^36.0 | 2^56.0 | 2^63.0 | 2^87.0 | 2^99.9 |

- **Unary.** `record / √t` stays between 0.7 and 0.85 from 10³ to 10⁷
  (2,401 = `7^4` at 10⁷). With lemma proofs it is 0.4 to 0.5
  instead. The exponent `1/2` of the first version of Proposition 2
  holds over this whole range. (The revised Proposition 2, with
  variables, gives `t/C`.)
- **Binary.** The crossover drops to 690 (`32^2`, size 11). From about
  10⁵ on, the record holders are powers of 3, 6 and 7 with exponents up
  to 63, and the size-11 ceiling `3^63 ≈ 2^99.9` is reached at about
  2·10⁶.

**The binary growth law is `2^{Θ(√t)}` here, not `2^{t^{1/3}}`.** At
fixed small name sizes the exponents the names can hold are capped, so
the tables cannot show the asymptotic law. `growth_families.py` follows
two families whose names grow only logarithmically, `2^(2^j)` and
`3^(2^j)` (name size `j + 6`), far past the exhaustive range
**[computed]**:

| name | size | log₂ value | chain t | log₂ value / √t | lemma t (reuse) | log₂ value / √t |
|---|---|---|---|---|---|---|
| `2^(2^4)` | 10 | 16 | 9,995 | 0.160 | 2,167 | 0.344 |
| `2^(2^6)` | 12 | 64 | 88,611 | 0.215 | 16,167 | 0.503 |
| `2^(2^8)` | 14 | 256 | 962,235 | 0.261 | 209,479 | 0.559 |
| `2^(2^10)` | 16 | 1,024 | 13,023,555 | 0.284 | 3,193,543 | 0.573 |
| `2^(2^12)` | 18 | 4,096 | 200,716,363 | 0.289 | 50,518,119 | 0.576 |
| `3^(2^4)` | 10 | 25 | 22,300 | 0.170 | 15,301 | 0.205 |
| `3^(2^6)` | 12 | 101 | 1,877,903 | 0.074 | 852,863 | 0.110 |
| `3^(2^8)` | 14 | 406 | 363,260,285 | 0.021 | 49,353,657 | 0.058 |

For powers of two the ratio settles at about 0.29 (chains) and 0.58
(lemma proofs), so `log₂ k ≈ 0.29·√t`. The reason: `2^a · 2^a` only
shifts digits (`D0(x)·y → D0(x·y)`), which costs about `a` lines of size
about `a`. Squaring `L`-digit numbers is therefore `O(L²)`, not the
`O(L³)` of general schoolbook multiplication. Powers of 3 do pay `L³` or
more, so their ratio to `√t` falls. **[observation]**

Bearing on Proposition 2 of the proof-budgets note **[checked for
instances]**: its first binary lower bound, `2^{(t/C)^{1/3}/2}`, used
repeated squaring of 2 with general multiplication (Lemma A3, `O(L³)`).
The toy suggested that using the shape of `bin(2^a)` would give
`2^{c√t}`. Working it out in `PA⁻` gave more. The lemma
`∀w ∀z (Dⁿ(w)·z = Dⁿ(w·z))` for `n = 2^i` follows from the one for
`2^{i−1}` in a fixed number of lines of size `O(n)`, so a squaring of
`2^{2^i}` costs `O(2^i)`, not `O(4^i)`, and the record is `2^{t/C}`. The
same trick gives `t/C` in unary. Both are now Proposition 2 (Lemmas A6
and A7 there), and `proof-budgets/doubling_check.py` writes the proofs
out and checks them line by line. The toy cannot do this: its lemmas are
closed equations, so the `n` doublings inside `Dⁿ` are paid for one at
a time.
---

## 10. Naming by a property

*Added 2026-11-24, second pass.* `exists.py` adds names of the form
`p(x) = c`: `c` is a closed term, and `p` is a term with one occurrence of
a variable `x` that is strictly increasing in `x`. Every operation on the
path to `x` is `S`, `D0`, `D1`, `+`, multiplication by something of value
`≥ 1`, `x^e` with `e ≥ 1`, or `b^x` with `b ≥ 2`. Such a name names the
unique `k` with `p(k) = c`, when there is one. Its size is
`|p| + |c| + 1`.

The proof **guesses** `k` and **checks** it. It gives the lemma proofs
(with reuse) of `p(k) = m` and `c = m`, sharing lemmas, plus the line
`p(k) = c`. Uniqueness ("`p` is increasing") is one fixed lemma per shape
of `p`, and is **not charged**, so these costs are lower bounds for a
real quantified system. The guess costs nothing extra, because the proof
had to write `k` down anyway (Proposition 1 of the proof-budgets note).
That is the toy's version of guess-and-verify. What it adds is the
inverses of the operations: division, roots and logarithms, which the
term language lacks.

**Exhaustive result, names of size `≤ 11`.** **[computed]** 589,180
property names have a solution, naming 312 different numbers. **None of
them is cheaper than the best term name or numeral for its number.** A
property name spends 2 symbols on `x` and `=`, and 4 or more once
the pattern does anything. At these sizes that overhead is never
recovered.

**Two families beyond the exhaustive range.** **[computed;
comparison with term names not exhaustive]**

| number | property name | name size | proof | `D` | numeral `D` |
|---|---|---|---|---|---|
| `(4^8 − 1)/3` (15 bits) | `S(x·3) = 4^8` | 17 | 5,701 | 29.5 | 20.0 |
| `(4^16 − 1)/3` (31 bits) | `S(x·3) = 4^16` | 18 | 17,714 | 32.1 | 37.0 |
| `(4^32 − 1)/3` (63 bits) | `S(x·3) = 4^32` | 19 | 61,559 | 34.9 | 70.0 |
| `(4^64 − 1)/3` (127 bits) | `S(x·3) = 4^64` | 20 | 228,964 | 37.8 | 135.0 |
| `(3^24 − 1)/2` (38 bits) | `S(x·2) = 3^24` | 17 | 73,873 | 33.2 | 44.3 |
| `(3^64 − 1)/2` (101 bits) | `S(x·2) = 3^64` | 19 | 932,851 | 38.8 | 108.7 |

From about 30 bits on, these property names beat the numeral by a wide
margin. We know no term name that comes close. `(4^j − 1)/3` is
`0101…01` in binary, and the best term we know for `j = 64` is the
product of the six factors `2^{2^i} + 1` (`i = 1…6`), of size about 65.
We did not search for terms at these sizes, so we have not shown that no
short term exists. The pattern is what the proof-budgets note
leads one to expect. A checked name is cheap whenever the number is the
answer to an easy-to-check question (here, "what times 3, plus one, is
`4^j`?") but is not the value of a short calculation in the term
language. The toy cannot go further and show that such a gap is
*necessary*, which is the hard part (§6).

---

## 11. Reproducing

From `large-numbers/naming-records/` (Python 3, no packages):

    python3 naming_records.py U 12 10000000 8 500   # ~15 s
    python3 naming_records.py B 10 10000000 6 200   # ~20 s
    python3 analyse.py U > tables_U.md
    python3 analyse.py B > tables_B.md
    python3 check_strategy.py                        # step-by-step check of the evaluation-proof lengths
    python3 check_frontier.py B 1100                 # shortest proofs of the record holders (minutes)

`naming_records.py` writes `out_U.json` and `out_B.json` (one row per
name: size, value, proof length, steps, the term and its reading; not
committed, 40 MB and 120 MB). `check_strategy.py` re-derives the
evaluation-proof length of 10,000 random names by rewriting them one step
at a time and found no mismatch.

Second pass (§8–§10):

    python3 lemma_run.py U 12 10000000; python3 lemma_run.py B 10 10000000   # lemma proofs, all rows
    python3 analyse.py UL > tables_UL.md; python3 analyse.py BL > tables_BL.md
    python3 big_run.py U 14 10000000     # ~30 min, 2 GB: chain and lemma tables at size 14
    python3 big_run.py B 11 10000000     # ~6 min
    for x in U14 U14L B11 B11L; do python3 analyse.py $x > tables_$x.md; done
    python3 check_lemmas.py              # line-by-line check of 3,000 lemma proofs
    python3 towers.py; python3 growth_families.py      # §8 and §9 tables (growth_families ~40 min)
    python3 exists.py 11 10000000; python3 compare_exists.py out_BE11.json out_B11L.json
    python3 exists_families.py           # §10 table

Saved outputs: `towers.md`, `growth_families.md`, `exists_results.md`.
