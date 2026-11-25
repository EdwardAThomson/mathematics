# Is CalcName_2 hard? A barrier, a failed gadget, and some counts

*Written 2026-11-24. Step 3 of the plan in `POLYLOG-NAMING-LADDER.md`
§4.2 and §7. Question: is `CalcName_2` (does `k` have a name of at most
`(log N)²` symbols in the binary toy arithmetic B, with an evaluation
proof of at most `m` symbols?) in P, or hard for `β_2`? Time-boxed. Three
pieces: a barrier, the partial version under randomized reductions, and
a computation. Code in `calcname2/`.*

Tags as elsewhere: **[classical]** known result, cited; **[paper]**
argued in full here; **[sketch]**; **[computed]** produced by the
scripts here; **[observation]** a pattern in computed data, not proved;
**[open]**.

Notation follows `POLYLOG-NAMING-LADDER.md`. `N` is the length of a
`CalcName` instance `(k, s, 1^m)`. For a number `k` and a budget `m`,

    K_B^m(k) = least size of a closed B-term whose evaluation proof
               has at most m symbols and ends in the numeral for k

(`∞` if there is none). So `(k, s, 1^m)` is a yes-instance iff
`K_B^m(k) ≤ s`.

---

## 0. The answer in plain language

**The question is still open.** Each of the three pieces gave a definite
result, though none settles it.

1. **Barrier (proved).** Suppose someone proves that `CalcName_2` is
   hard for `β_2` with an ordinary deterministic reduction of the
   "natural" kind, one where the size limit and the budget it asks about
   depend only on the input length. Then one of two things follows.
   Either `P = β_2`, which would refute the exponential time hypothesis.
   Or there is a fast, explicit recipe that prints numbers which have no
   name in B shorter than every constant multiple of `log N`. The second
   would be a new kind of lower bound for arithmetic. As far as we can
   find, nobody can prove even a modest lower bound like that for any
   explicit sequence of numbers. (For the closely related straight-line
   complexity `τ`, nothing beyond the trivial `log log k` is known for
   explicit numbers.) So a simple hardness proof would prove something
   people have long been unable to prove. This is the Kabanets–Cai
   barrier for circuit minimisation (MCSP), transferred to naming.
   **[paper]**

   *Added 2026-11-25:* the "natural" condition can be dropped (§1.4,
   following Murray and Williams). Any ordinary deterministic proof of
   hardness would give one of two lower bounds that nobody can currently
   prove. One is a lower bound on names for numbers that can be printed
   in exponential time. The other says that deterministic time cannot be
   traded for a short burst of guessing. The one condition is that the
   reduction must not set the calculation budget so tight that it rules
   out the short names. **[paper]**

   *Literature check (§5):* we still found no explicit lower bounds of
   this kind. Even the simplest neighbouring problem, the fewest 1s
   needed to write `n` with `+` and `×`, is neither known to be hard nor
   known to be easy. For the circuit version with small thresholds,
   "hardness magnification" results say that proving it *not* easy would
   also be a breakthrough. So both directions of our question probably
   meet known walls.

2. **Partial version (attempted, did not work).** We defined the
   "agree on given bits" version and built an arithmetic gadget: the cube
   of a well-chosen sum of powers of two. Its binary digits check every
   clause of a 3-SAT formula. The gadget is *complete*: a satisfying
   assignment always gives a short name that fits the pattern. Checked by
   computer on 11 random formulas, for every assignment. But the gadget
   is *not sound*. One concrete number, which encodes no assignment at
   all, fits every pattern, and its name is only 4 to 7 symbols longer
   than the honest names. Randomness does not obviously help either. Any
   random choice that the honest name has to know fits inside the name,
   so a cheating name can use it too. Hirahara's method relies on names
   that are polynomially long, so it does not carry over directly.
   **[paper for the gadget; computed checks; the obstacle is an
   observation]**

3. **Counting (computed).** We listed every number below `2^64` that has
   a B-name of at most 21 symbols. There are 9.6 million of them. Each
   extra symbol multiplies the count by about 2.3, so `s` symbols give
   about `2^{1.2 s}` numbers, well below the crude bound `7^s`. At the
   budget `s = (log₂ n)²` the count for `n`-bit numbers is about
   `2^{1.2 (log n)²}`. That is more than polynomial in `n` (so listing all
   short names is not a polynomial algorithm) but a vanishing fraction of
   all `n`-bit numbers. As names get longer, more numbers *need* a genuine
   sum or product of two large parts. The share that need `+` goes from 0
   at size 13 to 4% at size 19, and the share that need `*` from 0.3% to
   17%. We found no sign that names can be "peeled" one small piece at a
   time, which is what a simple polynomial algorithm would need.
   **[computed; trends are observations at a small scale]**

**Bottom line.** Hardness for `β_2` would need a non-natural or
randomized reduction, and the obvious randomized gadget fails for a
reason we can name. Membership in P has no support either: the data
shows the hard cases (genuine sums and products) becoming more common.
Our guess is that `CalcName_2` is neither in P nor provably `β_2`-hard
with current techniques, like MCSP. That remains a guess.

---

## 1. Piece 1: a barrier for deterministic hardness

### 1.1 The statement

A polynomial-time reduction `R` from `CSAT_2` to `CalcName_2` is
**natural** if the size bound `s`, the budget `m` and the length `N` of
`R(x) = (k, s, 1^m)` depend only on `|x|`. Write them `s(n)`, `m(n)`,
`N(n)`. (Kabanets and Cai call MCSP reductions natural when the size
parameter depends only on the input length. Requiring the same of `m`
and `N` is a mild extra. A reduction can usually be padded to make `N`
depend on `|x|` alone.)

We encode `CSAT_2` so that every input length `n` has an easy
no-instance `z_n`: the constant-0 circuit on `⌊(log n)²⌋` inputs, padded to
length `n`. `z_n` is computable from `1^n` in time `poly(n)`.

**Theorem A. [paper]** Suppose `CSAT_2` reduces to `CalcName_2` by a
natural deterministic polynomial-time reduction. Then at least one of
the following holds:

(i) `β_2 = P`. Under ETH this is false (`POLYLOG-NAMING-LADDER.md`,
Proposition 1).

(ii) There is a sequence of numbers `k_n`, printed from `1^n` in time
`poly(n)`, with `N(n) = poly(n)` bits and a polynomial budget `m(n)`, such
that for every constant `c`,

    K_B^{m(n)}(k_n) > c · log N(n)   for infinitely many n.

*Proof.* Let `R` run in time `n^a`.

*Case 1: for some `c`, `s(n) ≤ c·log N(n)` for all large `n`.* Then every
output of `R` is an instance of `CalcName` with `s ≤ c·log N`, which is
decidable in polynomial time by enumerating fewer than `7^{s+1}`
candidate names and checking each (Proposition 3(a) of the ladder note).
So `CSAT_2 ∈ P`, and since `CSAT_2` is `β_2`-complete, `β_2 = P`. That
is (i).

*Case 2: for every `c` there are infinitely many `n` with
`s(n) > c·log N(n)`.* Let `k_n` be the number in `R(z_n)`. Since `z_n` is
a no-instance, `R(z_n)` is a no-instance: `K_B^{m(n)}(k_n) > s(n)`. For
each `c` the infinitely many `n` of Case 2 satisfy
`K_B^{m(n)}(k_n) > s(n) > c·log N(n)`. And `k_n` is computed from `1^n` by
writing `z_n` and running `R`, in time `poly(n)`. That is (ii). ∎

**Corollary A′.** Under ETH, a natural deterministic reduction showing
`CalcName_2` is `β_2`-hard would give (ii). The same argument works for
`CalcName_j` and `CSAT_j` for every `j ≥ 2`. It also works for the
partial version of §2: an explicit partial pattern that no short name
fits is at least as strong as an explicit number with no short name.
**[paper]**

### 1.2 Why (ii) would be new

What is easy. For each *fixed* `c`, there are poly-time constructible
numbers with `K_B^m(k) > c·log N`. List all names of size at most
`c·log N` (there are `N^{O(c)}` of them), evaluate each within budget
`m`, and output the least `N`-bit number not hit. With
`s = (log N)²`, the same search takes quasi-polynomial time. So (ii) is
the first step that brute force cannot reach: it asks for one
polynomial-time recipe that beats *every* constant `c` infinitely often.
**[paper]**

What is known about explicit hard numbers. The closest classical measure
is the straight-line complexity `τ(k)`: the fewest `+, −, ×` steps that
compute `k` from 1. Trivially `τ(k) ≥ log₂ log₂ k + 1`, and this is tight
for `2^{2^r}`. Counting shows that most integers have `τ(k)` above every
polynomial in `log log k`. But for explicit sequences such as `n!`,
"there are few results which strengthen the general bounds" (Markström
2013, introduction). The Shub–Smale `τ`-conjecture, that `τ(m·n!)` is not
polylogarithmic in `n`, is open and would imply `P ≠ NP` over the complex
numbers. **[classical]**

Translating: `n` here is about `log N`, and statement (ii) asks for
explicit numbers whose B-complexity exceeds every `c·log N`. That is the
integer analogue of a superlinear circuit lower bound for a function in
E, which is also open. B is not the same model as `τ`. It uses formulas
rather than circuits, it has no subtraction, and it has `^` and binary
digits as primitives. Its time budget `m` caps every intermediate value
below `2^m`. Formulas and the time cap make lower bounds easier in
principle. So we cannot say (ii) is equivalent to a known open problem.
We have not found it proved anywhere, and the `τ` literature suggests it
is beyond current methods. **[observation about the literature]**

### 1.3 What the barrier does not cover

- **Non-natural deterministic reductions.** If `s` may depend on `x`,
  the reduction can choose a tiny `s` on no-instances, and Case 2 gives
  nothing. §1.4 handles all deterministic reductions with the
  Murray–Williams argument, with a weaker conclusion and one caveat on the
  budget `m`.
- **Randomized reductions.** The barrier says nothing about them. That
  is why §2 tries them.
- **The oracle barrier does not apply.** For `MINKT`, Ko (1991) gives an
  oracle relative to which `MINKT` is not NP-hard, so a hardness proof
  must be non-relativizing. The natural oracle version of `CalcName` is
  `OracleName` (B plus a circuit symbol from the input), and that *is*
  `β_j`-complete (ladder note, Theorem 4). So relativization is not an
  obstacle here. Only the Kabanets–Cai barrier is. **[paper, simple]**

**Contrast with `MINKT`.** For time-bounded Kolmogorov complexity the
same argument gives more. `k_n` is printed by a program of `O(log n)`
bits (it contains `n`) in time `T(n) = n^{O(1)}`. So a natural reduction
must use time budgets `t(n) < T(n)`, below its own running time. B is
not universal. A short B-term cannot simulate the reduction, so no such
self-defeating upper bound exists. This is why Theorem A(ii) is a real lower
bound and not a contradiction. **[paper]**

### 1.4 All deterministic reductions: the Murray–Williams analogue

*Added 2026-11-25.* Murray and Williams (CCC 2015, Theorem 1.3 with
Theorem 4.1) show: if MCSP is NP-hard under polynomial-time reductions,
then EXP ≠ NP ∩ P/poly. Their proof pads a NEXP language down into NP,
reduces it to MCSP, and uses EXP ⊆ P/poly to say that every truth table
the reduction prints has small circuits. So a large size parameter
means "yes" automatically, and a small one can be brute-forced. The same
idea works for `CalcName_2` once the padding is scaled to the `β_2`
ladder. **[paper, adapted from Murray–Williams]**

**Classes.** `NGUESS(2^{O(n)}, n²)` is the class of languages `L` with a
verifier `V(x, y)` that runs in time `2^{O(|x|)}` on witnesses of length
`|y| = |x|²`: `x ∈ L ⇔ ∃y V(x, y)`. Brute force puts it in
`DTIME(2^{O(n²)})`.

**Hypothesis `H_B(b, e)`** (`b ≥ 1`, `e ≥ 1`), the analogue of
"E has small circuits". For every function `f` from strings to numbers
that is computable in time `2^{O(n)}` on inputs of length `n`, there is a
constant `C` such that every `f(x)` has a B-name of size at most
`C·|x|^b` whose evaluation proof has at most `|f(x)|^e + C` symbols.
(Here `|f(x)|` is the bit length. `b ≥ 1` is forced: with `f(x) = x`,
counting shows names of size about `|x|/3` are needed.)

**Budget caveat.** Call a reduction to `CalcName` *`e`-generous* if every
output `(k, s, 1^m)` has `m ≥ |k|^e + C` for the `C` above. This holds
automatically for the variant of `CalcName` in which the budget is fixed
at `|k|^e` instead of being part of the input. Without it, a reduction
could squeeze `m` below what the short names of `H_B` need, and the
argument below breaks.

**Theorem B. [paper]** Suppose `CalcName_2` is `β_2`-hard under some
deterministic polynomial-time reduction `R` (natural or not) that is
`e`-generous. Then:

(a) if `H_B(b, e)` holds, `NGUESS(2^{O(n)}, n²) ⊆ DTIME(2^{O(n^b)})`;

(b) consequently, for every `1 ≤ b < c < 2`, at least one of these holds:

  (i) `H_B(b, e)` fails: some family of numbers computable in time
  `2^{O(n)}` from `n`-bit inputs has no B-names of size `O(n^b)` within
  the budget;

  (ii) `DTIME(2^{n^c}) ⊄ NGUESS(2^{O(n)}, n²)`.

*Proof.* (a) Let `L ∈ NGUESS(2^{O(n)}, n²)` with verifier `V`. Pad:
`L' = { x 0 1^{2^{|x|}} : x ∈ L }`. An instance of `L'` has length
`N ≈ 2^n`, its witness has `n² = (log N)²` bits, and `V` runs in time
`2^{O(n)} = poly(N)`. So `L' ∈ β_2`. Compose the padding with `R`. This
gives a map `x ↦ (k_x, s_x, 1^{m_x})`, computable in time `2^{O(n)}`, with
`x ∈ L` iff `K_B^{m_x}(k_x) ≤ s_x`. Also `m_x ≤ 2^{O(n)}`, and
`s_x ≤ (log N')² = O(n²)`, where `N' = poly(N)` is the output length.

Apply `H_B(b, e)` to `f(x) = k_x`, which is computable in time `2^{O(n)}`.
That gives a constant `C`. Decide `L` as follows. On input `x`, compute
`(k_x, s_x, m_x)` in time `2^{O(n)}`.

- If `s_x ≥ C·n^b`: by `H_B`, `k_x` has a name of size
  `≤ C·n^b ≤ s_x` whose evaluation proof has at most `|k_x|^e + C ≤ m_x`
  symbols, the last step by generosity. So the instance is a yes-instance.
  Accept. This is correct because `R` is a reduction.
- If `s_x < C·n^b`: try every name of size `< C·n^b`. There are fewer
  than `7^{C n^b} = 2^{O(n^b)}` of them. Run each evaluation for at most
  `m_x` symbols, which takes time `poly(m_x) = 2^{O(n)}`. Accept iff one of
  them ends in the numeral for `k_x`.

The total time is `2^{O(n)} + 2^{O(n^b)}·2^{O(n)} = 2^{O(n^b)}`, since
`b ≥ 1`. So `L ∈ DTIME(2^{O(n^b)})`.

(b) Suppose both (i) and (ii) fail. By (a),
`DTIME(2^{n^c}) ⊆ NGUESS(2^{O(n)}, n²) ⊆ DTIME(2^{O(n^b)})` with `b < c`.
This contradicts the deterministic time hierarchy theorem. ∎

**What this says.** Murray and Williams turn MCSP-hardness into
"EXP ⊄ NP or EXP ⊄ P/poly". Theorem B is the same shape, one level down:

- (i) is the B-analogue of "E needs circuits bigger than `n^b`". With
  `b = 1` it asks for numbers printable in time `2^{O(n)}` from `n`-bit
  inputs whose B-complexity grows faster than every `C·n`. Measured
  against their bit length `N = 2^{O(n)}`, that is complexity
  `ω(log N)` again, as in Theorem A(ii), but now for a family indexed by
  the input `x` instead of a single number per length. The circuit
  version (E ⊄ SIZE(`C·n`) for every `C`) is open: the best known lower
  bounds for explicit functions are about `3.1n`.
- (ii) is the analogue of "EXP ⊄ NP": deterministic time `2^{n^c}` cannot
  be compressed into `2^{O(n)}`-time verification with `n²` guessed bits.
  We do not know a proof. It holds if P = NP, since then
  `NGUESS(2^{O(n)}, n²) ⊆ NTIME(2^{O(n)}) = DTIME(2^{O(n)})` by padding,
  and the time hierarchy finishes the job.

Part (a) also reads as a fine-grained statement. A deterministic
hardness proof, together with `H_B`, would remove `n²` bits of
nondeterminism in time `2^{O(n^b)}`, much faster than the `2^{n²}` of brute
force. That is a strong algorithmic claim of the "subexponential
algorithms for long witnesses" kind. ETH by itself does not rule it out,
because ETH concerns witnesses about as long as the input, and here the
witness is quadratically longer.

**Comparison with Theorem A.** Theorem A needs naturalness but no budget
caveat. Its conclusion is a single explicit sequence printable in
polynomial time. Theorem B covers every deterministic reduction that is
generous with the budget. Its conclusion is a disjunction of two open
lower bounds, at exponential-time scale. Neither covers randomized
reductions (§2) or deterministic reductions that set `m` tight.
**[paper]**

**Still open after §1.4.** Remove the budget caveat. The difficulty is
that when `m_x` lies between `|k_x|` and `|k_x|^e`, neither "accept" nor
brute force over all `O(n²)`-size names (time `2^{O(n²)}`) is good
enough. Murray and Williams also derive EXP ≠ ZPP. We have not looked
for the corresponding statement.

---

## 2. Piece 2: the partial version and randomized reductions

### 2.1 The problem

> **PartCalcName_j.** Input: a pattern `p ∈ {0, 1, *}^ℓ`, a size bound
> `s ≤ (log N)^j`, a budget `1^m`. Question: is there a B-name of size
> `≤ s`, with evaluation proof `≤ m`, whose value `X` satisfies
> `bit_i(X) = p_i` for every `i` with `p_i ≠ *`? (Bits beyond the length
> of `X` count as 0.)

**Proposition B. [paper]** `PartCalcName_j ∈ β_j`, and
`PartCalcName_1 ∈ P`. *Proof.* As Proposition 3 of the ladder note.
Guess or enumerate the name, evaluate it, and compare bits. ∎

`CalcName_j` is the special case with no `*`, so `PartCalcName_j` is at
least as hard. This is the analogue of MCSP\* and `MINKT*`, which
Hirahara (FOCS 2022) proves NP-hard under randomized reductions.

### 2.2 Why Hirahara's theorem does not transfer directly

In Hirahara's theorem the size threshold is polynomial in the input
length (he notes the hardness needs `s = 2^{Θ(n)}` for truth tables of
length `2^n`). He also notes that small thresholds give `2^{O(s log s)}`
algorithms. Such hardness is "inevitable unless NP can be solved in
randomized sub-exponential time". So his names are long enough to
contain a whole NP witness. Here names have polylog size, and so does
the witness of a `β_2` problem. That does not rule hardness out, since
the target is `β_2` and not NP, but nothing in his construction can be
reused as is. A reduction has to make the *digits of the value of a
polylog-size arithmetic term* do the checking that a circuit of size `n`
does. **[observation]**

A weaker target is enough to say something. A reduction from 3-SAT on
`v` variables, running in time `2^{o(v)}` and producing instances with
`(log N)² ≥ s`, would show `PartCalcName_2 ∉ P` under ETH. Take
`N = 2^{Θ(√(v log v))}`. Names may then have size `Θ(v log v)`, enough to
list the true literals of an assignment. We tried this.

### 2.3 The cube gadget: complete, not sound

Fix a 3-CNF `φ` with `v` variables and `r` clauses, and a block width
`L` (8 is enough). Choose positions: a constant `c`, one constant `g_i`
per variable, and for each variable two literal positions `a_i⁺` (for
`y_i`) and `a_i⁻ = a_i⁺ + 2(g_i − c)` (for `¬y_i`). For an assignment
`y` let

    K   = 2^{Lc} + Σ_i 2^{L g_i},
    z_y = K + Σ_i 2^{L a_i^{y_i}},        τ_y = z_y³.

Writing `z_y` as a sum of terms `2^e` (each of size `5 + log₂ e`), `τ_y`
has size `O(v log v)`. Its value is evaluated within a budget polynomial
in its length. Expanding the cube, block `e` (bits `Le … Le+L−1`) holds
the number of ordered triples of support positions summing to `e`, as
long as no block overflows.

The pattern `p` checks three kinds of blocks:

- block `3c` must be 1;
- for each variable, block `2g_i + a_i⁺ = 2c + a_i⁻` must be 3. It
  receives `3·[y_i chosen] + 3·[¬y_i chosen]`, so it forces exactly one
  literal per variable;
- for each clause, the block at the sum of the positions of its three
  *falsifying* literals must be 0. It receives
  `6·(product of those three indicators)`.

**Lemma C (completeness). [paper; checked by computer]** If the positions
are chosen so that each checked block receives exactly the intended
ordered triples (random positions in a range `poly(v)` do this after a
few tries), then `τ_y` matches `p` iff `y` satisfies `φ`. In particular,
if `φ` is satisfiable then `(p, s, m)` is a yes-instance with
`s = max_y |τ_y| = O(v log v)`.

*Check.* `calcname2/cube_gadget.py` builds the positions, then for every
assignment `y` compares "`τ_y` matches `p`" with "`y` satisfies `φ`". It
does this for 11 random formulas with `v = 5, 6, 8, 10` and `r ≈ 4.3v`
clauses. All agree. **[computed]**

**Observation D (unsound). [paper; computed]** The number

    X = K³ + 3·Σ_i 2^{L(2g_i + a_i⁺)}

matches `p` for every `φ`, satisfiable or not. It has the constant block
right, puts 3 in every well-formedness block, and has nothing at all in
the clause blocks. Its name is `K³ + 3·Σ_i 2^{…}`, which in the runs is 4
to 7 symbols longer than the honest names (e.g. 289 against 283–284 for
`v = 6`). So with any budget `s` a few symbols above the honest size, the
reduction maps unsatisfiable formulas to yes-instances. With `s` set
exactly at the honest size, this cheater is excluded, but soundness
would need a proof that *no* B-term of that size other than the `τ_y`
fits the pattern. That is a sharp lower bound of exactly the kind §1
says we cannot prove. **[computed for the sizes; the conclusion is
paper]**

**Why the cube cannot be repaired by itself.** In `z³`, each ordered
triple of support positions contributes to exactly one block. A clause
check must see its forbidden product *alone*, so the most it can demand
is "this block is 0". A number that leaves out the assignment part
passes every such check. To force a cheater to contain the products, a
check would need a block whose target value is the same for every
satisfying assignment but is only reachable through products. An example
is the sum of the seven satisfying sign patterns of a clause, which is
always 6. But that block would have to share monomials with the
forbidden-product block, and in a single cube every monomial lands in
only one block. **[paper, for gadgets of the form "cube of a sparse
sum"]**

**Why randomness does not obviously help.** In a randomized reduction,
the honest name for a yes-instance can depend on the random choices only
through at most `s` symbols. So every random choice it needs is
available to a cheating name of the same size. Randomness can rule out
*generic* cheaters by a union bound over the `2^{O(s)}` names. It cannot
rule out structured cheaters like `X` above, which are built from the
same public positions. Soundness has to come from the arithmetic.
**[observation]**

**Status.** `PartCalcName_2`: in `β_2`. Not shown `β_2`-hard, and not
shown outside P under ETH. **[open]** Ideas not tried within the time
box: products of several different sparse sums (so that a monomial can
feed several checks), and names that also contain `φ` itself (the
budget `Θ(v log v)` is large enough to list the clauses).

---

## 3. Piece 3: counting short names in B

`calcname2/count_small_names.py` computes, by dynamic programming over
values, the least name size `K(k)` of every `k < 2^W` with `K(k) ≤ SMAX`.
Only names whose subterm values all stay below `2^W` count. This stands
in for the budget `m`, since every value met during the evaluation is
written as a numeral in the proof. With `W = 64` and `SMAX = 21`, the run
takes 36 seconds and finds 9,619,153 values. Full tables are in
`calcname2/small_names_tables.md` and `calcname2/counts_W64_S21.txt`.
**[computed]**

**Growth.** The number of values with least size exactly `s` grows by a
factor that settles at about 2.29–2.30 per symbol for `s = 15 … 21`
(37,286 at `s = 15`, 5,422,973 at `s = 21`). That is about `2^{1.2 s}`,
against the crude bound `7^s = 2^{2.8 s}` from counting strings. Most
strings of symbols name the same numbers as shorter ones.
**[computed; the rate is an observation]**

**At the budget `s = (log₂ n)²`.** Number of `n`-bit numbers with
`K(k) ≤ ⌊(log₂ n)²⌋` **[computed]**:

| n | s | count | log₂ count | fraction of n-bit numbers |
|---|---|---|---|---|
| 12 | 12 | 193 | 7.6 | 9.4% |
| 16 | 16 | 4,590 | 12.2 | 14% |
| 20 | 18 | 23,862 | 14.5 | 4.6% |
| 22 | 19 | 54,003 | 15.7 | 2.6% |
| 24 | 21 | 282,083 | 18.1 | 3.4% |

(For `n ≤ 10` the bound `(log n)²` exceeds the numeral size, so every
number counts.) The regime that matters, `s ≪ n`, starts only around
`n ≈ 2^{8}` (where `(log n)² = 64`), far beyond what can be enumerated.
So these numbers show the start of the trend and not the asymptotics.
Extrapolating the growth rate, the count is about `2^{1.2(log n)²}`. That
is quasi-polynomial in `n`: listing every short name is not a polynomial
algorithm, which agrees with the ladder note.

**What least names need.** We reran the count with some binary symbols
removed, and separately with `+` and `*` allowed only when one argument
is small. Share of values of least size `s` whose least size goes up
**[computed]**:

| restriction | s=13 | 15 | 17 | 19 |
|---|---|---|---|---|
| no `+` | 0.0% | 0.7% | 2.4% | 4.1% |
| no `*` | 0.3% | 2.8% | 8.7% | 17.1% |
| `^` only (no `+`, no `*`) | 0.3% | 3.5% | 11.1% | 21.4% |
| `+`, `*` only with an argument of size ≤ 6 | 0.0% | 0.0% | 0.3% | 3.1% |

A polynomial algorithm for `CalcName_2` would most naturally "peel" the
target. It would strip binary digits (`D0`, `D1`), subtract 1 (`S`), take
exact roots (`^`), and split off small summands or factors. That works
when every least name is built from one big part and small parts. The
table shows the share of numbers that need a genuine split into two big
parts growing steadily with `s`, with no sign of levelling off. The
`+` splits look like subset sum and the `*` splits like factoring into
two large parts. We read this as weak evidence *against* an easy
algorithm, and nothing more: the sizes are small, and an algorithm could
exploit structure that does not show up in these statistics.
**[observation]**

---

## 4. Summary and what is left

| piece | result | tag |
|---|---|---|
| 1. barrier | natural deterministic `β_2`-hardness ⇒ `P = β_2` or explicit numbers with superlogarithmic B-complexity (Theorem A) | paper |
| 1. all deterministic reductions | Murray–Williams analogue (Theorem B): hardness ⇒ B-lower bound for exponential-time-printable numbers, or `DTIME(2^{n^c}) ⊄ NGUESS(2^{O(n)}, n²)`; needs a generous budget `m ≥ \|k\|^e` | paper |
| 1. oracle barrier | does not apply: the oracle version is complete | paper |
| 2. partial version | in `β_2`; cube gadget complete but unsound (Lemma C, Observation D) | paper + computed |
| 2. randomized hardness | not achieved; randomness cannot hide structure from names | open |
| 3. counts | about `2^{1.2 s}` values of size `s`; need for real splits grows | computed |

**Still open:** is `CalcName_2` in P, or `β_2`-hard? Smaller questions
that came up:

- Theorem B without the budget caveat (reductions that set `m` tight).
- Is a statement like (ii) of Theorem A known, for B or for a nearby
  model (formulas over `+, ×, ^` with numerals)?
- Can a gadget built from several sparse sums make the partial version
  hard under ETH?

---

## 5. Literature check (2026-11-25)

We searched for (a) lower bounds on the arithmetic complexity of
explicit integers, (b) the complexity of finding a shortest arithmetic
expression for a number, and (c) meta-complexity results at small (for
example polylogarithmic) size thresholds. We read the sources below in
part. Nothing we found settles the question, and nothing contradicts the
notes above.

**(a) Explicit lower bounds: still nothing beyond trivial.**

- Saranurak and Jindal, *Subtraction makes computing integers faster*
  (arXiv:1212.2549). Their Theorem 5 says almost every `n`-bit integer
  needs `Θ(n/log n)` steps with or without subtraction, by counting. The
  only explicit separation is a single step: `τ(2^{2^n} − 1) ≤ n + 2`,
  but at least `n + 3` without subtraction (Theorem 24). Whether
  subtraction can ever help superpolynomially is open.
- Markström (arXiv:1306.3091), already cited: for `n!` "there are few
  results which strengthen the general bounds".
- van den Dries and Moschovakis, *Arithmetic complexity* (ACM TOCL 2007),
  prove `log log`-type lower bounds for explicit inputs (Theorems 3.1,
  3.8, 4.1). These bound the number of steps to compute *gcd* from given
  primitives, not the size of a representation of a number.

So Theorem A(ii) and Theorem B(i) still look out of reach. No explicit
sequence of integers is known to need representations of superlogarithmic
size in any of these models (logarithmic in the bit length, i.e.
`ω(log N)`). **[observation about the literature]**

**(b) Finding shortest expressions: open even in the simplest model.**
The closest studied problem is *integer complexity* `‖n‖`: the fewest 1s
needed to write `n` with `+` and `×`. He, *Improved algorithms for
integer complexity* (arXiv:2308.10301), states: "Currently no hardness
results are known for this problem". He also asks whether `‖n‖` can be
computed in time polylogarithmic in `n`. The best single-target
algorithm runs in time `O(n^{0.6154})` (his Theorem 8), which is
exponential in the bit length. So in the simplest neighbouring model,
deciding `‖n‖ ≤ s` is in NP (guess the expression), but it is not known
to be NP-hard or to be in P. That is the same situation as `CalcName`,
one level up the ladder. It supports the guess in §0 that `CalcName_2`
is neither easy nor provably hard with current techniques.
**[classical, cited; the comparison is ours]**

**(c) Barriers and small thresholds for MCSP.** These are cited via the
introduction of Fu, *Hardness of sparse sets and minimal circuit size
problem* (arXiv:2003.00669). We did not read the original papers.

- Hitchcock and Pavan (2015) prove: if MCSP is NP-hard under
  polynomial-time *truth-table* reductions, then EXP ⊄ NP ∩ P/poly. That
  extends Murray–Williams from many-one to truth-table reductions. Our
  Theorem B is many-one only. The same extension for `CalcName_2` is a
  natural next check. **[open]**
- Fu shows that if MCSP is ZPP-hard under polynomial-time truth-table
  reductions, then EXP ≠ ZPP.
- **Hardness magnification.** Oliveira–Santhanam,
  Oliveira–Pich–Santhanam and McKay–Murray–Williams prove that MCSP with
  *small* size thresholds, such as `poly(log n)`, has a striking
  property: even very weak lower bounds against it, for example in
  streaming models, would imply major separations such as P ≠ NP. This is
  the other side of our §1. There, a *hardness* proof for a
  polylog-threshold problem would prove new lower bounds. Magnification
  says that proving such a problem *not easy*, even slightly, would also
  prove new lower bounds. If an analogue holds for `CalcName_2`, then both
  directions of the question are blocked by known barriers. We have not
  checked whether the magnification arguments transfer to B. They use the
  fact that a small-threshold MCSP instance is a long truth table with a
  short description, and `CalcName_2` instances have the same shape.
  **[cited via Fu; the transfer is open]**

**Not found.** We found no study of short arithmetic names with `^` and
binary digits, no study of `CalcName`-type problems with polylog
thresholds, and no Mahaney-type theorem for sets of quasi-polynomial
density inside limited-nondeterminism classes. (`CalcName_2` has only
`2^{O((log N)²)}` yes-instances of each length.)

---

## References

- V. Kabanets and J.-Y. Cai, *Circuit minimization problem*, STOC 2000.
  (Cited via Hirahara 2022 and Murray–Williams; natural reductions.)
- C. D. Murray and R. R. Williams, *On the (non) NP-hardness of
  computing circuit complexity*, CCC 2015; *Theory of Computing* 13
  (2017) article 4. Abstract read (quoted in §1.3); Theorems 1.3 and 4.1 and their proofs read for §1.4.
- S. Hirahara, *NP-hardness of learning programs and partial MCSP*,
  FOCS 2022, ECCC TR22-119. §§1–2 read for the ladder note.
- K. Ko, *On the complexity of learning minimum time-bounded Turing
  machines*, SIAM J. Comput. 20 (1991). (As cited in
  `P-VS-NP-LIMITS.md`.)
- K. Markström, *The straight line complexity of small factorials and
  primorials*, arXiv:1306.3091. Introduction read: bounds on `τ`, few
  results for explicit sequences, and the link to Shub–Smale.
- M. Shub and S. Smale, *On the intractability of Hilbert's
  Nullstellensatz and an algebraic version of "NP ≠ P?"*, Duke Math. J.
  81 (1995). (Cited via Markström; not read.)
- T. Saranurak and G. Jindal, *Subtraction makes computing integers
  faster*, arXiv:1212.2549. Read in full (Theorems 5, 24).
- L. van den Dries and Y. N. Moschovakis, *Arithmetic complexity*, ACM
  Trans. Comput. Logic (2007). Read in part (Theorems 3.1, 3.8, 4.1).
- Q. He, *Improved algorithms for integer complexity*, arXiv:2308.10301.
  Read in full (Theorems 6–8 and the concluding open problems).
- B. Fu, *Hardness of sparse sets and minimal circuit size problem*,
  arXiv:2003.00669 (COCOON 2020). Abstract and introduction read. Source
  for the Hitchcock–Pavan and hardness-magnification citations.
- I. C. Oliveira and R. Santhanam, *Hardness magnification for natural
  problems*, FOCS 2018; D. M. McKay, C. D. Murray and R. R. Williams,
  *Weak lower bounds on resource-bounded compression imply strong
  separations of complexity classes*, STOC 2019. (Cited via Fu; not
  read.)
