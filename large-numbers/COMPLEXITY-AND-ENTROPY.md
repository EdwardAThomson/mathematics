# Complexity, entropy and the ladder

*Written 2026-11-24. A companion to `THE-LADDER.md` and
`BOOLOS-IS-BUSY-BEAVER-CLASS.md`. It answers the question: do our results
about large numbers say anything about bounds on complexity, about entropy
in Shannon's sense, or about hierarchies of complexity classes?*

Short answer: yes, and the link is tight. "The largest number you can name
in n symbols" and "the fewest symbols needed to name a given number" are
the same relationship read in two directions. The second one is
**description complexity**, the subject Kolmogorov, Solomonoff and Chaitin
founded in the 1960s. So every result in this project is also a statement
about description complexity, and the ladder of big-number schemes is also
a ladder of complexity measures.

Each claim carries a tag, as in `THE-LADDER.md`:

- **[Lean]** machine-checked in this repository;
- **[paper]** argued here or in a sibling note, not machine-checked;
- **[classical]** a standard textbook result (the reference to check is
  Li and Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*), not re-proved here;
- **[analogy]** a structural resemblance, not a theorem.

Nothing in §§1 to 5 has been checked against the literature for priority.
Most of it is certainly classical in spirit. §7 says what might be ours.

---

## 1. Two views of one thing

Fix a rulebook: a notion of "description" with a size, and a notion of
"this description names the number k". Two functions come with it.

- **Biggest number**: `Big(n)` = the largest number named by a description
  of size at most n. This is what the project has studied all along.
- **Description complexity**: `D(k)` = the size of the smallest description
  naming k.

They determine each other:

    Big(n) = the largest k with D(k) ≤ n.

For Turing machines or programs, `D` is **Kolmogorov complexity** `K`, and
`Big` is a Busy Beaver function. For our provability scheme, a description
is a formula φ of arithmetic, its size is `fSize φ`, and "names k" means
that PA proves `∀x (φ(x) ↔ x = k)`. Call the resulting complexity `D_PA`.
Then `BoolosBig_PA(n)` is exactly the largest k with `D_PA(k) ≤ n`.

So a large-number contest is a hunt for the numbers that are both enormous
and extremely cheap to describe.

## 2. What our theorems say in this language

**(a) Computable functions cannot raise complexity by more than a
logarithm. [Lean]** For every computable f there is a constant C with

    D_PA(f(n)) ≤ C + 6·log₂ n      for all n.

This is `logName_names` with `fSize_logName_le` in `RayoBoolos/Binary.lean`.
The headline `BoolosBig_PA_log_bound` is the same fact read the other way.
It is the provability counterpart of the textbook inequality
`K(f(n)) ≤ K(n) + C_f`. In words: if you can compute something from n, its
description costs no more than a description of n plus a fixed overhead,
and n itself costs about log n symbols because you can write it in binary.

**(b) Provability complexity and Kolmogorov complexity are the same
measure up to a modest factor. [first inequality Lean, second paper]** This
is the Busy Beaver sandwich
(Theorems 2 and 3 of the Busy Beaver note) restated:

    D_T(k) ≤ c·K(k) + c           and           K(k) ≤ c·D_T(k)·log D_T(k) + c_T.

The first holds because "the output of program p" is a formula about
`|p|` symbols long whose value PA can confirm once p has halted. The
second holds because a machine given φ can search through T's proofs
until it finds the number φ names. The `log` factor is the cost of writing
variable names in bits. The theory T enters only through the constant
`c_T`. This is the precise sense in which the choice of axioms does not
matter. The first inequality is machine-checked in the form
`BoolosBigIn_partrec_bound` (`RayoBoolos/BusyBeaver.lean`): if program
number e halts with output v, then every consistent theory containing `𝗣𝗔⁻`
names v within `C + 6·log₂ e` symbols, with one C for all theories.

**(c) Almost every number is incompressible. [paper, by counting]** There
are at most `2^(c·n·log n)` formulas of size n, so at most that many
numbers have `D_PA(k) ≤ n`. Among the numbers with m binary digits, all
but a vanishing fraction need on the order of `m / log m` symbols or more.
A typical number costs about as much to describe as to write out.

Put (a) and (c) together and you get the right picture of the landscape:
ordinary numbers sit at "complexity ≈ number of digits", and the numbers
this project cares about are the rare extreme outliers on the other side,
with astronomically many digits and tiny complexity. `Big(n)` is the single
most extreme outlier at each budget.

**(d) The complexity measure is not computable. [Lean, in the Big form]**
`BoolosBig_PA_not_computable` says `Big` is not computable. Equivalently
there is no algorithm computing `D_PA`, or even any computable lower bound
on it that grows without limit **[paper]**, just as for `K`
**[classical]**.

## 3. Bounds on what a theory can know: Chaitin's theorem

The "no top" argument of `THE-LADDER.md` §3 uses Berry's paradox ("the
smallest number not nameable in under twenty words"). Chaitin turned the
same paradox into a hard bound on complexity:

> **Chaitin's incompleteness theorem. [classical]** For every consistent
> theory T (that can be listed by a machine and includes basic arithmetic)
> there is a constant `L_T` such that T cannot prove `K(k) > L_T` for any
> specific number k, although this is true for all but finitely many k.

So a theory can certify that numbers are simple, but it cannot certify
that any particular number is more complex than a fixed threshold, and that
threshold is roughly the description length of the theory itself. Our
Claim A (**[Lean]**, `Rayo/NoTop.lean`) is the same argument with the
theory stripped away: a scheme cannot name "one more than my own record at
budget n" within budget n.

Three consequences for our function.

1. **T can only ever prove lower bounds on its own record. [paper]** The
   statement "`BoolosBig_T(n) = k`" includes the claim that some sentence
   is *not* provable in T. A consistent T can never prove that anything is
   unprovable in T, since that would prove its own consistency, which
   Gödel's second theorem forbids. So PA proves `BoolosBig_PA(n) ≥ k` for
   every true such bound, and proves the exact value for no n ≥ 1. The
   function is defined by what PA can prove, yet PA cannot determine a
   single value of it. (This short argument is ours as far as this
   repository goes. It needs a literature check.)

2. **Each value carries about n bits of unobtainable information.
   [classical, transferred by (b)]** Knowing the Busy Beaver number for
   size n lets you decide the halting problem for every program up to that
   size: run each one for that many steps. That is about n bits of
   information that no algorithm can produce, and it is the same
   information as the first n bits of Chaitin's halting probability Ω, up
   to a logarithmic slack. By the sandwich, the same holds for
   `BoolosBig_T(n)` after rescaling n.

3. **Stronger theories know more values, but only finitely many.
   [classical]** For each T there is a size beyond which T cannot settle
   the value of the ordinary Busy Beaver function. For ZF the published
   bound is 748 states (O'Rear, reported in Aaronson 2020), with smaller
   figures reported as pending verification. Strengthening the axioms pushes the
   threshold up by roughly the number of bits of new axioms, and never
   removes it.

This is the honest form of "bounds on complexity" that our work supports:
*a rulebook of description length κ can certify at most about κ bits'
worth of complexity, and can settle its own Busy Beaver function only up to
a budget of about κ.* The project's κ(R), the cost of the rulebook, is
exactly this quantity.

## 4. Shannon entropy

Shannon's entropy `H = −Σ p·log₂ p` and Kolmogorov's complexity `K` both
measure information in bits, but of different things.

- **Shannon** measures a *source*: a probability distribution over
  messages. H is the average number of bits per message that the best
  possible code needs. It says nothing about any one message.
- **Kolmogorov** measures a *single object*: the length of its shortest
  description. No probabilities are involved.

They agree on average. **[classical]** For any distribution P that a
program can compute, the average of `K(x)` over x drawn from P equals
`H(P)` up to a constant that depends only on the program for P. Shannon
entropy is the expected Kolmogorov complexity.

What this says about large numbers:

1. **Size and information are different quantities.** A number with a
   million digits chosen by coin flips has about 3.3 million bits of
   information. `BoolosBig_PA(100)` has more digits than there are atoms
   in any universe you care to name, and at most about 100 symbols of
   information. Its information per digit is zero for every practical
   purpose. Large-number schemes maximise *size per bit*, the opposite of
   what a good compressor's output looks like.

2. **Big nameable numbers are overwhelmingly "likely" under the natural
   prior on descriptions. [classical]** If you pick a program by flipping
   coins, the chance that it prints k is about `2^(−K(k))`. For a typical
   number that is about `1/k`. For the Busy Beaver number of size n it is
   about `2^(−n)`, which is inconceivably larger than one over the number
   itself. Solomonoff's theory of prediction is built on this prior.

3. **The cost of changing rulebook is a bounded number of bits, inside a
   rung. [classical + paper]** The invariance theorem says two universal
   programming languages assign complexities that differ by at most a
   constant: the length of an interpreter for one written in the other.
   Our result (b) extends that across the gap between programs and proofs,
   at the price of a logarithmic factor. This is why everything on one
   rung of the ladder (Turing machines, lambda calculus, provable naming
   in any reasonable theory) produces the same growth: within a rung, a
   change of rulebook is worth a fixed number of bits.

4. **Between rungs there is no exchange rate. [classical]** No constant,
   and no computable function, converts a description that uses a halting
   oracle into one that does not. That failure of the invariance theorem
   is what a rung *is*. In entropy terms: moving up a rung is not buying
   more bits, it is changing what a bit is allowed to refer to.

There is also a time dimension that neither H nor K sees. A Busy Beaver
number has a short description that takes unimaginably long to unpack.
Bennett called this **logical depth**. Large numbers of this kind are the
deepest objects there are at their description length. **[classical, as a
remark]**

*Follow-up: `NAMING-DEPTH.md` defines the proof-length version of depth for
naming. It also qualifies the remark above: it holds for absolute depth,
while depth relative to the length of the number is a separate question,
and some enormous numbers are shallow in that sense.*

## 5. Hierarchies

There are three different hierarchies in play, and it helps to keep them
apart.

### 5.1 Inside the computable: the fast-growing hierarchy

Computable functions are themselves stratified by how fast they grow, and
the levels are indexed by ordinals: elementary functions, primitive
recursive functions (below ω), multiply recursive functions (below ω^ω),
and so on. **[classical]** The functions PA can *prove* always halt are
exactly those below level ε₀.

This is where ε₀ honestly belongs in the project, and it explains the
earlier mislabelling. ε₀ measures **what PA can prove total**, which is a
question about all inputs at once. `BoolosBig_PA` asks **what PA can pin
down one value at a time**, and that needs no proof of totality, only a
finished computation to point at. Hence the jump from ε₀ to Busy Beaver
class. **[Lean for the jump; classical for the ε₀ characterisation]**

This hierarchy is rung 0 of the ladder seen under a microscope.

### 5.2 Beyond the computable: the arithmetical hierarchy and upward

Above the computable, problems are classified by how many alternating
"for all / there exists" quantifiers over numbers are needed to state
them. One "there exists" gives the halting problem. Each further
alternation gives a strictly harder class, and each corresponds to adding
one more halting oracle. **[classical]** Beyond all finite levels come
arithmetic truth, then the hyperarithmetic and analytical hierarchies
(quantifiers over sets of numbers), and eventually truth in set theory.

The ladder of `THE-LADDER.md` *is* this hierarchy, read through the
"largest number in n symbols" lens:

| rung | allowed to refer to | complexity measure | Big(n) |
|---|---|---|---|
| 0 | a fixed terminating process | resource-bounded complexity | a computable function |
| 1 | halting, or provability | K, or D_T | Busy Beaver |
| k | halting with k−1 nested oracles | K relative to the (k−1)-th halting problem | k-th order Busy Beaver |
| ω | all arithmetic truth | K relative to arithmetic truth | beats every rung k |
| … | truth for richer languages | relativised likewise | … |
| Rayo | truth in set theory | definability complexity in set theory | Rayo's function |

Rows 0 and 1 are partly **[Lean]**, as detailed in `THE-LADDER.md`. The rows
below are **[classical]** or **[expected]** exactly as tagged there. The
third column is the new reading: *each rung of the ladder is Kolmogorov
complexity relative to a stronger oracle.*

### 5.3 Complexity classes: P, NP and the polynomial hierarchy

*Follow-up: `PROOF-BUDGETS-AND-COMPLEXITY.md` works this section out in
detail (proof-length budgets, the ε₀ rung, `Kt`/`KNt`, bounded
quantifiers).*

The classes of practical complexity theory are a scaled-down copy of
§5.2. **[analogy]** Take the arithmetical hierarchy and require every
quantified object to be short (polynomial length) and every check to be
fast (polynomial time). One "there exists" gives NP. Alternations give the
polynomial hierarchy. The diagonal argument behind our "no top" result is
the same one that proves the **time hierarchy theorem**: more running time
strictly increases what can be computed. **[classical]**

The analogy stops at an important place. In the unbounded world every
level is provably distinct from the next. In the polynomial world nobody
can prove that even the first two levels differ: that is the P versus NP
problem. Diagonalisation alone provably cannot settle it. **[classical:
Baker, Gill and Solovay]**

So our results say nothing directly about P versus NP, and it would be
wrong to suggest they do. What they share is the method and the shape: a
ladder generated by "add one more quantifier", with a Berry-style argument
separating levels wherever the levels are generous enough for it to work.

One accurate bridge does exist. Any bound of the form "this takes at most
t(n) steps" with t computable defines a complexity class. Busy Beaver
growth is the boundary of all of them together: a function is computable
exactly when some computable time bound suffices, and Busy Beaver
eventually exceeds every such bound. `BoolosBig_PA_dominates_computable`
**[Lean]** therefore places our function strictly above the union of all
time-complexity classes.

## 6. The bounds in one place

| statement | status |
|---|---|
| `D_PA(f(n)) ≤ C_f + 6·log₂ n` for every computable f | [Lean] |
| `Big` for provable naming exceeds every computable function and is not computable | [Lean] |
| A scheme cannot name its own record plus one within budget | [Lean] |
| Outputs of halting programs are nameable in `C + 6·log₂(program number)` symbols, same C for every consistent T ⊇ 𝗣𝗔⁻ | [Lean] |
| Conversely a proof-search program recovers k from the formula naming it (`exists_search`) | [Lean] |
| Quantitatively `K(k) ≤ c·D_T(k)·log D_T(k) + c_T` | [paper] |
| At most `2^(c·n·log n)` numbers have `D_PA ≤ n`; typical numbers are incompressible | [paper] |
| T proves lower bounds on `BoolosBig_T(n)` but never an exact value | [paper] |
| T cannot prove `K(k) > L_T` for any k | [classical] |
| Expected K equals Shannon entropy up to a constant | [classical] |
| Each rung is K relative to a stronger oracle, with no exchange rate between rungs | [classical] |
| Any consequence for P versus NP | none claimed |

## 7. What might be ours, and what to check

Everything tagged [classical] is textbook material. The candidates for
something of our own are narrow:

1. the machine-checked statements themselves, in particular the
   logarithmic bound for a *provability* complexity measure with explicit
   constants;
2. the observation that naming, unlike proving totality, makes theory
   strength disappear into a constant (§5.1), with the ε₀ correction as a
   worked example of how easy the two are to confuse;
3. the remark in §3.1 that a theory proves no exact value of its own
   provable-naming record;
4. the presentation of the Busy Beaver to Rayo ladder as one family of
   relativised complexity measures priced by rulebook cost.

A first literature search is in `LITERATURE-SURVEY.md` (2026-11-24): items
1 and 4 are ours as artifact and arrangement, item 2 is apparently unstated
folklore, item 3 is an immediate corollary of Gödel II that we found nowhere
applied to this function. It started from: Chaitin's papers on incompleteness and
Ω; Boolos, "A new proof of the Gödel incompleteness theorem" (1989);
Li and Vitányi's book; Aaronson's survey "The Busy Beaver Frontier"; and
the Googology community's write-ups of Rayo's function and its variants.
