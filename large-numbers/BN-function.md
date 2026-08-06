# The Budgeted Number function BN(R, n)

## 1. Motivation

CodeParade's two videos (transcripts in this directory) work through a
sequence of "biggest number in a fixed message length" constructions:
digits, power towers, factorials, Graham's number, a Python program, a
Haskell program, closed lambda terms, Binary Lambda Calculus (BLC), and
finally ordinal-indexed fast-growing hierarchies (Buchholz's ordinal, the
Bashicu Matrix System, Loader's number). At each step the *encoding* gets
more compact, but the underlying question stays the same: given a budget of
$n$ symbols and a fixed set of ground rules, what is the largest number you
can unambiguously specify?

Rayo's number formalizes one endpoint of this (first-order set theory,
symbols instead of bytes), but it is usually presented as a single number,
not as a function of the budget. Busy Beaver is the same idea restricted to
Turing machines, with the budget measured in states rather than symbols.
The goal of this note is to state one function, $BN(R, n)$, that both are
instances of, and to be explicit about a constraint that is present in
spirit in all of these constructions but rarely written down: **the
rule-set $R$ itself must be simple and fixed, independent of $n$, and must
be consistent** — otherwise the budget $n$ is meaningless, because
complexity can be smuggled into $R$ instead of paid for out of the budget.

## 2. Reference systems

A **reference system** is a triple
$$R = (\Sigma, L, \llbracket \cdot \rrbracket)$$
where:

- $\Sigma$ is a finite alphabet (e.g. $\{0,1\}$, ASCII, or the symbols of a
  formal language including quantifiers and set-theoretic connectives).
- $L \subseteq \Sigma^{*}$ is the language of *syntactically legal*
  expressions (well-formed programs, well-formed formulas, valid lambda
  terms, valid Turing-machine tables, ...).
- $\llbracket \cdot \rrbracket : L \rightharpoonup \mathbb{N}$ is a **partial**
  denotation function: it sends a legal expression to the natural number it
  names, when that is well-defined, and is undefined otherwise (a program
  that does not halt, a formula that does not pin down a unique natural
  number, a lambda term that does not normalize to a Church numeral or
  binary-encoded integer, etc.).

For $e \in L$, write $|e|$ for the length of $e$ as a string over $\Sigma$.
(Section 5 discusses normalizing this to bits so that systems with
different alphabet sizes can be compared fairly.)

## 3. Definition

$$
BN(R, n) \;=\; \sup \left\{\, \llbracket e \rrbracket \;:\; e \in L,\; |e| \le n,\; e \in \operatorname{dom}(\llbracket \cdot \rrbracket) \,\right\}
$$

with $BN(R, n) = 0$ (or "undefined") if no expression of length $\le n$ has
a well-defined value.

$BN$ is trivially monotone non-decreasing in $n$: enlarging the budget only
enlarges the candidate set.

## 4. Admissibility conditions on R

$BN(R, n)$ is only a meaningful "biggest number per symbol" function if $R$
satisfies conditions that rule out the Berry-paradox failure mode ("the
smallest number not nameable in under twenty syllables" — ill-defined
because English has no fixed decidable grammar or semantics). These are the
conditions CodeParade's construction is implicitly reaching for when it
insists on Turing machines, then lambda calculus, as the base rather than
"any programming language" or "any English description":

- **(A1) Fixed alphabet.** $\Sigma$ is finite and does not depend on $n$.
- **(A2) Decidable syntax.** $L$ is a decidable subset of $\Sigma^{*}$:
  given a string, whether it is a legal expression can be checked by an
  algorithm. This makes "enumerate all candidates of length $\le n$" an
  effective procedure, even though evaluating them may not be.
- **(A3) Fixed evaluation rules.** $\llbracket \cdot \rrbracket$ is
  specified by a fixed, finite set of computation or proof rules,
  independent of $n$ (a transition function, a reduction relation, an
  axiom system plus inference rules).
- **(A4) Well-definedness / consistency.** For every $e \in
  \operatorname{dom}(\llbracket \cdot \rrbracket)$, $\llbracket e
  \rrbracket$ is unique. If $R$ is logic-based, this requires the
  underlying theory to be **consistent** — an inconsistent theory proves
  everything via explosion, so every formula would "name" every number and
  $BN(R, n)$ would be trivially (and vacuously) unbounded for every $n$.
  This is the formal counterpart of "the rules must not be
  self-contradictory."
- **(A5) Bounded self-description.** There is a fixed constant $\kappa(R)$
  — the length, in some fixed reference meta-language, of a full
  specification of $\Sigma$, $L$'s grammar, and the evaluation/proof rules
  — and $\kappa(R)$ does not grow with $n$. This is the condition your
  observation is really about: a rule-set that is allowed to scale with $n$
  (or that is already enormous) isn't measuring "biggest number per $n$
  symbols," it's measuring "biggest number per ($n$ + however much was
  spent defining $R$) symbols," which defeats the point of fixing a budget
  at all.

A system satisfying (A1)-(A5) is called **admissible**. All of the
constructions in the two videos are (implicitly) admissible reference
systems: Turing machines, lambda calculus, BLC, and first-order set theory
each have a fixed finite grammar and a fixed finite rule set, and (assuming
the theory used is consistent) a well-defined denotation.

## 5. Bit-normalized budget

Raw symbol count depends on $|\Sigma|$: a system with a 2-symbol alphabet
and one with a 50-symbol alphabet are not directly comparable measured in
symbols. Define the bit-normalized length
$$
|e|_{\text{bits}} = |e| \cdot \log_2 |\Sigma|
$$
and $BN_{\text{bits}}(R, n) = BN(R, n / \log_2|\Sigma|)$ when comparing
across systems with different alphabets (this is exactly why BLC, which
uses an optimized 0/1 encoding rather than ASCII source text, compresses so
much better per byte than the Python or Haskell programs in the first
video — most of the gain is a smaller alphabet-normalized constant, not a
difference in what is expressible in principle).

## 6. Basic properties

**Monotonicity.** $BN(R, \cdot)$ is non-decreasing (Section 3).

**Uncomputability (for Turing-complete R).** If $R$ can encode arbitrary
Turing machines (i.e. $L$ and $\llbracket \cdot \rrbracket$ can simulate
any TM and its halting output), then $BN(R, \cdot)$ is not a computable
function of $n$. This is the standard Busy Beaver argument (Radó, 1962):
a computable $BN(R, \cdot)$ would let you decide whether a given machine of
description-length $m$ halts, by simulating it for $BN(R, m)+1$ steps and
declaring non-halting if it hasn't stopped by then — solving the halting
problem, which is impossible. $BN(R, \cdot)$ therefore grows faster than
every computable function.

**Invariance up to an additive constant.** For any two admissible,
Turing-complete reference systems $R_1, R_2$, there is a constant $c =
c(R_1, R_2)$ — the length of an interpreter for $R_1$ written in $R_2$ (or
vice versa) — such that
$$
BN(R_1, n) \;\le\; BN(R_2, n + c) \quad \text{for all } n,
$$
and symmetrically with $R_1, R_2$ swapped. This is the busy-beaver /
Kolmogorov-complexity invariance theorem applied to this setting. It
explains the shape of CodeParade's own progression: moving from Python to
Haskell to lambda calculus to BLC does not change *which growth class* is
eventually reachable (all four are Turing-complete, so all four are
eventually dominated by the same "faster than any computable function"
behavior) — it only shrinks the additive constant, i.e. how much of the
budget is wasted on interpreter/boilerplate overhead before you start
buying real growth. That is why the crossover happens so early (real gains
appear already at 15-49 bytes of BLC) and why the specific numeric value of
$BN(R, n)$ at small, practically-computable $n$ is far more sensitive to
$R$'s per-symbol overhead than to $R$'s theoretical power.

**Sub-Turing-complete R gives computable BN, indexed by an ordinal.** If
$R$ is admissible but not Turing-complete — e.g. $L$ and $\llbracket \cdot
\rrbracket$ only capture primitive recursion, or a specific ordinal-notation
system such as the Bashicu Matrix System, or provable termination in a
fixed formal theory $T$ — then $BN(R, \cdot)$ may be computable, and its
asymptotic growth rate is classified by the fast-growing hierarchy indexed
at $T$'s (or $R$'s) proof-theoretic ordinal $PTO(R)$. This is precisely the
ladder the second video climbs: $\varepsilon_0$ for Peano arithmetic,
Buchholz's ordinal $\psi(\Omega_\omega)$ for $\Pi^1_1\text{-CA}_0$ (and for
single-row BMS), something between that and full second-order arithmetic
for multi-row BMS, and the proof-theoretic ordinal of System F / the
Calculus of Constructions for Loader's number. Each rung is a genuinely
different, more expressive admissible $R$, each with a larger $\kappa(R)$
than the last (more rules to specify) buying a strictly faster-growing
$BN(R, \cdot)$.

## 7. Known instances

| $R$ | Budget unit ($n$) | Domain of $\llbracket\cdot\rrbracket$ | Computability of $BN(R,\cdot)$ |
|---|---|---|---|
| Turing machines, $k$ states, 2-symbol tape | number of states | halting machines' output | uncomputable (Busy Beaver, Radó 1962) |
| Binary Lambda Calculus (Tromp) | bits | closed terms normalizing to a Church/binary numeral | uncomputable |
| Bashicu Matrix System, single row | symbols/bytes (via BLC encoding, Kale) | terminating sequences | computable; growth rate $\varepsilon_0$ |
| BMS / proof-theoretic-ordinal systems up to $\Pi^1_1\text{-CA}_0$ | bytes | terminating sequences / provably total functions | computable; growth rate $\psi(\Omega_\omega)$ (Buchholz's ordinal) |
| Loader's number's system (System F / Calculus of Constructions) | bytes | strongly-normalizing typed terms | computable; growth rate the PTO of System F / CoC |
| First-order set theory (Rayo's function) | symbols | formulas with one free variable naming a unique natural number | uncomputable; provably dominates every function whose totality is provable in the same theory |

Rayo's function is the case where $R$ is taken to be (a fixed, consistent
axiomatization of) first-order set theory itself — the strongest
admissible $R$ commonly used, precisely because first-order logic has a
fixed, small, decidable grammar (condition A2) even though the *theory*
built on top of it (ZFC) is extremely expressive. Its value is not just
"big": by a diagonal argument against the theory's own proof strength, it
provably grows faster than any function whose totality that theory can
prove — which is the sense in which each successive $R$ in the table
"dominates" the ones before it.

## 8. The open question this framework is for

Sections 6-7 show that growth rate is governed by $PTO(R)$ (or, in the
Turing-complete case, is simply "uncomputable, full stop"), while the
*practical* value of $BN(R,n)$ at small, checkable $n$ is governed by the
per-symbol overhead captured in the invariance constant $c(R_1,R_2)$. Both
of those are properties of $R$ alone. What is not standard, and is the
genuinely open direction your question points at, is a formal relationship
between $\kappa(R)$ (how much it costs to specify $R$'s own rules) and how
fast $BN(R, \cdot)$ is allowed to grow. Concretely:

- Is there a "compactness law" bounding $PTO(R)$ (or, for Turing-complete
  $R$, the invariance constant $c(R, R_0)$ against some fixed baseline
  $R_0$) as a function of $\kappa(R)$? I.e., how much specification
  complexity must be paid to reach the next rung of the fast-growing
  hierarchy?
- Is the googology-community progression (Peano arithmetic $\to$
  $\Pi^1_1\text{-CA}_0$ $\to$ multi-row BMS $\to$ System F/CoC $\to$ ZFC)
  close to the *cheapest* way to reach each successive ordinal, or is it
  just the sequence people happened to formalize? Nothing in the existing
  literature seems to claim optimality here.
- Empirically: for small, human-checkable budgets ($n = 1$ bit, $n = 10$
  symbols, $n \approx$ tens of bytes), which admissible $R$ actually
  maximizes $BN(R,n)$, and how does the maximizing $R$ change as $n$ grows?
  This is close to the "bignum bakeoff" community's actual practice (John
  Tromp's BLC leaderboard, Ralph Loader's `loader.c`, Pat Kale's BMS-to-BLC
  port) but that community optimizes one fixed $R$ (BLC) rather than
  varying $R$ itself and studying $\kappa(R)$ against the reachable
  $BN(R,n)$.

## 9. Practical scope for further work

Exact values of $BN(R, n)$ are only tractable for very small $n$, mirroring
Busy Beaver (known exactly only up to $BB(5)$ as of the 5-state proof in
2024; $BB(6)$ is only lower-bounded). A concrete empirical study should:

1. Fix a small set of well-studied admissible $R$ (small Turing machines;
   BLC; a couple of BMS/ordinal-notation systems) rather than trying to
   search over "all possible $R$."
2. For $n$ in the range where exhaustive or near-exhaustive search is
   feasible (single-digit states for TMs; tens of bits for BLC), compute or
   look up $BN(R,n)$ directly and compare against the bignum-bakeoff and
   `bbchallenge.org` leaderboards as ground truth.
3. For larger $n$ (hundreds to millions of symbols), exact search is
   infeasible; use the ordinal-notation systems themselves (BMS, Buchholz's
   $\psi$) as computable *lower bounds* on $BN(R,n)$ for Turing-complete
   $R$, since a term that provably terminates is automatically a legal
   witness, and use the invariance theorem (Section 6) to transport bounds
   between BLC-style $R$ and other Turing-complete encodings.
4. Treat $\kappa(R)$ concretely as the byte-length of a reference
   implementation of $R$'s parser plus evaluator/reduction rules (e.g. in
   BLC or in a fixed universal Turing machine), so the open question in
   Section 8 has an actual measurable quantity on both axes rather than a
   philosophical one.

## References (by name, not URL — locate via the googology/bignum-bakeoff literature)

- H. Radó, "On non-computable functions," 1962 (Busy Beaver).
- A. Rayo, the "Big Number Duel," 2007 (Rayo's function).
- J. Tromp, work on Binary Lambda Calculus and the BLC bignum leaderboard.
- R. Loader, `loader.c` (Loader's number).
- P. Kale, Bashicu Matrix System proofs and BLC port of BMS and of
  Loader's number (referenced directly in the "Finding Even Larger
  Numbers" transcript, via a linked Stack Overflow post).
- S. Saibian, Googology Wiki articles on FOOT / BIG FOOT and the
  oodle/array-notation hierarchy, for the broader "successively stronger
  reference theory" pattern this note formalizes as $\kappa(R)$ vs.
  $PTO(R)$.
- Kolmogorov complexity invariance theorem (any standard computability
  theory reference, e.g. Li & Vitányi) for the proof technique behind
  Section 6's invariance claim.
