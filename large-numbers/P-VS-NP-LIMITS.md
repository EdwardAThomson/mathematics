# What this project can and cannot say about P versus NP

*Written 2026-11-24, at Ed's request. A companion to
`PROOF-BUDGETS-AND-COMPLEXITY.md` and `GENERAL-NAMING-THEOREM.md`.*

Tags as elsewhere: **[Lean]** machine-checked here, **[paper]** argued
here, **[classical]** a published result we cite, **[open]** nobody knows.

## 0. In plain language

**Short answer: our methods provably cannot settle P versus NP, and we
can say exactly why.**

- Every argument in this project still works if every machine is given
  the same "magic box": an oracle that answers some fixed question for
  free. Arguments with this property are called *relativizing*.
- In 1975 Baker, Gill and Solovay built one magic box that makes P equal
  NP and another that makes them differ. A relativizing argument would
  have to give the same answer for both boxes, so no relativizing
  argument can decide the question either way.
- So Berry's paradox, diagonalization and Busy Beaver, which run this
  whole project, are the wrong kind of tool. That isn't a matter of
  effort: it is a theorem about the tools.
- The closest real contact between our theme and P versus NP is a live
  research area called **meta-complexity**: how hard is it to work out
  the shortest description of an object, when descriptions have to run
  in limited time? Our "cost of naming with a short proof" is a question
  of exactly that kind. §4 states one precise open question it raises.
  It has the same flavour as the field's central open problem, and we do
  not claim to solve it.

## 1. Relativization

Give every machine access to an oracle `A`: a set of numbers it may
query in one step. `P^A` and `NP^A` are P and NP for such machines.

**Theorem (Baker, Gill, Solovay 1975). [classical]** There are oracles
`A` and `B` with `P^A = NP^A` and `P^B ≠ NP^B`. (For `A`, any
PSPACE-complete set works.)

A proof *relativizes* if it goes through unchanged when every machine in
it is given the same oracle. If a relativizing proof showed `P ≠ NP`, the
same proof would show `P^A ≠ NP^A`, contradicting the theorem. If it
showed `P = NP`, it would show `P^B = NP^B`, again a contradiction. So
neither answer has a relativizing proof.

Diagonalization relativizes. That is why it proves the time hierarchy
theorem (more time solves more, with or without an oracle) but cannot
compare P and NP, which differ in kind (guessing) rather than in
amount of time.

## 2. Our arguments relativize

1. **"No top" (Berry).** `Rayo/NoTop.lean` **[Lean]** is stated for an
   arbitrary naming scheme, any set of expressions with sizes and a
   "names" relation. It never asks what the expressions mean. A scheme
   whose expressions may consult an oracle is just another scheme, so the
   theorem applies to it as it stands.
2. **Busy Beaver class.** The project has in effect already proved the
   oracle version. `GENERAL-NAMING-THEOREM.md` **[paper; key lemmas
   Lean in `RayoBoolos/Decided.lean`]** shows a theory's naming function
   is Busy Beaver *relative to whatever oracles the theory decides*, with
   plain Busy Beaver as the case of no oracle. The argument treats the
   oracle as a black box. That is what relativizing means.
3. **Proof budgets.** In `PROOF-BUDGETS-AND-COMPLEXITY.md`, Proposition 1
   (the budget is the ceiling) is a counting argument that ignores
   computation altogether. Proposition 5 (`KNt ≲ D_T ≲ Kt`) and
   Corollary 6 go through with an oracle added to the machines and to
   the proof checker. **[paper]**

**Consequence. [paper, from the classical theorem]** No argument of the
kind used in this project can prove `P = NP` or `P ≠ NP`. Any connection
between our results and P versus NP has to be conditional ("if P = NP
then …"), or else go through a non-relativizing step that is not in the
project.

## 3. The other two barriers

These matter less to us, because we do not attempt circuit lower bounds.
They complete the picture of what a proof of `P ≠ NP` must avoid.

- **Natural proofs (Razborov and Rudich, 1994). [classical]** Most known
  lower-bound proofs for circuits work by finding an easy-to-check
  property that random functions have and easy functions lack. If secure
  pseudorandom functions exist, which cryptographers widely believe, no
  argument of that shape can prove `P ≠ NP`.
- **Algebrization (Aaronson and Wigderson, 2008). [classical]** Some
  famous non-relativizing results (IP = PSPACE, for instance) use
  algebraic extensions of the machines' oracles. Aaronson and Wigderson
  showed those techniques still cannot settle P versus NP.

So a proof of `P ≠ NP` must avoid all three: not relativize, not be
"natural", and not algebrize. This is the main reason the problem is
believed to need genuinely new ideas.

## 4. Where description complexity really meets P versus NP

**Meta-complexity** asks how hard it is to compute complexity measures
themselves. Two central objects:

- `K^t(x)`: the length of the shortest program that prints `x` within
  `t(|x|)` steps, for a polynomial `t`. This is Kolmogorov complexity
  with a time limit.
- **MCSP** (Minimum Circuit Size Problem): given the full table of a
  Boolean function and a size `s`, does the function have a circuit of
  size at most `s`? It is clearly in NP. Whether it is NP-complete has
  been open since Levin's work in the early 1970s.

Results that tie these to the big questions **[classical]**:

- **Liu and Pass (FOCS 2020, arXiv:2009.11514).** For every polynomial
  `t(n) ≥ (1+ε)n`, one-way functions exist (the basic assumption of
  modern cryptography) *if and only if* `K^t` is mildly hard to compute
  on average: no randomized polynomial-time algorithm gets it right on
  more than a `1 − 1/p(n)` fraction of `n`-bit strings, for some
  polynomial `p`.
- **Hirahara.** A worst-case to average-case reduction inside NP (STOC
  2021), proved using time-bounded Kolmogorov complexity with an NP
  oracle. Separately, NP-hardness under randomized reductions of the
  partial-function version of MCSP (FOCS 2022), a question open since
  Levin.
- **Huang, Ilango and Ren (STOC 2023).** NP-hardness of *approximating*
  meta-complexity with nearly optimal gaps, under a cryptographic
  assumption.
- **Barrier remark.** Ko (1991) showed that no relativizing proof can
  establish NP-hardness of some of these problems. The results above
  get round this with non-relativizing techniques. (Source: the Simons
  Institute's 2023 overview of its meta-complexity programme.)

**Our analogue. [paper for the definition and membership; open for
hardness]** The polynomial-scale version of our proof-charged naming
cost gives a decision problem:

> **Short-naming.** Given `k` in binary, a size `s` in unary and a proof
> budget `m` in unary: is there a formula `φ` with `|φ| ≤ s` and a
> `T`-proof of length `≤ m` of `∀x (φ(x) ↔ x = bin(k))`?

- It is in NP: guess `φ` and the proof, then check.
- If the formula is *fixed* and only the proof is sought, the problem is
  NP-complete. It is just bounded provability (Gödel's 1956 question to
  von Neumann).
- **Is Short-naming itself NP-hard? [open]** The obvious reduction from
  bounded provability breaks for the same reason as for MCSP. The
  question asks for *some* short formula, and a different formula may
  name `k` cheaply without solving the instance we encoded. This is the
  typical difficulty of meta-complexity. We have not resolved it. Any
  proof of NP-hardness would probably have to be non-relativizing, as in
  Ko's barrier above.

Whether Short-naming is NP-hard is the honest form of "can provable
naming tell us something about P versus NP?". It is a genuine research
question. We would expect a solution to need the modern meta-complexity
toolkit rather than anything in this project.

## 5. Could the relativization claim be machine-checked?

Partly, and the cheap part is already done.

- **Done.** The "no top" theorem (`NoTop.lean`) is scheme-agnostic, so
  it already covers oracle schemes. The key lemmas of the general naming
  theorem (`Decided.lean`) are stated for whatever a theory decides.
- **Not cheap.** A Lean statement "every theorem in `RayoBoolos` holds
  for oracle machines" would need oracle machines with code numbers and
  an oracle predicate added to Foundation's language of arithmetic.
  Mathlib does have oracle computability (`Mathlib.Computability.RecursiveIn`
  and Turing degrees), but not oracle Busy Beavers or an oracle-extended
  arithmetic. That is days of work, and it would only confirm what §2
  says on paper. We do not recommend it now.

Relativization is also, strictly, a property of *proofs*, not of
theorems. A Lean check of the oracle versions would show that the
oracle versions are true. It would not formalize the meta-claim that "no
proof of this shape can settle P versus NP". That claim is the content
of the Baker–Gill–Solovay theorem.

## 6. Summary

| statement | status |
|---|---|
| P versus NP is well defined, with a definite answer | [classical] |
| Our "no top", Busy Beaver and proof-budget arguments relativize | [Lean] for "no top"; [paper] otherwise |
| Hence they cannot prove P = NP or P ≠ NP | [paper], from Baker–Gill–Solovay |
| A proof of P ≠ NP must avoid relativization, natural proofs and algebrization | [classical] |
| One-way functions exist iff time-bounded Kolmogorov complexity is mildly hard on average | [classical] Liu–Pass |
| Short-naming is in NP | [paper] |
| Short-naming is NP-hard | [open] |

## References

- T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP
  question", *SIAM J. Comput.* 4 (1975). [memory]
- A. Razborov, S. Rudich, "Natural proofs", STOC 1994; *JCSS* 55
  (1997). [memory]
- S. Aaronson, A. Wigderson, "Algebrization: a new barrier in complexity
  theory", STOC 2008; *ACM TOCT* 1 (2009). [memory]
- Y. Liu, R. Pass, "On one-way functions and Kolmogorov complexity",
  FOCS 2020, arXiv:2009.11514. [abstract read]
- S. Hirahara, STOC 2021 and FOCS 2022 papers on meta-complexity, as
  summarized in V. Guruswami, "Theory at the Institute and Beyond,
  February 2023", Simons Institute. [overview read; papers not read]
- Y. Huang, R. Ilango, H. Ren, "NP-hardness of approximating
  meta-complexity: a cryptographic approach", STOC 2023, IACR ePrint
  2023/528. [abstract read]
- K.-I. Ko, "On the complexity of learning minimum time-bounded Turing
  machines", *SIAM J. Comput.* 20 (1991). [cited via the Simons overview]
- K. Gödel, letter to J. von Neumann, 20 March 1956. [memory]
