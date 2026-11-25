# The claimed proof that VP ≠ VNP, and where it sits next to this project

*Written 2026-11-24, at Ed's request, about a day after the claim
appeared. A companion to `P-VS-NP-LIMITS.md`,
`PROOF-BUDGETS-AND-COMPLEXITY.md` and `POLYLOG-NAMING-LADDER.md`.*

Tags used here, which differ slightly from the other notes because this
note is about someone else's work:

- **[read]** I read it in the primary source (the paper, the README or
  the Lean files) on 2026-11-24.
- **[reported]** a secondary source says so and I did not check it.
- **[my reading]** my own interpretation. It has not been checked by
  anyone else.
- **[classical]** a published result, cited from memory unless it says
  otherwise.

Nothing in this note is human verification of the proof. I am an AI
model too, and I did not build the Lean development (see §3.3).

## 0. In plain language

- **What is claimed.** A Claude model at Anthropic, described only as
  "an internal research Claude model", found a proof that the permanent
  cannot be computed by small *arithmetic* circuits. Arithmetic circuits
  are circuits whose gates add and multiply. The claimed bound is
  superpolynomial, though only just: roughly `2^{c·(log m)^{4/3}}` gates
  for an `m × m` matrix. That separates Valiant's classes VP and VNP,
  over every field. This is the algebraic cousin of P versus NP, open
  since 1979. **[read]**
- **What is checked by machine.** A Lean 4 development of 324 files and
  about 73,000 lines proves the main theorems. The repository's CI
  reports that Lean's own checker and a second, independent checker
  both accept it, with only the three standard axioms. **[read for the
  setup; reported for the CI result]**
- **What is not checked.** No human mathematician has checked the
  paper, the Lean proof, or, most importantly, the ~100-line file that
  says what the Lean theorems *mean*. Anthropic says so itself. A Lean
  proof is only as good as its statement. **[read]**
- **Is it P versus NP?** No, and the paper says so in its abstract.
  An arithmetic circuit must compute the polynomial itself, as a formal
  expression, while a Boolean circuit only has to get the right answer
  on 0s and 1s. The known implication runs the *other* way: a Boolean
  separation (NP ⊄ P/poly) would give VP ≠ VNP, under the generalized
  Riemann hypothesis. Nothing is known in the direction we would want.
  **[read; classical]**
- **The barriers.** The Boolean barriers in `P-VS-NP-LIMITS.md` §1 and
  §3 do not apply as stated, because they are about Boolean computation.
  The algebraic version of natural proofs is a real concern, and the
  paper's main tool is deliberately non-explicit, which is how it seems
  to stay clear of it. The paper says it has *not* analysed relativization
  or algebrization. **[read; my reading for "seems to"]**
- **For this project.** It changes no result here. The most interesting
  link is to `P-VS-NP-LIMITS.md`: we said diagonalization alone cannot
  separate P from NP because it treats machines as black boxes. Half of
  this proof ends in exactly such a diagonal argument, but only after a
  step that opens up the circuit and reads the polynomial at every
  gate. That is the "non-black-box step" our note said would be needed,
  in a setting where it is available. **[my reading]**

## 1. Sources

Primary, all read on 2026-11-24:

- Repository folder `anthropics/formal-math`, `vp-vnp/`:
  <https://github.com/anthropics/formal-math/tree/main/vp-vnp>. It holds
  the README, `paper.pdf`, `Statement.lean`, `Challenge.lean`,
  `Solution.lean`, `comparator.json` and the development itself.
  The README says: "Research artifact. Not maintained and not accepting
  contributions."
- The paper: *VP ≠ VNP over every field*, by "Claude (Anthropic)",
  70 pages, the `paper.pdf` in that folder. I read the abstract,
  Sections 1 to 3 (introduction, proof overview, Lean statement file)
  and Appendix Q (the Lean development), not the 50-page appendix
  proof. A preprint copy is reported at hexagonmath.org (2611.00954v1).
  No arXiv posting was found. **[reported]**

There is no Anthropic blog or newsroom post that I could find. The
README is Anthropic's only statement. **[reported, by vibemathlab.com
on 23 November]**

Secondary, used for reactions and for things I did not check myself:
lilting.ch (which counted the files and read the CI log), datacamp.com,
explainx.ai, casrai.org, vibemathlab.com, winzheng.com. Full links are
at the end.

## 2. What exactly is claimed

### 2.1 The theorems

**Theorem 1.1 of the paper. [read]** There is an absolute constant
`c > 0` such that, for every characteristic `p` (zero or prime), there is
an `m₀` with this property. Over every field of characteristic `p` and
for every `m ≥ m₀`, every arithmetic circuit for the Hamiltonian cycle
polynomial `HC_m`, and every circuit for the permanent `PERM_m` if
`p ≠ 2`, has more than `m^{c·(log₂ m)^{1/3}}` gates.

- In characteristic 2 the permanent *is* the determinant, which has
  small circuits. That is why the permanent is excluded there and the
  Hamiltonian cycle polynomial is used instead.
- `m^{c(log m)^{1/3}} = 2^{c(log m)^{4/3}}`. This is superpolynomial
  but quasi-polynomial. The best upper bounds are exponential,
  `2^{O(m)}` (Ryser's formula). So there is a huge gap left.
- The circuits are general: any depth, any constants from the field,
  cancellations allowed. Variables and constants count as gates.
- `m₀` is not computed. It depends on an integer `μ` that the proof
  shows exists but does not find (§2.3 below). So the theorem names no
  concrete `m` at which the bound starts to hold.
- The previous best lower bound for general circuits was Baur and
  Strassen's `Ω(n log d)`, about `m² log m` for the permanent. If the
  claim holds it is a very large jump. **[read; classical]**

**Corollary 1.2. [read]** Over every field, VP is a proper subset of
VNP.

**Theorem 1.4. [read]** The same bound holds for circuits that only
*approximate* the polynomial, in the sense of border complexity. So VNP
is not contained in the closure of VP. The paper says this implies that
the permanent is not approximated by small determinants, which is the
statement Mulmuley and Sohoni's geometric complexity theory programme
aims at. That consequence (Remark N.6) is the one numbered statement
that is not in Lean.

### 2.2 What the paper says it does not do

From the abstract and §1.3 **[read]**:

- It does not settle P versus NP, and "says nothing about whether
  NP-complete problems have fast algorithms".
- The bound "does not apply to Boolean circuits".
- "We have not analysed how it relates to relativization and
  algebrization."
- It has not worked out the consequences for derandomizing polynomial
  identity testing.

### 2.3 The shape of the proof

From the paper's §2 overview **[read]**. I have not checked any of it.

1. **Spectral points.** The basic objects are functions on tensors in
   the style of Strassen's asymptotic spectrum: multiplicative, and
   monotone under restriction and sums. The ones used are only shown to
   exist by Zorn's lemma. Nobody, including the paper, has a formula for
   them.
2. **Distances with nonpositive curvature.** Each spectral point gives a
   distance between the "parties" of a tensor. An identity for two
   crossing wires shows these distances always satisfy the Bruhat–Tits
   inequality, so they look like distances in a CAT(0) space.
3. **Two cases, at least one of which holds over every field.** Either
   these distances can be Euclidean (the *flat* case), or for some `μ`
   they always fall short of Euclidean by a fixed factor on a certain
   configuration of `μ × μ` matrices over F₂ (the *contracting* case).
   The paper does not know which case holds, even over the reals.
4. **Flat case.** A small circuit for the permanent gives, by
   substitution, a small circuit for the polynomial of a "network of
   wires" on the complete graph. Splitting that circuit at balanced
   sets of gates, as in depth reduction, writes its tensor as a sum of
   low-rank pieces. A Euclidean choice of distances then forces the
   circuit to be large. This gives the `2^{c(log m)^{4/3}}` bound.
5. **Contracting case.** No circuit appears for most of it. A Poincaré
   inequality, a duality theorem and "rerouting laws" show that every
   computation of a weighted nondeterministic program can be cut into
   short pieces. Then: a small circuit for the permanent, read *as a
   formal polynomial* gate by gate, gives an "accelerator" that sums the
   runs of short programs faster than they run. Repeating this at
   larger and larger scales and then diagonalizing gives a program whose
   value `V` would satisfy `V = 1 + V`. That is impossible. This case
   gives the stronger bound `2^{c(log m)²/log log m}`.
6. **Where it fails for the determinant.** Only at the substitution
   step: the permanent can express these polynomials, and the
   determinant is not known to.
7. **Where it fails for Boolean circuits.** At the two steps that look
   inside the circuit. A Boolean circuit for `HC_m` may compute any
   polynomial that agrees with `HC_m` on 0/1 inputs, for example
   `HC_m + Σ (x_i² − x_i)·h_i`. Its multilinear and low-degree parts
   can be unrelated to those of `HC_m`, so neither step says anything.

**An important caveat inside the paper. [read]** The paper's appendix
says that four of its proofs (Proposition I.1, Theorem H.2(d)(e),
Theorem J.3 and Proposition N.4) "describe machines and programs and
account for their sizes and running times. That these do exactly what is
claimed can be verified only in the Lean development." So the
contracting case, and with it every main theorem, relies on Lean at
those points. A human referee cannot fully check the paper on paper
alone.

## 3. Verified versus reported

### 3.1 What Lean is said to check

**[read]** The README describes two checks.

- `lake build` should print `sorry` warnings only from `Challenge.lean`,
  and `scripts/PrintAxioms.lean` should list no axioms beyond `propext`,
  `Classical.choice` and `Quot.sound`. These are the three standard
  axioms that Mathlib itself uses. The paper says there is no
  `native_decide` and no declared axiom.
- The repository's CI runs Comparator (`leanprover/comparator`). It
  checks that each of five theorems in `Solution.lean` has exactly the
  statement of its namesake in `Challenge.lean`, and replays the proofs
  in Lean's kernel and in **nanoda**, an independently written checker.
  The five theorems are `mainTheorem`, `mainTheoremApprox`, `separation`,
  `separationClosure` and `permanent_over_real`.

**[reported]** The CI job "verify (vp-vnp)" passed on 23 November,
21:44–22:05 UTC, and its log ends "Your solution is okay!" (lilting.ch,
which read the log). I did not open the CI log myself.

### 3.2 Does the statement file say what is claimed?

This is the weak point that everyone, including Anthropic, flags. The
README: "Lean checks the proofs, but no machine checks that this file
says what is claimed." Appendix Q: "Whether the statements say what is
meant was judged only by AI readers."

I read `Statement.lean` (98 lines, imports only Mathlib),
`Challenge.lean` and the start of `Solution.lean`. **[read]**

- `Challenge.lean` imports `Statement.lean` and adds only the five
  theorem headers with `sorry`. So the trusted definitions are exactly
  those in `Statement.lean`, and Comparator's check ties the proved
  theorems to them.
- `Computes f s`: a list of `s` polynomials, each a variable, a
  constant, or the sum or product of two earlier entries, with `f` among
  them. That is the standard model, equality as formal polynomials, any
  constants allowed.
- `perm` and `hc` are the usual sums over all permutations and over the
  single-cycle permutations.
- `Beyond c m s` is `m^{c·(log₂ m)^{1/3}} < s` over the reals. The
  exponent parses as `(log₂ m)^{1/3}`.
- `MainTheorem` matches Theorem 1.1, including one `m₀` per
  characteristic for all fields of that characteristic at once.
- `VP`: number of variables, total degree and circuit size are all at
  most `n^a + a`. `VNP`: `f_n` is the sum over all 0/1 vectors `e` of
  `g_n(x, e)` with `g` in VP. The number of summed bits is not bounded
  separately, but it is bounded by the VP condition on `g`. Both match
  Valiant's definitions as usually stated.
- `Separation` says `VP F ⊂ VNP F` for every field, which includes the
  easy inclusion and its strictness.
- `Approximates` asks for a circuit over Laurent series in `ε` computing
  `f + ε·g` with `g` having power-series coefficients. This is the usual
  algebraic definition of border complexity.

**My reading:** I found no mismatch, and no quirk that would make the
separation true for a trivial reason. But this is one more AI reader,
not the human check the README says is missing. **[my reading]**

### 3.3 What I could not do

- **Build the development.** I tried to install the Lean toolchain in my
  sandbox to rerun `lake build` and the axiom printout. The installation
  was blocked by my environment's permissions, so I stopped there. As of
  24 November no outside rebuild has been reported. **[reported:
  datacamp.com, vibemathlab.com]** Rebuilding it on Ed's computer is
  possible (it took about 22 minutes in CI) if wanted.
- **Read the appendix proof.** It is 50 pages. Even a complete reading
  would not settle the four Lean-only steps above.
- **Confirm an OpenAI counter-claim.** One headline (fourweekmba.com)
  says OpenAI posted its own VP ≠ VNP proof five hours later. The page
  would not load, and no other source I read mentions it. Treat it as
  **unconfirmed**. The OpenAI work that the paper *does* cite is
  different: a cubic lower bound on the determinantal complexity of the
  permanent, also with Lean.

### 3.4 Expert reaction so far

- **Lance Fortnow** (via an X post quoted by datacamp.com): if it holds,
  the permanent has no polynomial-size arithmetic circuits over the
  reals, and it does not settle P versus NP. He reportedly had Claude
  and Gemini check that the *formal statement* matches, called it
  "likely correct" and "a huge result", and said the proof "seems to
  sidestep" geometric complexity theory. **[reported, single source; I
  did not read the post]**
- Other researchers shared the link on Bluesky without comment.
  **[reported]**
- No detailed human audit had been published as of 24 November.
  **[reported]**

**Summary of status:** the proof is machine-checked against a statement
that looks right to AI readers, including me. It is not human-verified,
not peer-reviewed, and not independently rebuilt. A fair one-line status
is "credible and formally checked, but unconfirmed".

## 4. What it implies for Boolean P versus NP

**Nothing directly. [read; classical]**

- Arithmetic circuits must output the polynomial itself. Boolean circuits
  only need the right values on 0/1 inputs, and may use tricks
  (`x² = x`, bit manipulation) that have no meaning for a formal
  polynomial. The paper's §2.5 shows exactly where its proof breaks for
  Boolean circuits.
- Known implications go from Boolean to algebraic. Bürgisser (2000): if
  NP ⊄ P/poly, then VP ≠ VNP over ℂ, assuming the generalized Riemann
  hypothesis. A proof of VP ≠ VNP is therefore *consistent with* P ≠ NP
  and is evidence of a sort, but no theorem turns it into a Boolean
  separation.
- Evaluating the permanent of a 0/1 matrix is #P-complete (Valiant
  1979). That is a Boolean statement, and the claimed theorem does not
  touch it.

**A possible indirect link. [classical, from memory; not re-checked]**
Kabanets and Impagliazzo (2004) tied permanent lower bounds to
derandomizing polynomial identity testing, which is a Boolean-world
question. The paper explicitly leaves this unexplored. With a bound
this weak (quasi-polynomial) any consequence is likely to be modest.
This is the place where an expert would first look for Boolean
fallout.

## 5. The three barriers

`P-VS-NP-LIMITS.md` §§1 and 3 list relativization, natural proofs and
algebrization as the three barriers a proof of P ≠ NP must get past.
How they bear on this claim:

| barrier | applies to this claim? | status |
|---|---|---|
| **Relativization** (Baker–Gill–Solovay) | Not as stated. It is about Turing machines with an oracle, and arithmetic circuits have no standard oracle. | The paper has not analysed it. **[read]** |
| **Natural proofs** (Razborov–Rudich) | Not as stated. It is about Boolean circuits and assumes pseudorandom functions. | — **[classical]** |
| **Algebraically natural proofs** (Forbes–Shpilka–Volk; Grochow–Kumar–Saks–Saraf) | Yes, this is the algebraic analogue, and it is conditional: it would bite only if certain succinct hitting sets exist, and the paper cites evidence both ways. | The flat case uses spectral points that exist only by Zorn's lemma, so it is not "constructive" in the natural-proofs sense. The contracting case uses no property of polynomials other than low degree, and ends in a diagonalization. **[read]** Whether that is enough to avoid the barrier is **[my reading]**: plausibly yes, but nobody has argued it carefully. |
| **Algebrization** (Aaronson–Wigderson) | About Turing-machine class separations with algebraic oracles. Not directly applicable. | The paper has not analysed it. **[read]** |
| **Rank methods** (Efremenko–Garg–Oliveira–Wigderson and others) | Yes: known limits on lower bounds via ranks of partial-derivative matrices. | The paper replaces ranks with spectral points to avoid this. **[read]** |
| **Geometric complexity theory obstructions** (Ikenmeyer–Panova; Bürgisser–Ikenmeyer–Panova) | Limits occurrence obstructions in GCT. | The proof does not use GCT, though Theorem 1.4 reaches GCT's target statement. **[read]** |

A caution on a common phrasing: it is not quite right to say
algebraic lower bounds "sidestep" natural proofs. They sidestep the
*Boolean* barrier, but there is an algebraic analogue that may or may
not be a real obstacle. This proof appears to avoid it by being
non-constructive. **[my reading]**

## 6. Where it sits relative to this project's notes

### 6.1 `P-VS-NP-LIMITS.md`: diagonalization, with a white-box step

Our note says the project's tools (Berry's paradox, diagonalization,
Busy Beaver) cannot settle P versus NP because they relativize: they
treat machines as black boxes, so they work the same way with any
oracle attached.

The contracting case of this proof *ends* in a diagonalization: a
program applied to itself would have value `V = 1 + V`. That is the same
self-reference trick as Berry's paradox and our "no top" argument. What
makes it work here is the step before (Lemma K.2, `lem_lowdeg`), which
opens the circuit and reads the formal polynomial at every gate,
including its low-degree part. A black box gives no such access, and
neither does a Boolean circuit. **[read for the proof structure; my
reading for the comparison]**

So the claim is a worked example of what `P-VS-NP-LIMITS.md` §2 says a
separation needs: the diagonal argument is fine as the *last* step,
provided an earlier step uses something that does not survive replacing
the machine by a black box. In the algebraic world "look at the
polynomial each gate computes" is such a step. In the Boolean world
there is no known equivalent, and that is the whole difficulty.

Nothing in our §6 summary table changes. Our arguments still relativize
and still cannot settle P versus NP.

### 6.2 `PROOF-BUDGETS-AND-COMPLEXITY.md`: finding versus checking

Our note recalls Gödel's 1956 question: bounded provability is
NP-complete, so finding short proofs is believed hard while checking
them is easy. This claim is a large real-world instance. The proof is
about 73,000 lines of Lean. Finding it took an AI research model an
unknown amount of effort, but checking it is mechanical and took about
22 minutes in CI. The weak point is neither the search nor the check,
but the 98-line statement that says what the checked theorem means. In
our language, the trusted part is the *name* (the formula), not the
proof. **[my reading]**

None of the propositions in that note change. Its claim that P versus
NP "lives in the complexity measure" is about Boolean and Turing-machine
measures. Algebraic circuit size is a different measure.

### 6.3 `POLYLOG-NAMING-LADDER.md` and `CALCNAME2-HARDNESS.md`: no transfer

These notes ask whether naming *explicit numbers* with short
calculations is hard, and they compare that with the Shub–Smale
`τ`-conjecture (`τ(n!)` is not polylog in `n`), which would imply
P ≠ NP over ℂ in the Blum–Shub–Smale model and, by Bürgisser's work, a
constant-free version of VP ≠ VNP. **[classical, from memory]**

The implications run from `τ` to VP ≠ VNP, not back. A lower bound for
a *multivariate polynomial family* says nothing about the complexity of
individual integers. So:

- Statement (ii) of `CALCNAME2-HARDNESS.md` §1, explicit numbers with no
  short B-name, is still open and as hard as before.
- The Kabanets–Cai-type barrier there is unaffected.
- The `β_j` ladder and its ETH-conditional strictness are unaffected.
  ETH is a Boolean hypothesis.

The method might matter more than the result. Spectral points and the
"ranks become distances" lemma are tools for lower-bounding tensors.
Whether anything like them applies to integer straight-line programs is
**[open]**, and I see no obvious route.

## 7. Summary

| statement | status |
|---|---|
| A Claude model's paper claims VP ≠ VNP over every field, with bound `2^{c(log m)^{4/3}}` | **[read]** |
| The main theorems are proved in Lean with only the standard axioms | claimed in README and paper **[read]**; CI pass **[reported]**; not rebuilt by me or anyone outside **[reported]** |
| The Lean statement file faithfully expresses the claim | judged by AI readers only, including me **[my reading]**; no human check |
| Four steps of the contracting case are checkable only in Lean | stated in the paper **[read]** |
| A human expert has verified the proof | **no**, as of 2026-11-24 |
| It implies P ≠ NP or any Boolean separation | **no** **[read; classical]** |
| It gets past the algebraic natural-proofs barrier | plausibly, through non-explicit spectral points **[my reading]** |
| It gets past relativization and algebrization | not analysed by the paper; these barriers are not stated for this model **[read]** |
| It changes any result in this project | **no** |
| An OpenAI VP ≠ VNP proof was posted the same day | **unconfirmed** |

## References

Primary:

- Claude (Anthropic), *VP ≠ VNP over every field*, `paper.pdf`, and the
  Lean development, <https://github.com/anthropics/formal-math/tree/main/vp-vnp>.
  Read 2026-11-24.
- `leanprover/comparator`, <https://github.com/leanprover/comparator>.
  [reported via lilting.ch]

Secondary, used for reactions and reported facts:

- lilting.ch, "Checking Anthropic's VP≠VNP Lean Proof", <https://lilting.ch/en/articles/vp-vnp-valiant-conjecture-claude-lean>
- DataCamp, "Claude Claims Proof of Valiant's Conjecture", <https://www.datacamp.com/blog/claude-claims-proof-of-valiants-conjecture-vp-vs-vnp>
- explainx.ai, "Claimed vs Verified", <https://explainx.ai/blog/anthropic-claude-vp-vnp-valiant-lean-proof-claimed-vs-verified-2026>
- CASRAI, <https://casrai.org/news/anthropic-claude-authored-vp-vnp-proof-unverified-lean-2026>
- Vibe Math Lab, <https://vibemathlab.com/guide/is-vp-vs-vnp-solved>
- winzheng.com, <https://www.winzheng.com/en/article/claude-vp-vnp-proof-unverified-lean-anthropic>
- FourWeekMBA headline on an OpenAI counter-claim (page did not load),
  <https://fourweekmba.com/ai-openai-posts-its-own-vp-vnp-proof-5-hours-after-anthropic/>

Classical, from memory unless the paper cites them:

- L. Valiant, "Completeness classes in algebra", STOC 1979.
- P. Bürgisser, *Completeness and Reduction in Algebraic Complexity
  Theory*, Springer 2000 (Boolean-to-algebraic implication under GRH;
  cited by the paper).
- W. Baur, V. Strassen, "The complexity of partial derivatives", 1983.
- M. Forbes, A. Shpilka, B. Volk, "Succinct hitting sets and barriers to
  proving lower bounds for algebraic circuits", 2018; J. Grochow, M.
  Kumar, M. Saks, S. Saraf, "Towards an algebraic natural proofs
  barrier via polynomial identity testing", 2017 (both cited by the
  paper).
- V. Kabanets, R. Impagliazzo, "Derandomizing polynomial identity tests
  means proving circuit lower bounds", *Comput. Complexity* 13 (2004).
- P. Bürgisser, "On defining integers and proving arithmetic circuit
  lower bounds", *Comput. Complexity* 18 (2009) (`τ`-conjecture and
  constant-free VP ≠ VNP).
