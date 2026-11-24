# Literature survey: provable naming, Busy Beaver, and the ladder

*Written 2026-11-24. Companion to `BOOLOS-IS-BUSY-BEAVER-CLASS.md`,
`THE-LADDER.md` and `COMPLEXITY-AND-ENTROPY.md`. Purpose: say, before
anything goes into a public report, which of this project's results are
already known, which are folklore, and which appear to be ours.*

## 0. Verdict in brief

- **Boolos's 1989 notion of "names" is exactly our `TNamesMeta`.** Boolos
  says a formula `F(x)` names `n` when the sentence `∀x(F(x) ↔ x = [n])` is
  in the output of the machine (for a formal system: is a theorem). So
  `BoolosBig_T` is literally "the largest number Boolos-named by a formula of
  size ≤ n", and the project's name for it is historically accurate.
- **Every ingredient of our results is classical.** Σ₁-completeness,
  representability of computable functions by a least-witness formula,
  proof search, Berry's paradox and Tarski's theorem are all textbook.
- **The specific packaged statements appear not to be in print** in the
  sources we could read: (i) `BoolosBig_T` is Busy-Beaver class for every
  consistent r.e. `T`, with an explicit two-sided sandwich and theory
  strength confined to the argument rescaling; (ii) `T` proves no exact value
  of its own `BoolosBig_T(n)` for any `n`. Both are short consequences of
  standard facts, so the honest label is **"apparently unstated folklore"**,
  not "new theorem".
- **What is clearly ours** is the Lean mechanization (no formalization of a
  Boolos-style naming function, or of its growth, turned up anywhere), the
  `ε₀` correction as a worked example, and the arrangement of the ladder.
- **Closest prior work** to the project as a whole is David Simmons,
  *Naming the largest number* (arXiv:1809.08676), which compares "axiomatic
  strategies" across theories and meta-languages, and Lafitte, *Busy beavers
  gone wild* (2009), which studies what theories can prove about Busy Beaver
  values. Neither states our sandwich.

Suggested wording for the public report is in §5.

## 1. How this was done, and its limits

Sources marked **[read]** below were read in full or in the relevant
sections during this survey. Sources marked **[memory]** are standard
references cited from memory: the citation details should be checked
against the publication before the report goes out. One source was only
partly read; this is noted at the entry.

Not reachable during the survey: the full text of Kikuchi, Kurahashi and
Sakai (2012); the Googology Wiki talk pages for Rayo's number; the later
sections and appendices of Simmons (2018/2022), which were seen only as a
summary. A search of these specific places is the main remaining gap
(§6).

## 2. Claim-by-claim assessment

### Claim 1. `BoolosBig_T` is Busy-Beaver class for every consistent r.e. `T` ⊇ basic arithmetic; theory strength only rescales the argument

Repo: `BOOLOS-IS-BUSY-BEAVER-CLASS.md` Theorems 1–3, Corollaries 4–5
(Theorem 1 in Lean; 2–5 paper).

**Status: apparently unstated folklore.** Each half is a one-paragraph
argument from standard facts, but we found no source stating the sandwich
or the theory-independence corollary.

What is known:

- *Lower half (dominates every computable function, ≥ BB after linear
  rescaling).* Follows from Σ₁-completeness of `Q` and representability of
  computable functions (Tarski, Mostowski and Robinson 1953; any textbook,
  e.g. Boolos, Burgess and Jeffrey). Chaitin, Arslanov and Calude (1995)
  [read] state the program-size version: with `Σ(n) = max{x : H(x) ≤ n}`,
  an `n`-bit program that halts does so in time `< Σ(n + c)`, and `Σ` is not
  recursively bounded. That is the Kolmogorov form of our Theorem 2.
- *Upper half (≤ BB after `n log n` rescaling).* Proof search; the same
  idea is used by Lacerda (2014) [read] to bound proof length by a Busy
  Beaver of the sentence length, and by Simmons [partly read], whose
  `f_A{n}` ("largest output of an algorithm that `A` proves halts with a
  proof of length ≤ n") is computed by an `O(log n)`-size program
  (his Thm 1.5). Simmons measures *proof* length, we measure *formula*
  length; the two functions are different, though both are Busy-Beaver
  class.
- *Theories determine only finitely many BB values; strength helps only
  finitely.* Aaronson (2020) Prop. 4 [read], Chaitin (1974) [memory], and
  Lafitte (2009) Thms 2.1–3.2 [read], who studies families `σ` of
  Busy-Beaver-like functions (max runtime, max output, a Kolmogorov
  variant) that differ by an additive shift of the argument.
- *Theory dominance in Simmons.* His Cor. 1.6 / 2.5: if `(L₁, A₁)` is at
  least as strong as the meta-system of `(L₂, A₂)`, the axiomatic strategy
  of `A₁` beats that of `A₂`. That is a dominance statement, not the
  "equal up to rescaling" statement we make.

Caution to carry into the report. Our Corollary 4 says theory strength
"hides in the constant `c_T`". Raatikainen (1998) [memory] criticizes
reading Chaitin's constant `c_T` as a measure of a theory's strength: it
depends on the coding and need not track consistency strength. Our claim is
only about growth class, which is safe, but any sentence suggesting `c_T`
*measures* how strong `T` is should be avoided or qualified with that
citation.

### Claim 2. Values of a computable `f` are `T`-nameable in `C_f + O(log n)` symbols by a least-witness formula, with no provable totality

Repo: `BOOLOS-IS-BUSY-BEAVER-CLASS.md` §2–3; Lean `BoolosBig_PA_log_bound`.

**Status: known (classical).** This is strong (functional) representability
of every computable function in Robinson's `Q`: there is one formula
`φ(x, y)` with `Q ⊢ ∀y(φ(n̄, y) ↔ y = f(n)‾)` for every `n`, and the
standard proof uses exactly the least-witness trick and needs no totality
proof inside the theory (Tarski, Mostowski and Robinson 1953 [memory]; Boolos,
Burgess and Jeffrey ch. 16 [memory]). Our `μₙ` is that formula with the
input numeral substituted.

The `O(log n)` comes from short numerals. Boolos (1989) [read] already uses
the same device: he writes `10^k`-ish bounds as `[10] × [k]` to keep his
Berry formula short. Dyadic numerals of logarithmic length are standard in
proof complexity (Pudlák 1998 [memory]). The analogue in program-size terms,
`K(f(n)) ≤ K(n) + c_f ≤ 2 log n + c_f`, is in every Kolmogorov textbook
(Li and Vitányi [memory]).

What is ours: the explicit constant 6 for this size measure, and the
machine-checked proof. Note for the report: the mechanized route avoided a
formal proof of representability by going semantically through
`Arithmetic.complete`; the textbook route is syntactic in `Q`.

### Claim 3. `T` proves no exact value of its own provable-naming function

Repo: `COMPLEXITY-AND-ENTROPY.md` §3.1 (paper).

**Status: apparently unstated, but an immediate corollary of a textbook
fact.** The argument: "`BoolosBig_T(n) = k`" contains at least one
conjunct `¬Pr_T(⌜ψ⌝)`, and a consistent `T` proves no sentence of that form,
because `T ⊢ ¬Pr_T(⌜ψ⌝) → Con(T)` and Gödel's second theorem applies. The
general fact ("a consistent theory proves no instance of its own
unprovability") is standard (e.g. Smoryński 1977 [memory], via Kikuchi's
and Kritchman–Raz's citations). We found no source applying it to the
Boolos naming function.

Related known results, each weaker or different:

- Aaronson (2020) Prop. 4 [read]: for arithmetically sound `T` there is
  `n_T` with no statement `BB(n) = k` provable for `n ≥ n_T`.
- Lafitte (2009) Thm 2.1 [read]: `T` proves, from `Con(T)`, that it
  cannot prove `σ(n_T) < s` for any `s`.
- Kritchman and Raz (2010) [read], Kikuchi (1995/1997) [read/memory]: `T`
  cannot prove `K(x) > L` for any `x`, and formalized versions give Gödel II.

What makes our version worth one sentence in the report is the contrast
it draws: for the ordinary Busy Beaver function, small values *are*
provable (`S(5) = 47,176,870` is proved in Coq), and unprovability starts
only at some threshold. For provable naming there is no threshold: every
nontrivial value is out of reach, for the trivial reason that pinning it
down asserts an unprovability. That is folklore-level, and should be
presented as an observation, not a theorem.

One check needed before publishing: the statement assumes `n` is large
enough that some formula of size `≤ n` exists (otherwise the value is a
vacuous default), and uses a standard provability predicate satisfying the
derivability conditions.

### Claim 4a. The ladder BB → oracle BB → … → Rayo, read as relativised Kolmogorov complexity

Repo: `THE-LADDER.md` §2, `COMPLEXITY-AND-ENTROPY.md` §5.2.

**Status: known in pieces; the arrangement is expository.**

- Oracle Busy Beavers `BB¹, BB², …, BB^ω, …` along computable ordinals:
  Aaronson (2020) §3 [read]; formal definitions and the link to the
  arithmetical hierarchy: Cao (2025) [read], whose Prop. 2 is a
  reformulation of Post's theorem.
- Busy Beaver as the inverse of Kolmogorov complexity
  (`BB⁰_L(n) = max{m : K_L(m) ≤ n}`): Aaronson §1 [read]; Chaitin's `Σ(n)`
  (Chaitin 1987; Chaitin, Arslanov and Calude 1995) [read].
- Kolmogorov complexity relative to `0′` and higher jumps:
  Bienvenu, Muchnik, Shen and Vereshchagin, "Limit complexities revisited"
  [memory for content; title confirmed], and the 2024 JSL paper "Limit
  complexities, minimal descriptions and n-randomness" [title confirmed,
  not read]; relativised `Ω`: Becher, Daicz and Chaitin (2001), Becher,
  Figueira, Nies and Picchi (2005) [memory].
- A hierarchy of naming languages ordered by "can express the previous
  one's semantics": Simmons [partly read], §2 and §4, which also invokes
  Tarski and Kripke-style self-referential truth.
- The googology version of "add the previous naming function as an
  oracle": Fish number 7's Rayo hierarchy `R_α` (Fish, October 2013)
  [read, Googology Wiki].

The specific bridge "naming by truth of Σ_k formulas ≈ BB at oracle level
`k−1`, up to argument rescaling" is tagged [expected] in the repo and we
found it nowhere explicitly. It should stay tagged that way.

### Claim 4b. "No largest number in n symbols" via Berry/Tarski

Repo: `THE-LADDER.md` §3; Lean `Rayo/NoTop.lean`.

**Status: known.** Berry's paradox (Russell 1906/1908 [memory]); Boolos
(1989) [read] is precisely the provability rung: his formula `F(x)` ("the
least number not named by a formula with fewer than `10k` symbols") has
about `2k + 24` symbols, is true of exactly one number, and the naming
sentence is not a theorem. Tarski's undefinability theorem gives the
truth-rung version, and Simmons §2 [partly read] states the general form
("no classical language reproduces its own metalanguage"). Iterated
truth-predicate extensions are what Fish number 7 does.

What is ours: the abstract Claims A/B in Lean core, which we found no
formalization of.

### Other statements worth checking

| statement in repo | assessment |
|---|---|
| `BoolosBig_T` not computable; Turing-equivalent to `0′` (Cor. 5) | known/folklore: same degree argument as for `BB` (Aaronson §2: "BB is Turing-equivalent to the halting problem") |
| PA-provably-total functions are exactly those below `ε₀` | classical (Kreisel, Wainer, Schwichtenberg) [memory] |
| Our earlier "≈ ε₀" reading was a confusion of provable totality with pointwise provable naming | the distinction is classical; the worked mistake is ours and is a good teaching example |
| `D_T` and `K` agree up to a constant factor and a log (COMPLEXITY §2b) | folklore; Lafitte has the additive-shift analogue between BB variants |
| at most `2^(c n log n)` numbers have `D_PA ≤ n` | trivial counting, classical |
| Shannon entropy = expected Kolmogorov complexity | classical (Li and Vitányi; Shen, Uspensky, Vereshchagin) |
| "For ZFC that size is known to be at most a few hundred states" (COMPLEXITY §3.3) | correct order, should cite: 748 states for ZF (O'Rear; reported in Aaronson 2020 Thm 7, conditional on the construction being sound), improvements to 636 and to 432 states reported as pending verification (bbchallenge 2025) |
| Rayo needs MK-strength / second-order satisfaction | Rayo himself and Wikipedia flag that well-definedness rests on second-order satisfaction; Aaronson (2020, fn 13) declines to count such sequences as well defined. Our MK analysis (`RAYO-R0-WELLDEFINEDNESS.md`) goes further than any source read |
| BIG FOOT ill-defined | not checked: the Googology pages were unreachable. Keep as the repo's own finding |

## 3. Recent work (2020–2026) touching the project

- **`S(5) = 47,176,870` and `Σ(5) = 4,098`**, proved in Coq (now Rocq):
  The bbchallenge Collaboration et al., arXiv:2509.12337 (2025, v2 2026).
  Also `S(2,4) = 3,932,964`. Uses `S` for steps and avoids the notation
  `BB(n)`. Independent proof of the key holdout: Chris Xu, *Skelet #17 and
  the fifth Busy Beaver number*, arXiv:2407.02426 (2024).
- **`S(6) > 2↑↑↑5`**: reported in the same paper (Table 1, Appendix B).
- **ZF independence threshold**: 748 states (O'Rear), improvements to 636
  and 432 states pending verification (as reported in arXiv:2509.12337).
  Aaronson conjectures ZF does not settle `BB(20)` and PA does not settle
  `BB(10)` (Conjectures 11–12).
- **Higher-order Busy Beaver**: Cao, arXiv:2507.20321 (2025).
- **Expository/heuristic**: Tandi, Gonzalez-Hendrix and Brown,
  arXiv:2605.20215 (2026), Busy Beaver state counts as a measure of a
  conjecture's difficulty. Weakly relevant.
- **Survey of incompleteness proofs**, including Berry/Kolmogorov proofs:
  Cheng, arXiv:2009.04887 (2020). Cheng is reported (in the part we did not
  read verbatim) to say Kikuchi "replaced truth with provability" in
  Boolos's notion of name; Boolos's own text already uses machine output,
  so the original should be cited directly rather than via Cheng.

We found no Lean, Coq or Isabelle formalization of a Boolos-style naming
function, of Berry-paradox incompleteness via naming, or of an abstract
"no top" theorem for naming schemes. (Gödel's theorems themselves are
formalized in several systems, including the `Foundation` library we use.)
This is a negative search result and should be phrased as "we are not aware
of".

## 4. Bibliography

Status tag: **[read]** read during this survey; **[memory]** standard
reference, details from memory, to be checked; **[listing]** existence and
title confirmed by search listing only.

**Berry paradox and incompleteness**

1. G. Boolos, "A new proof of the Gödel incompleteness theorem", *Notices
   Amer. Math. Soc.* 36(4) (1989), 388–390. [read]
2. M. Kikuchi, "A note on Boolos' proof of the incompleteness theorem",
   *Math. Logic Quarterly* 40 (1994), 528–532. [citation read in two
   independent bibliographies]
3. M. Kikuchi, "Kolmogorov complexity and the second incompleteness
   theorem", *RIMS Kôkyûroku* 912 (1995), 33–42. [read]
4. M. Kikuchi, "Kolmogorov complexity and the second incompleteness
   theorem", *Arch. Math. Logic* 36 (1997), 437–443. [citation read in
   Kritchman–Raz]
5. M. Kikuchi, T. Kurahashi, H. Sakai, "On proofs of the incompleteness
   theorems based on Berry's paradox by Vopěnka, Chaitin, and Boolos",
   *Math. Logic Quarterly* 58(4–5) (2012), 307–316,
   doi:10.1002/malq.201110067. [bibliographic data and abstract read; full
   text not reached]
6. P. Vopěnka, "A new proof on the Gödel's result of non-provability of
   consistency", *Bull. Acad. Polon. Sci.* 14 (1966), 111–116. [citation
   read in Kritchman–Raz]
7. S. Kritchman, R. Raz, "The surprise examination paradox and the second
   incompleteness theorem", *Notices Amer. Math. Soc.* 57(11) (2010).
   arXiv:1011.4974. [read]
8. Y. Cheng, "Current research on Gödel's incompleteness theorems", arXiv:2009.04887
   (2020). [partly read]
9. C. Smoryński, "The incompleteness theorems", in *Handbook of
   Mathematical Logic*, North-Holland 1977, 821–865. [citation read]
10. A. Tarski, A. Mostowski, R. M. Robinson, *Undecidable Theories*,
    North-Holland 1953. [memory]
11. G. Boolos, J. Burgess, R. Jeffrey, *Computability and Logic*, 5th ed.,
    Cambridge 2007. [memory]
12. P. Pudlák, "The lengths of proofs", in *Handbook of Proof Theory*,
    Elsevier 1998. [memory]

**Algorithmic information theory**

13. G. J. Chaitin, "Computational complexity and Gödel's incompleteness
    theorem", *ACM SIGACT News* 9 (1971), 11–12. [citation read]
14. G. J. Chaitin, "Information-theoretic limitations of formal systems",
    *J. ACM* 21 (1974), 403–424. [citation read]
15. G. J. Chaitin, "Computing the Busy Beaver function", in T. M. Cover,
    B. Gopinath (eds.), *Open Problems in Communication and Computation*,
    Springer 1987, 108–112. [citation read]
16. G. J. Chaitin, *Algorithmic Information Theory*, Cambridge 1987.
    [citation read]
17. G. J. Chaitin, A. Arslanov, C. Calude, "Program-size complexity
    computes the halting problem", CDMTCS Research Report 008, Univ.
    Auckland, 1995. [read]
18. M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
    Applications*, 4th ed., Springer 2019. [memory]
19. A. Shen, V. A. Uspensky, N. Vereshchagin, *Kolmogorov Complexity and
    Algorithmic Randomness*, AMS Math. Surveys and Monographs 220, 2017.
    [listing]
20. L. Bienvenu, An. Muchnik, A. Shen, N. Vereshchagin, "Limit complexities
    revisited", arXiv:0802.2833; *Theory Comput. Syst.* (2010). [listing]
21. P. Raatikainen, "On interpreting Chaitin's incompleteness theorem",
    *J. Philos. Logic* 27 (1998), 569–586. [memory]
22. V. Becher, S. Daicz, G. Chaitin, "A highly random number", 2001; V.
    Becher, S. Figueira, A. Nies, S. Picchi, "Program size complexity for
    possibly infinite computations", *Notre Dame J. Formal Logic* 46 (2005).
    [memory]

**Busy Beaver**

23. T. Radó, "On non-computable functions", *Bell System Tech. J.* 41
    (1962), 877–884. [memory]
24. S. Aaronson, "The Busy Beaver Frontier", *ACM SIGACT News* 51(3)
    (2020), 32–54; ECCC TR20-115. [read]
25. A. Yedidia, S. Aaronson, "A relatively small Turing machine whose
    behavior is independent of set theory", *Complex Systems* 25(4) (2016).
    [citation read]
26. P. Michel, "The Busy Beaver competition: a historical survey",
    arXiv:0906.3749. [listing]
27. The bbchallenge Collaboration et al., "Determination of the fifth Busy
    Beaver value", arXiv:2509.12337 (2025; v2 2026). [read]
28. C. Xu, "Skelet #17 and the fifth Busy Beaver number", arXiv:2407.02426
    (2024). [read]
29. G. Lafitte, "Busy beavers gone wild", arXiv:0906.3257 (2009; EPTCS).
    [read]
30. Z. Cao, "More on higher order Busy Beaver functions", arXiv:2507.20321
    (2025). [read]
31. G. Lacerda, "Upper-bounding proof length with the Busy Beaver",
    arXiv:1406.1808 (2014). [read]
32. G. Tandi, J. Gonzalez-Hendrix, J. P. Brown, "Measuring decidability as
    related to Busy Beaver numbers", arXiv:2605.20215 (2026). [read]
33. M. Vielhaber, M. del P. Canales Chacón, S. Jara Ceballos, "Friedman's
    'Long Finite Sequences': the end of the Busy Beaver contest",
    arXiv:2303.02855 (2023). [read; not relevant to our claims]

**Large-number naming**

34. D. Simmons, "Naming the largest number: exploring the boundary between
    mathematics and the philosophy of mathematics", arXiv:1809.08676.
    [partly read]
35. A. Rayo, "Big Number Duel" (vs. A. Elga), MIT, 26 January 2007;
    web.mit.edu/arayo/www/bignums.html; Wikipedia, "Rayo's number". [read
    via Wikipedia]
36. Fish, "Fish number 7", October 2013; Googology Wiki,
    googology.fandom.com/wiki/Fish_number_7. [read]
37. S. Aaronson, "Who can name the bigger number?", 1999 essay. [memory]

## 5. Suggested wording for the public report

> The notion of a formula *naming* a number in a theory is Boolos's (1989),
> who used it to give a Berry-paradox proof of incompleteness. We study the
> associated function `BoolosBig_T(n)`, the largest number named in `T` by
> a formula with at most `n` symbols. Using only standard facts
> (Σ₁-completeness, the least-witness representation of computable
> functions, and proof search) one sees that this function eventually
> dominates every computable function, lies between two Busy Beaver
> functions up to a rescaling of the argument, and so has the same growth
> class for every consistent, computably axiomatized `T` extending basic
> arithmetic. We have not found this stated explicitly in the literature
> and expect it is known to specialists; closely related results are due to
> Chaitin (1974, 1987), Chaitin, Arslanov and Calude (1995), Lafitte (2009)
> and Simmons (2018). Our contribution is a machine-checked proof in Lean
> of the domination and non-computability statements, with an explicit
> logarithmic bound, and an abstract machine-checked form of the
> Berry/Tarski argument that no naming scheme is final.

Avoid in the public report: "new theorem" for Claims 1–3; any suggestion
that `c_T` measures the strength of `T` (see Raatikainen); quoting the ZF
threshold as anything other than "748 states, with smaller claims pending
verification".

## 6. Remaining gaps, in order of value

1. Read Kikuchi, Kurahashi and Sakai (2012) in full. It generalizes
   Boolos's proof and relates it to Chaitin's; it is the most likely place
   for a statement close to Claim 3 or to "Boolos naming relative to any
   `T`".
2. Read Simmons §4–5 and Appendices B, C, E verbatim. His Example 4.5
   reportedly defines a Busy-Beaver-based function, and Appendix E
   discusses near-optimal strategies; a sandwich could be there.
3. Check the Googology Wiki for a provability-based naming function (pages
   on Rayo variants, "Ξ", and community blogs). Not reachable here.
4. Verify the [memory] entries in §4 against the publications.
