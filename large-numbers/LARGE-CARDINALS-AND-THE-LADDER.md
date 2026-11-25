# Levels of infinity and the naming ladder

Written 2026-11-24, in answer to the question "are the various levels of
infinity another ladder, and how does it compare to ours?" It places the
infinite cardinals, and in particular the large cardinals, against the rungs
of `THE-LADDER.md`, using the cost measures of `ASSUMPTION-COST-SCALE.md`.

Tags as in the rest of the project: **[Lean]** machine-checked here,
**[paper]** argued here or in another note of this project and not
independently checked, **[classical]** a known result cited from the
literature (from memory unless a source is named), **[expected]** believed
true but neither proved here nor checked against a source. Nothing in this
note is machine-checked or new mathematics, except where it cites the
project's own Lean results. What it offers is the comparison.

## 0. The answer in plain language

**Yes, the infinities form a ladder, and like ours it has no top. But it
measures something else, so the two ladders mostly run side by side rather
than one inside the other.**

- **The infinity ladder measures size.** It runs ℵ₀ (the whole numbers),
  ℵ₁, ℵ₂, … and then the large cardinals: inaccessible, Mahlo, weakly
  compact, measurable, Woodin, supercompact, rank-into-rank. Each large
  cardinal is an *axiom*: "an infinity this big exists". Its strength is
  measured by which other such axioms it proves consistent.
- **Our ladder measures how much truth a naming rule consults.** A rung is
  set by the kind of question whose answers you treat as given: does this
  program halt, is this statement about numbers true, is this statement about
  sets of numbers true, is this statement about all sets true.

A large-cardinal axiom never moves a naming scheme to a higher rung. It acts
in two other ways, at two different heights of our ladder:

1. **At the bottom (rung 0), it lets you prove that more computations
   finish.** A theory with a stronger large cardinal proves more computable
   functions total, so it certifies faster-growing *computable* functions.
   A real example: a function built from the Laver tables, a purely finite
   construction, is known to be defined for every input only if one assumes a
   rank-into-rank cardinal, almost the strongest large cardinal there is.
   This is the "ordinal" coordinate of `ASSUMPTION-COST-SCALE.md`.
   **It buys nothing at rung 1:** the largest number a theory can *provably*
   name in `n` symbols grows like Busy Beaver whether the theory is
   arithmetic or set theory with any large cardinals. Stronger axioms shift
   the input by at most about `n log n`. **[Lean]**
2. **Higher up (statements about sets of numbers, from three blocks of set
   quantifiers on), it makes the named numbers definite.** There, which
   number a formula names can change from one universe of sets to another.
   Large cardinals (Woodin cardinals) freeze those answers: once they are
   assumed, no forcing construction can change any statement about sets of
   numbers. That is the main thing large cardinals do for our ladder. It
   lowers the price in the "what must be accepted" column without changing
   the growth column.

Two more points of contact:

3. **Questions about the sizes themselves** (the continuum hypothesis: is the
   number of sets of whole numbers ℵ₁?) are statements about sets of sets of
   numbers. They sit on the third-order rungs, below Rayo's, and they are the
   first place where large cardinals stop helping: no known large cardinal
   settles the continuum hypothesis.
4. **Large cardinals first appear *inside* the domain at Rayo's rung**,
   whose formulas range over all sets. They also cast countable "shadows"
   all the way down: the ordinal notations that measure rung 0 are built
   from symbols for an uncountable cardinal, an inaccessible, a Mahlo
   cardinal and so on, collapsed to countable ordinals.

So: the size ladder does not give us new rungs. It gives us, at the bottom,
stronger guarantees that computations finish, and in the middle, a way to
make the second-order rungs' numbers definite. Above the projective level it
gives nothing that is known.

### What this corrects in the first-pass answer

The answer posted in the project chat was right in outline. Four
corrections:

- "A theory with them can prove that more programs halt, so its naming
  function is larger … a bigger number within a rung." For *provable naming*
  this is true only at a fixed small input. The growth class does not change
  at all, not even within the rung (§2.2). The "bigger within a rung" effect
  is real for the *computable functions a theory proves total* (§2.1), which
  are on rung 0, not rung 1.
- "Every theory built from them still sits under Busy Beaver." The
  provably total functions sit under Busy Beaver. The provable naming
  function of such a theory is *equal* to Busy Beaver in growth class.
- "Large cardinals … never past Busy Beaver" is true for growth, but large
  cardinals do act on the higher rungs, through absoluteness and determinacy
  (§2.3). That is the main point of contact the first answer missed.
- "CH … near Rayo's rung." It sits lower: CH is a third-order statement
  (§2.4).

## 1. Two ladders and what each measures

### 1.1 The size ladder

Cardinals measure the size of sets. ZFC proves there are infinitely many
infinite sizes, ℵ₀ < ℵ₁ < ℵ₂ < … < ℵ_ω < …, and proves that for every
cardinal there is a bigger one, so there is no top. **[classical: Cantor]**

Large cardinals are sizes whose existence ZFC cannot prove: if ZFC proved
that an inaccessible exists, ZFC would prove its own consistency. **[classical:
Gödel's second theorem, since `V_κ ⊨ ZFC` for `κ` inaccessible]** Each is
added as a new axiom. Remarkably, the natural ones line up in a single
order of *consistency strength*: for the usual axioms `A`, `B`, either
`ZFC + A` proves `ZFC + B` consistent, or the reverse, or they are
equiconsistent. This linearity is observed, not proved. **[classical,
as an empirical observation; Kanamori, *The Higher Infinite*]**

The ladder also has a wall at the top. Reinhardt cardinals, the natural
next step after rank-into-rank cardinals, contradict the axiom of choice
(Kunen 1971). **[classical]** That plays the role of our BIG FOOT: an attempt
to climb one step too far that defines nothing.

### 1.2 Our ladder

A rung is set by what "names" means (`THE-LADDER.md` §2): evaluation (rung 0),
halting or provability (rung 1), halting with oracles or truth of formulas
with `k` quantifier blocks (rung `k`), all arithmetic truth (rung ω), truth
with set quantifiers (`SECOND-ORDER-RUNGS.md`), truth for all of set theory
(Rayo), and truth-predicate extensions above that. Its steps are made by
adding the truth notion of the current language as a new primitive, and
there is no top (Claims A and B, **[Lean]** in `rayo-lean/Rayo/NoTop.lean`).

### 1.3 Where the two touch: the sizes of the domains

There is one crude alignment. Each family of rungs is about a domain of a
certain size:

| rungs | quantifiers range over | size of the domain |
|---|---|---|
| 0 to ω | whole numbers | ℵ₀ = ℶ₀ |
| second-order (`Σ¹_k`, `Π¹_k`) | sets of whole numbers | 2^ℵ₀ = ℶ₁ |
| third-order | sets of sets of numbers | ℶ₂ |
| `n`-th order | | ℶ_{n−1} |
| Rayo | all sets | no size: a proper class |

**[classical for the sizes; the table is ours]** So the big families of
rungs follow the *beth* numbers ℶ (iterated power sets), not the ℵ numbers,
and only the bottom of the beth ladder. The finer rungs inside a family
come from quantifier alternations, which have nothing to do with size.
Every large cardinal is far above every ℶ_n with `n` finite, so large
cardinals are inside the domain only at Rayo's rung.

That is why the two ladders mostly run side by side. What connects them is
not size but *proof strength* and *absoluteness*, as follows.

## 2. What large cardinals do on each part of our ladder

### 2.1 Rung 0: they prove more computations finish

A computable naming scheme is well defined once you believe its evaluation
always terminates. `ASSUMPTION-COST-SCALE.md` prices that belief by the
proof-theoretic ordinal of the weakest theory proving it (the second
coordinate `ord(R)`).

Large cardinals extend that scale far beyond where ordinal analysis has
reached.

- **Stronger axiom, more provably total functions.** If `T` proves that `S`
  is `Σ₁`-sound (every `Σ₁` sentence `S` proves is true), then `T` proves
  total a computable function that eventually dominates every function `S`
  proves total. **[classical: Kreisel]** For large cardinals this applies
  directly: `ZFC + "κ is inaccessible"` proves `V_κ ⊨ ZFC`, hence that ZFC is
  sound for arithmetic. Each standard step up the large-cardinal ladder
  proves the step below it sound in this way. **[classical]** So the
  large-cardinal ladder gives a strictly increasing chain of classes of
  certified computable functions.
- **A concrete function that needs a very large cardinal: the Laver
  tables.** For each `n` there is a unique operation `⋆` on
  `{1, …, 2ⁿ}` with `a ⋆ 1 = a + 1 (mod 2ⁿ)` and
  `a ⋆ (b ⋆ c) = (a ⋆ b) ⋆ (a ⋆ c)`. It is finite and computable. Laver
  proved, assuming a rank-into-rank (I3) cardinal, that the period of the
  row of `1` tends to infinity with `n`. So
  `g(k) := the least n at which that period is at least 2^k` is total,
  given I3. Whether ZFC (or even primitive recursive arithmetic) proves `g`
  total is open. Dougherty showed `g` grows so fast that `g(5)` exceeds an
  Ackermann-type tower, `A(9, A(8, A(8, 254)))`. **[classical: Laver 1995;
  Dougherty 1993; Drápal]** This is a rung-0 function whose only known
  totality proof sits near the top of the large-cardinal ladder.
- **Friedman's finite combinatorics.** Harvey Friedman has given explicit
  statements about finite functions on integers that are provable from
  Mahlo cardinals of every finite order but not from ZFC
  (*Boolean Relation Theory*), and others calibrated against subtle
  cardinals. **[classical, from memory; not checked here]**

What is *not* known: where any of this sits on the fast-growing hierarchy.
Ordinal analysis has been carried out up to roughly `Π¹₂-CA₀` (Rathjen,
Arai); the proof-theoretic ordinal of ZFC, let alone of ZFC with an
inaccessible, has no known notation. **[classical]** So on rung 0 the large
cardinals continue the ordinal scale past where anyone can write it down,
ordered by consistency strength instead of by an ordinal.

**Countable shadows.** The ordinal notations that *do* exist are built from
large cardinals. Rathjen's collapsing functions use a symbol `Ω` for an
uncountable cardinal, `I` for an inaccessible, `M` for a Mahlo, `K` for a
weakly compact, and collapse terms in these symbols to countable ordinals.
`ψ(ε_{I+1})` is the ordinal of `KPi` (recursively inaccessible sets),
`ψ(ε_{M+1})` that of `KPM` (recursively Mahlo), and a weakly compact gives
`Π₃`-reflection. **[classical: Jäger and Pohlers; Rathjen 1990, 1994]** So the
large-cardinal ladder is copied, in miniature, inside rung 0, where it
measures termination strength. The same copy shows up one rung higher:
ω₁^CK, the least ordinal not computable as a well-ordering of ℕ, is the
"computable ℵ₁". It is the height of the hyperarithmetic hierarchy, so it
is exactly the length of the oracle hierarchy that the `Π¹₁` rung
diagonalizes over (`SECOND-ORDER-RUNGS.md`, Theorem 3). **[classical for
ω₁^CK; the reading is ours]**

### 2.2 Rung 1: they buy nothing

For any consistent, computably axiomatized theory `T` extending a little
arithmetic, the largest number `T` provably names in `n` symbols is
Busy Beaver class, with constants that do not depend on `T`:

- lower bound, uniform in `T`: `BB_le_BoolosBigIn`,
  `BoolosBigIn_partrec_bound` in `RayoBoolos/BusyBeaver.lean` **[Lean]**;
- upper bound, comparing any two theories: `BoolosBigIn_le_any` in
  `RayoBoolos/UpperBound.lean`, with the explicit `n log n` rescaling in
  `RayoBoolos/CompactCode.lean` **[Lean]**.

`ZFC + "there is a proper class of Woodin cardinals"`, or
`ZFC + I3`, is such a theory. So passing from PA to the strongest large
cardinals stretches the input by at most an `n log n` factor plus a constant
(`BOOLOS-IS-BUSY-BEAVER-CLASS.md` Corollary 4). The constant can be very
large at small `n`: a large-cardinal theory can name, with a short formula,
a number whose shortest PA name is long (for instance, a Laver-table value
it proves exists). It cannot change the growth class. The reason is the one
in `THE-LADDER.md`: arithmetic can already name the halting time of the
program that searches the large-cardinal theory's proofs.

This is the first coordinate `deg(R)` of `ASSUMPTION-COST-SCALE.md` in
action. Every computably axiomatized theory has degree `0′` there, so
consistency strength, however large, cannot raise it.

Even the *existence* of these numbers costs nothing that large cardinals
supply: `IΣ₁` proves "`BoolosBig_T(n)` exists for every `n`" for every
such `T` (`ASSUMPTION-COST-SCALE.md` §2). **[expected]**

### 2.3 Second-order rungs: they make the numbers definite

Here large cardinals matter for our ladder, in the "must accept" column.

**The issue.** The rung for `Σ¹_k` naming is Busy Beaver over `Δ¹_k`
oracles (`SECOND-ORDER-RUNGS.md` Theorem 3). That theorem is proved in ZFC,
so it holds in any universe of sets. But the function `N_{Σ¹_k}` it talks
about is computed from truth in that universe's `𝒫(ℕ)`. For `k ≤ 2` this
truth is the same in every universe (Mostowski, Shoenfield). From `k = 3`
on it can differ. For example "`0#` exists" is a `Σ¹₃` sentence, false in
Gödel's universe `L` and true in a universe with a measurable cardinal.
**[classical]** So a formula like "`x` is the large number `B` if `0#`
exists, and `x = 0` otherwise" names different numbers in different
universes. Whether the *record* `N_{Σ¹₃}(n)` itself changes is a separate
question; we know no argument either way. **[open]**

`SECOND-ORDER-RUNGS.md` §7 and `ASSUMPTION-COST-SCALE.md` §2 concluded
that from `Σ¹₃` on one must accept a single intended `𝒫(ℕ)`.

**What large cardinals do.** They pin projective truth down against
forcing, the standard method for building different universes.

| assumption | effect on second-order truth | source |
|---|---|---|
| none (ZFC) | `Σ¹₁`, `Π¹₁`, `Σ¹₂`, `Π¹₂` truth the same in every universe with the same ordinals | Mostowski, Shoenfield **[classical]** |
| every set has a sharp (follows from a measurable cardinal) | `Σ¹₃` truth unchanged by set forcing; `Σ¹₁` games determined | Martin–Solovay 1969; Martin 1970; Harrington 1978 for the converse on determinacy **[classical]** |
| `n` Woodin cardinals with a measurable above | `Π¹_{n+1}` games determined | Martin–Steel 1989 **[classical]** |
| infinitely many Woodin cardinals (with a measurable above) | projective determinacy; every projective statement unchanged by set forcing; indeed the whole theory of `L(ℝ)` | Woodin **[classical]** |

So the `Σ¹_k` rungs (`k ≥ 3`) split two ways in what they cost:

- **Without large cardinals,** the values are definite only if one accepts
  a single intended `𝒫(ℕ)` by fiat.
- **With infinitely many Woodin cardinals and a measurable above them,**
  every second-order sentence,
  hence every naming formula of second-order arithmetic, has the same truth
  value in every set-forcing extension. **[classical; the application to
  naming is ours]** Under projective determinacy the second-order rungs
  also acquire the rich structure theory of descriptive set theory: for
  example `Π¹₃` behaves like `Π¹₁`, with its own analogue of Kleene's `O`.
  **[classical: Moschovakis, *Descriptive Set Theory*, ch. 6]** One would
  expect the `BB^O` overshoot of `SECOND-ORDER-RUNGS.md` Theorem 4(d) to
  repeat at each odd level. **[expected; not worked out]**

This does not make the values absolute in every sense. `L` itself has no
measurable cardinal, and the values computed in `L` can differ. The
large-cardinal route trades one commitment (a single intended `𝒫(ℕ)`) for
another (these large cardinals exist), which most set theorists regard as
better justified because the large cardinals are mutually consistent and
settle so much at once. That is the content of Woodin's programme, and it
is a philosophical judgement, not a theorem. **[classical as a description
of the field]**

**Growth is unchanged.** None of this moves a rung. Within any fixed
universe, the comparisons of `SECOND-ORDER-RUNGS.md` §4 hold as stated.
Large cardinals change which universe you are in, or how many universes
agree, not which rung beats which.

### 2.4 Third-order rungs and the continuum hypothesis

The continuum hypothesis says that every set of reals is countable or the
same size as ℝ. It quantifies over sets of reals, so it is a statement of
third-order arithmetic (it is `Σ²₁`). **[classical]** So CH is a statement
on the third-order rungs, below Rayo's rung, not near it.

Here large cardinals stop helping. Small forcing preserves every standard
large cardinal, and CH can be switched on or off by small forcing, so no
standard large cardinal decides CH. **[classical: Lévy–Solovay 1967]**
Consequently the third-order naming relation depends on the universe in a
way no known large cardinal removes: "`x = B` if CH, else `x = 0`" names `B`
in some universes with a supercompact cardinal and `0` in others.
**[classical ingredients; the example is ours]** There is a partial result:
with a proper class of measurable Woodin cardinals, every `Σ²₁` statement
that can be forced together with CH holds in every forcing extension where
CH holds. **[classical: Woodin's `Σ²₁` absoluteness theorem]** That pins the
third-order truth only after CH itself has been decided.

So in the "must accept" column there is a new boundary on our ladder,
visible only once large cardinals are considered:

| rungs | definite without extra axioms? | definite given large cardinals? |
|---|---|---|
| 0 to `Σ¹₂` | yes (absolute) | yes |
| `Σ¹₃` and the rest of second-order | no | yes, against forcing (Woodin cardinals) |
| third-order, starting with CH | no | no (Lévy–Solovay) |
| Rayo | no | no |

**[classical ingredients; the table is ours]**

### 2.5 Rayo's rung: large cardinals inside the domain

Rayo's formulas quantify over every set, so they can talk about large
cardinals directly. Three consequences.

- **The cost of defining Rayo's function lies between ZFC and one
  inaccessible.** `RAYO-R0-WELLDEFINEDNESS.md` showed that Morse–Kelley class
  theory (MK) defines Rayo's function, and that plain ZFC does not. MK
  proves `Con(ZFC)`, so it is stronger than ZFC. If `κ` is inaccessible, then
  `V_κ` together with its subsets is a model of MK, so MK is weaker than one
  inaccessible. **[classical]** Defining Rayo's function costs more than ZFC
  and less than the first large cardinal.
- **An inaccessible collapses a whole stretch of the ladder.** If `κ` is
  inaccessible, truth for `V_κ` is a set, definable in `V` by a formula that
  mentions "the least inaccessible". So Rayo's function computed in the small
  universe `V_κ`, and every truth-predicate extension of it of the kind
  listed above Rayo in `THE-LADDER.md`, is definable by one formula of set
  theory in `V`. By Claim B, `V`'s own Rayo function beats all of them.
  **[expected; follows the `THE-LADDER.md` §3 argument]** This mirrors how
  the next large cardinal makes the previous one's universe into a set.
  Both ladders climb by the same move: treat everything so far as a finished
  object and talk about it from outside.
- **Large cardinals do not make Rayo's function universe-independent.**
  Rayo's formulas can express CH, so the naming relation varies between
  universes that agree on every large cardinal (§2.4). Whether the record
  `Rayo(n)` itself varies is open, as at `Σ¹₃`. **[open]**

## 3. Where specific large cardinals land

Ordered by consistency strength, weakest first. "Rung 0" says what each
certifies about computable functions. "Second-order rungs" says what it
makes definite. "Countable shadow" is its analogue among countable ordinals,
where one is standard.

| axiom | rung 0: certifies | second-order rungs: makes definite | countable shadow | status |
|---|---|---|---|---|
| ZFC (no large cardinal) | everything ZFC proves total; ordinal of ZFC unknown | `Σ¹₂` and below, absolutely | ω₁^CK as the "computable ℵ₁", height of the `Π¹₁` rung | [classical] |
| worldly / inaccessible | functions dominating every ZFC-provably total function (via `Con`, soundness of ZFC) | nothing new | recursively inaccessible; `ψ(ε_{I+1})`, ordinal of `KPi` | [classical] |
| Mahlo; Mahlo of every finite order | Friedman's Boolean relation theory statements | nothing new | recursively Mahlo; `ψ(ε_{M+1})`, ordinal of `KPM` | [classical] |
| weakly compact | more of the same | nothing new | `Π₃`-reflection; Rathjen's `K` | [classical] |
| subtle, ineffable | Friedman's calibrated finite statements | nothing new | | [classical, not checked] |
| `0#` exists / every set has a sharp (from a measurable) | more of the same | `Σ¹₃` truth fixed under forcing; `Σ¹₁` determinacy | | [classical] |
| measurable | more of the same | as above, and `V ≠ L` | | [classical] |
| `n` Woodin cardinals with a measurable above | more of the same | `Π¹_{n+1}` determinacy | | [classical] |
| infinitely many Woodin cardinals | more of the same | all projective truth fixed under forcing; projective determinacy; the theory of `L(ℝ)` fixed | | [classical] |
| proper class of measurable Woodins | more of the same | `Σ²₁` truth fixed among universes with CH; CH itself still open | | [classical] |
| supercompact | more of the same | nothing further on CH (Lévy–Solovay); consistency of forcing axioms such as PFA, which do decide 2^ℵ₀ = ℵ₂ | | [classical] |
| rank-into-rank (I3) | totality of the Laver-table function `g` (§2.1), not known from anything weaker | | | [classical] |
| Reinhardt | inconsistent with the axiom of choice (Kunen): the wall | | | [classical] |

For every row, provable naming stays Busy Beaver class (§2.2) **[Lean]**,
and Rayo's function eventually beats anything the axiom lets one define
(§2.5) **[paper]**.

## 4. The two ladders side by side

| | size ladder | naming ladder |
|---|---|---|
| a step is | a larger infinity whose existence is assumed | a larger body of truth taken as definite |
| how a step is made | treat the universe so far as a set (reflection) | treat the truth of the language so far as a primitive |
| measured by | consistency strength | growth class of the naming function |
| top? | none; Kunen's wall stops one natural route | none; Claims A and B **[Lean]** |
| ill-defined overreach | Reinhardt cardinals with choice | BIG FOOT |
| effect on the other ladder | rung 0: certifies faster computable functions; second-order rungs: fixes truth | the first time any large cardinal is in the domain is Rayo's rung |

The shared move in the second row is not a coincidence. An inaccessible
`κ` gives a set-sized model `V_κ` of everything below it, and with it a
truth predicate for that model, which is exactly our ladder's step. **[the
analogy is ours; the facts behind it are classical]** The difference is
in what is measured. Our ladder asks how fast the named numbers grow, and
there a truth predicate is a whole new rung. The size ladder asks what can
be proved consistent, and there the same truth predicate is a small part
of one step.

## 5. Open items

1. Whether `N_{Σ¹₃}(n)`, or `Rayo(n)`, actually takes different values in
   different universes, as opposed to individual formulas naming different
   numbers (§2.3, §2.5).
2. Under projective determinacy, work out the odd-level analogue of the
   `BB^O` overshoot (`SECOND-ORDER-RUNGS.md` Theorem 4(d)) at `Π¹₃`.
3. Check the Friedman and Laver-table citations against sources, and find
   whether any rung-0 function is known whose totality is *equivalent* to a
   specific large-cardinal consistency statement.
4. Make the §2.5 claim precise: which truth-predicate extensions of Rayo's
   function over `V_κ` are definable in `V`, given `κ` inaccessible.

## 6. Is this known?

The large-cardinal facts are standard (Kanamori, *The Higher Infinite*;
Moschovakis, *Descriptive Set Theory*; Woodin's and Martin–Steel's work on
determinacy and absoluteness; Laver and Dougherty on Laver tables; Rathjen on
ordinal notations from large cardinals). Popular googology accounts mention
large cardinals mainly through ordinal collapsing functions, that is, the
countable shadows of §2.1. We did not search specifically for a statement
connecting large-cardinal absoluteness to naming functions; given how
direct it is, it may well be folklore. Not searched in this pass.
