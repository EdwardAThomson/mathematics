# Large numbers: what does it cost to name one?

I've been interested in big numbers for a long time. The immediate spark for
this project was two CodeParade videos on the game of "biggest number you
can write in a fixed message length": digits, power towers, Graham's number,
Binary Lambda Calculus, the Bashicu Matrix System, Loader's number, and at
the top of the ladder, Rayo's function. What the videos sparked wasn't the
interest itself but a specific curiosity: how do you specify a big number
*rigorously*, in the smallest amount of space? The bigger numbers in the
game aren't written in digits, they're written in ever more powerful
*notation systems*, and the notation system itself has to be specified
somewhere. So what does that specification cost, and does paying more for it
reliably buy faster growth?

Made precise: fix a reference system R (a grammar plus evaluation rules) and
a symbol budget n. How big a number can you name, and what does the rule-set
itself cost to specify? I call the rule-set's price κ(R) and the reachable
growth `BN(R, n)`; the full formal setup is in
[`BN-function.md`](BN-function.md).

This file is the narrative through-line connecting seventeen notes and two
Lean projects into one story, written so it can be read cold or used to pick
the work back up later.

**The headline results, up front:**

- Pricing κ(R) across six real systems found **no clean compactness law**.
  Turing-complete systems blow up to uncomputable growth almost immediately,
  and only the sub-Turing ordinal ladder shows a real gradient (Part 1).
- Naming 0–6 in bare first-order set theory by *enumerating predecessors*
  costs **10, 30, 128, 403, 1228, 3703, 11128** symbols (roughly 3× per
  step), mechanically proved in Lean. That's the cost of one bad strategy,
  not the minimum: a **successor-chain** naming gets 6 for **388 symbols,
  28.7× cheaper** (Part 2).
- The blowup is a property of the build-each-number-up-from-below strategy
  (and of first-order set theory's austerity), not of numbers themselves.
  Rayo's number gets its real power from **self-reference**, a trick that
  by Tarski isn't even available inside first-order set theory (Part 3).
- Making that self-reference rigorous splits into two forks running the
  *same* naming machine on different fuel: **Boolos's provability-in-PA**
  route is fully mechanized in Lean, sorry-free, and tops out at growth
  class ε₀; **Rayo's own truth-in-V** route transcends every fixed ordinal
  notation, but only holds up given an unstated **Morse-Kelley-strength**
  commitment, and is verified on paper only so far (Part 4).

---

## Part 1: measuring six real systems, no clean law

The first run ([`PLAN.md`](PLAN.md) → [`METHODOLOGY.md`](METHODOLOGY.md) →
[`KAPPA-TABLE.md`](KAPPA-TABLE.md)) priced κ(R) in BLC bits for six systems:
Turing machines, BLC itself, single- and multi-row BMS, System F/CoC, and
first-order set theory (Rayo's family). The question was whether growth rate
scales predictably with that price.

It doesn't; there is **no clean compactness law**. Turing-complete systems
(Busy Beaver, BLC) hit uncomputable growth within a few hundred bits, and
past that point paying more κ buys nothing faster. Only the sub-Turing
ordinal ladder (single-row BMS < multi-row BMS < System F/CoC) shows a real
gradient, and even that is flagged as possibly just the sequence googology
happened to formalize rather than a law. Rayo's own row came back
"infeasible to pin exactly."

One side finding: a live wiki claim that BIG FOOT "beats Rayo's number" was
checked against its own cited proof and found false. BIG FOOT is provably
ill-defined.

---

## Part 2: pricing Rayo's row for real, and what defining each number costs

A follow-up run mechanically proved, in Lean 4, exactly how many symbols
bare first-order set theory needs to name the numbers 0 through 6: no
numerals, no `+`, just membership and logic. The proofs are
[`rayo-lean/Rayo/K0.lean`](rayo-lean/Rayo/K0.lean) through
[`K6.lean`](rayo-lean/Rayo/K6.lean), with
[`RAYO-EXPLAINER.md`](RAYO-EXPLAINER.md) as the plain-English walkthrough.

The answer is **10, 30, 128, 403, 1228, 3703, 11128**, a ratio that settles
to almost exactly 3× per step, forever, because every number's formula has
to embed a full copy of every number before it. κ(R) itself came back a
real, measured 90 lines / 556 Lean tokens. The rule-set is cheap; naming is
what's expensive.

Letting formulas *reuse* each other instead of respelling everything
([`Reuse.lean`](rayo-lean/Rayo/Reuse.lean)) cuts naming 6 to 148/550
symbols (75×/20× cheaper), mechanically confirmed, slightly beating a hand
estimate made first.

**A correction, found later and now verified** (see
[`RAYO-EXPLAINER.md`](RAYO-EXPLAINER.md), "Is enumerate-predecessors the
cheapest strategy?"): the ~3^k table is the cost of one specific bad
strategy, *enumerate every predecessor*, not the minimum. A
**successor-chain** naming (just count up to k, reusing the "successor of"
step each time instead of re-deriving everything) names 6 in **388 symbols,
28.7× cheaper** than `K6.lean`'s 11,128. This is mechanically confirmed in
[`K6Chain.lean`](rayo-lean/Rayo/K6Chain.lean), sorry-free. K0-K6 stay
correct as upper bounds under their own strategy (they never claimed to be
minimal); this narrows how far from minimal they actually were.

**A second correction, caught while building the check above:**
`K0.lean`/`K1.lean` are genuinely `Classical.choice`-free
(`[propext, Quot.sound]` only), but `K2.lean` through `K6.lean` (and
`K6Chain.lean`) do use `Classical.choice`, via `Classical.em` to extract
witnesses from `¬∀¬`-encoded existentials. This project previously stated
"never `Classical.choice`" for all seven files. That was wrong for k ≥ 2,
and is corrected in `RAYO-EXPLAINER.md` with the exact line numbers rather
than left standing.

---

## Part 3: building numbers up is the wrong strategy

The point of this project was never counting for its own sake. It was to
understand how numbers are *defined*, and how compactly they can be
defined. Parts 1-2 answered that for the most austere setting: bare
first-order set theory, building each number up from below. The answer is
that it's expensive, and the expense may say less about numbers than about
first-order set theory itself. The language is minimal (membership and
logic, nothing else) and rigorously correct, and that very austerity is
what makes every definition verbose.

The consequence is stark. Under the enumerate-predecessors table, a
googol-symbol budget defines nothing past k ≈ 210, and even the cheaper
successor chain only buys numbers linear in the budget. No build-it-up
strategy gets anywhere near Rayo's number's reputation.

Rayo's actual construction doesn't build its number up at all. It uses
**self-reference**: a formula that talks about *other formulas* ("the
smallest number no shorter formula can name") to get enormous power in one
shot. And, foreshadowing Part 4: that trick isn't available *inside*
first-order set theory. Evaluating what formulas name requires a truth
predicate that, by Tarski, first-order set theory can't supply for itself.
So Rayo's move is something of a hack, not strictly "allowed" in the system
he's nominally pricing definitions in, even though everyone broadly knows
what he means in a pragmatic way.

K0-K6 measured the cost of the wrong strategy on purpose, to make this gap
visible. [`DIAGONALIZATION-PLAN.md`](DIAGONALIZATION-PLAN.md) scopes what
it would take to verify the real strategy rigorously.

---

## Part 4: two ways to make self-reference rigorous, same machine, different fuel

The **Stage 0 audit**
([`DIAGONALIZATION-STAGE0-FINDINGS.md`](DIAGONALIZATION-STAGE0-FINDINGS.md))
turned up something surprising: nobody has ever formalized Rayo's
construction in a proof assistant, and no fully rigorous end-to-end proof
of it exists in the mainstream literature. His own account is a prose
sketch. (One honest amendment, found by the later [`LADDER.md`](LADDER.md)
audit: the googology community's own technical wing has carefully analyzed
the *well-definedness* half since 2018, reaching the same MK-strength
verdict as R0 below; nothing there is mechanized, and the growth-rate half
remains unproven outside this project.)

Real, usable Lean prior art does exist for the *other* classical route to
self-reference, Gödel/Boolos-style diagonalization:
`FormalizedFormalLogic/Foundation`, sorry-free, built on Mathlib. Two forks
followed from there.

### The Boolos fork: provability, PA-strength

The idea ([`BOOLOS-FUNCTION-PLAN.md`](BOOLOS-FUNCTION-PLAN.md)): swap
"true" for "provable" relative to one fixed theory (PA). Provability,
unlike truth, *is* expressible inside the theory itself (Gödel's own
machinery), so this sidesteps Tarski's undefinability barrier entirely.

- **B0, well-definedness**
  ([`BOOLOS-B0-WELLDEFINEDNESS.md`](BOOLOS-B0-WELLDEFINEDNESS.md)): proved
  on paper *and* machine-checked
  ([`BoolosB0Core.lean`](rayo-lean/Rayo/BoolosB0Core.lean)). This is the
  exact step Rayo's own account skips. It also surfaced a real subtlety:
  formulas must be counted up to variable-renaming or the construction is
  infinite (now `METHODOLOGY.md` C8, project-wide).
- **B1, the naming predicate**
  ([`TNames.lean`](rayo-lean-boolos/RayoBoolos/TNames.lean)): the
  provability-naming predicate formalized as genuine object-language logic,
  sorry-free.
- **B3, domination**
  ([`BOOLOS-B3-PAPER-VERIFICATION.md`](BOOLOS-B3-PAPER-VERIFICATION.md)):
  the paper verification caught a real bug in the draft argument. Naming
  costs `O(n)` symbols, not a fixed constant, so the fix is to pre-inflate
  the target function to `f(n²)` before naming it; squaring avoids
  re-introducing a costly numeral. **Now fully mechanized, sorry-free**
  ([`BoolosBig.lean`](rayo-lean-boolos/RayoBoolos/BoolosBig.lean)):
  `BoolosBig_PA` exists as a real, monotone `ℕ → ℕ` function, and
  `BoolosBig_PA_dominates` proves the literal target,
  `∃ N, ∀ m > N, BoolosBig_PA m ≥ f m` for every PA-provably-total,
  monotone `f`. `#print axioms` on every theorem in the chain shows only
  `[propext, Classical.choice, Quot.sound]`, the project's standard bar for
  Foundation-based work.

  What that theorem actually says, in plain terms: `BoolosBig_PA(m)` is
  *defined* as the biggest number provably nameable within m symbols, so
  "it beats every nameable number" is trivial, like pointing at the
  tallest person in the room. The definition alone doesn't say anyone in
  the room is tall. Part 2 shows that worry is real: if enumerating
  predecessors were the best naming strategy available, the biggest number
  nameable in m symbols would only be ~log(m). The content of the theorem
  is that the room contains giants: for any function f that PA proves
  total, *short* formulas (linear in n) provably name values as huge as
  f(n²), so past a threshold every budget m reaches at least f(m). The
  restriction to PA-provably-total functions is also exactly why this
  rung's growth caps at ε₀.

### The Rayo fork: truth, MK-strength

This fork ([`RAYO-RIGOR-PLAN.md`](RAYO-RIGOR-PLAN.md)) attempts Rayo's own
route directly, with a real, honest chance it just doesn't hold up, per the
plan's own exit conditions.

- **R0, well-definedness**
  ([`RAYO-R0-WELLDEFINEDNESS.md`](RAYO-R0-WELLDEFINEDNESS.md)): the
  construction *is* consistent and does name a specific number, but only
  relative to a commitment the popular description hides. "Satisfies" for
  first-order formulas secretly needs a second-order truth predicate, and
  by Tarski that can't be first-order set theory itself; it needs roughly
  **Morse-Kelley (MK) strength** (independently derived here; later found
  to have precedent in the googology community's technical literature, see
  [`LADDER.md`](LADDER.md) rung 9). Grant that, and Rayo's number is real
  and well-defined. Withhold it, and the construction names nothing.
- **Growth rate, given the commitment**
  ([`RAYO-GROWTH-RATE.md`](RAYO-GROWTH-RATE.md)): using the *same*
  direct-naming-plus-pre-inflation argument as Boolos B3, Rayo eventually
  dominates every ZFC-provably-total function, and by naming ordinals
  intrinsically it climbs *every* fixed ordinal notation in
  `KAPPA-TABLE.md` (ε₀, Buchholz, Γ₀, BMS, System F's PTO) rather than
  sitting at one rung. It strictly transcends the whole definable-total
  class, and unlike Boolos this falls out immediately from Tarski, no
  diagonalization needed. Paper only (Lean was unavailable in that
  session).

### The throughline

Both forks are the *identical* naming schema (`BN(R,n)`'s unique-denotation
machine) running on different fuel. Boolos burns **provability-in-PA**
(Tarski-safe, cheap, fully mechanizable) and tops out at growth class ε₀.
Rayo burns **truth-in-V** (Tarski-forbidden without an extra realist
commitment, only paper-verified so far) and transcends every fixed ordinal
notation there is.

The entire gap between "caps at ε₀" and "beyond everything nameable" traces
to **one variable, the strength of what "names" is allowed to mean**: not a
different mechanism, not a cleverer trick. That is real, sharpened evidence
for Part 1's open question. The jump is a sharp, Tarski-drawn step between
two commitment levels, not a smooth dial you can turn partway.

### Is Rayo's rung the top? (standard theory, not a project result)

No, and it's worth being explicit that this paragraph is inherited from
standard theory rather than verified by this project. The naming game
relativizes: it takes a language plus a notion of naming and returns a
function. Rayo's rung plays it over first-order set theory, with truth
supplied by an MK-strength metatheory (the R0 finding). But that metatheory
is itself a formal language, so the identical game can be played one level
up, and by the same diagonal argument the resulting function eventually
dominates Rayo's. Tarski's hierarchy guarantees there is always a stronger
rung and never a top, so "the biggest number for a given symbol count,
across all systems" has no answer in principle. This project verified
exactly one step of that ladder (PA-provability vs truth-in-V); nothing
above Rayo's rung has been checked here. And climbing carelessly does fail:
BIG FOOT (Part 1) was an attempted higher rung whose language turned out to
be ill-defined.

A concrete example makes the step vivid. The metatheory has the one tool
FOST lacks: a satisfaction predicate `Sat(⌜φ⌝, v)` saying "FOST formula φ
is true of v". With that predicate, "φ names x" and then "Rayo(n)" become
ordinary definitions, so the metatheory can write "x is the successor of
Rayo(10^100)" in a few thousand symbols. By the definition of Rayo's
function, naming that same number in FOST takes more than a googol
symbols. A number costing over 10^100 symbols at level 0 costs about 10^3
one level up, and for barely more you can write Rayo(Rayo(googol)) or
worse. Note what paid for the win: not cleverness, but the assumption that
"true FOST formula" is a determinate notion, the same MK-strength
commitment R0 identified. And the metatheory cannot define *its own*
satisfaction predicate (Tarski again), which is exactly why the game
repeats forever instead of closing.

---

## Status, as of this writing

Settled:

1. **The Boolos fork is done.** B0, B1, and B3 (`BoolosBig_PA_dominates`)
   are all mechanized, sorry-free, matching the project's standard axiom
   bar. It took three rounds to close the last bridging lemma (`fSize`
   under substitution); the eventual fix was a `Foundation` API mismatch
   between two notations for the same connectives, not a real mathematical
   obstacle.
2. **The successor-chain question is answered.** Naming k=6 takes 388
   symbols, 28.7× cheaper than `K6.lean`'s enumerate-predecessors 11,128
   ([`K6Chain.lean`](rayo-lean/Rayo/K6Chain.lean), sorry-free).
3. **The Mathlib/`Foundation` dependency paid off.** It delivered the full
   B3 proof, settling `LAPTOP-HANDOFF.md` Task 3's keep-or-drop question in
   favor of keeping it.

Still open:

4. **Rayo's growth-rate result is paper-only.** No Lean session has had
   toolchain access at the same time as attempting it yet.

---

## Map

| what | where |
|---|---|
| the formal question | [`BN-function.md`](BN-function.md) |
| κ(R) convention, all definitional choices flagged | [`METHODOLOGY.md`](METHODOLOGY.md) |
| the six-system comparison, no compactness law | [`KAPPA-TABLE.md`](KAPPA-TABLE.md) |
| the famous numbers audited rung by rung | [`LADDER.md`](LADDER.md) |
| naming 0-6 in bare FOST, mechanized | [`RAYO-EXPLAINER.md`](RAYO-EXPLAINER.md), [`K0`](rayo-lean/Rayo/K0.lean)–[`K6.lean`](rayo-lean/Rayo/K6.lean) |
| successor-chain naming (388 vs 11,128 symbols) | [`K6Chain.lean`](rayo-lean/Rayo/K6Chain.lean) |
| Gödel-coding formulas as data | [`Encoding.lean`](rayo-lean/Rayo/Encoding.lean) |
| formula reuse / compression, mechanized | [`Reuse.lean`](rayo-lean/Rayo/Reuse.lean), [`ReuseSix.lean`](rayo-lean/Rayo/ReuseSix.lean) |
| B0 core (finite-max fact), mechanized | [`BoolosB0Core.lean`](rayo-lean/Rayo/BoolosB0Core.lean) |
| diagonalization scoping + prior-art audit | [`DIAGONALIZATION-PLAN.md`](DIAGONALIZATION-PLAN.md), [`DIAGONALIZATION-STAGE0-FINDINGS.md`](DIAGONALIZATION-STAGE0-FINDINGS.md) |
| Boolos fork plan / B0 proof / B3 paper-check | [`BOOLOS-FUNCTION-PLAN.md`](BOOLOS-FUNCTION-PLAN.md), [`BOOLOS-B0-WELLDEFINEDNESS.md`](BOOLOS-B0-WELLDEFINEDNESS.md), [`BOOLOS-B3-PAPER-VERIFICATION.md`](BOOLOS-B3-PAPER-VERIFICATION.md) |
| Boolos fork Lean (B1, B3) | [`TNames.lean`](rayo-lean-boolos/RayoBoolos/TNames.lean), [`Domination.lean`](rayo-lean-boolos/RayoBoolos/Domination.lean), [`BoolosBig.lean`](rayo-lean-boolos/RayoBoolos/BoolosBig.lean), [`BOOLOS-B1-B3-REPORT.md`](rayo-lean-boolos/BOOLOS-B1-B3-REPORT.md) |
| Rayo fork plan / R0 / growth rate | [`RAYO-RIGOR-PLAN.md`](RAYO-RIGOR-PLAN.md), [`RAYO-R0-WELLDEFINEDNESS.md`](RAYO-R0-WELLDEFINEDNESS.md), [`RAYO-GROWTH-RATE.md`](RAYO-GROWTH-RATE.md) |
| next Lean steps, precisely scoped | [`LAPTOP-HANDOFF.md`](LAPTOP-HANDOFF.md) |
| dated narrative of every run | `DEVLOG.md` (private repo root, not part of this extract) |
