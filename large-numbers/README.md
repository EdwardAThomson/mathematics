# Large numbers: what does it cost to name one?

Started from two CodeParade videos on "biggest number in a fixed message
length" — digits, power towers, Graham's number, Binary Lambda Calculus, the
Bashicu Matrix System, Loader's number, Rayo's function. The question this
project actually asks, made precise: fix a reference system R (a grammar plus
evaluation rules) and a symbol budget n — how big a number can you name, and
what does the *rule-set itself* cost to specify? Call the budget's price
κ(R) and the reachable growth `BN(R, n)`. Read `BN-function.md` for the full
formal setup; this file is the narrative through-line connecting seventeen
notes and two Lean projects into one story, for reading cold or picking back
up later.

## Part 1 — measuring six real systems, no clean law

`PLAN.md` → `METHODOLOGY.md` → `KAPPA-TABLE.md`: an autonomous plimsoll run
priced κ(R) in BLC bits for Turing machines, BLC itself, single/multi-row
BMS, System F/CoC, and first-order set theory (Rayo's family), and asked
whether growth rate scales predictably with that price. **No clean
compactness law.** Turing-complete systems (Busy Beaver, BLC) hit
uncomputable growth within a few hundred bits — paying more κ buys nothing
faster once you're there. Only the sub-Turing ordinal ladder (single-row BMS
< multi-row BMS < System F/CoC) shows a real gradient, flagged as possibly
just the sequence googology happened to formalize rather than a law. Rayo's
own row came back "infeasible to pin exactly." Along the way: a live wiki
claim (BIG FOOT "beats Rayo's number") was checked against its own cited
proof and found false — BIG FOOT is provably ill-defined.

## Part 2 — pricing Rayo's row for real, and how bad naive counting is

A follow-up run mechanically proved, in Lean 4, exactly how many symbols
bare first-order set theory needs to name the numbers 0 through 6 — no
numerals, no `+`, just membership and logic (`rayo-lean/Rayo/K0.lean`
through `K6.lean`, `RAYO-EXPLAINER.md` for the plain-English walkthrough).
Result: **10, 30, 128, 403, 1228, 3703, 11128** — a ratio that settles to
almost exactly 3× per step, forever, because every number's formula has to
embed a full copy of every number before it. κ(R) itself came back a real,
measured 90 lines / 556 Lean tokens — cheap; naming is what's expensive.
Letting formulas *reuse* each other instead of respelling (`rayo-lean/
Rayo/Reuse.lean`) cuts naming 6 to 148/550 symbols (75×/20× cheaper),
mechanically confirmed, slightly beating a hand estimate made first.

**Correction, found later (`RAYO-GROWTH-RATE.md` §2):** this ~3^k table is
the cost of one specific bad strategy — *enumerate every predecessor* — not
the minimum. A **successor-chain** naming (just count up to k, `O(k)`
symbols) is almost certainly far cheaper, possibly by orders of magnitude at
k=6. Not yet verified in Lean — this is `LAPTOP-HANDOFF.md`'s Task 2, a
self-contained, no-Mathlib check ready to run in `rayo-lean/` whenever
wanted. K0-K6 stay correct as upper bounds either way (never claimed
minimal); this just narrows how far from minimal they are.

## Part 3 — why counting is the wrong question

If naming costs ~3^k forever, a googol-symbol budget only reaches k ≈ 210 —
laughably small next to Rayo's number's reputation. The resolution: Rayo's
actual construction doesn't count up to a target one integer at a time. It
uses **self-reference** — a formula that talks about *other formulas*
("the smallest number no shorter formula can name") to get enormous power in
one shot. K0-K6 measured the cost of the wrong strategy on purpose, to make
this gap visible. `DIAGONALIZATION-PLAN.md` scopes what it would take to
verify the real strategy rigorously.

## Part 4 — two ways to make self-reference rigorous, same machine, different fuel

**Stage 0 audit** (`DIAGONALIZATION-STAGE0-FINDINGS.md`): nobody has ever
formalized Rayo's construction, and — bigger finding — nobody has ever
given it a fully *rigorous* proof at all, informal or mechanized. His own
account is a prose sketch. Real, usable Lean prior art exists for the
*other* classical route to self-reference (Gödel/Boolos-style
diagonalization): `FormalizedFormalLogic/Foundation`, sorry-free, built on
Mathlib. Two forks followed from there.

### The Boolos fork — provability, PA-strength (`BOOLOS-FUNCTION-PLAN.md`)

Swap "true" for "provable" relative to one fixed theory (PA). Provability,
unlike truth, *is* expressible inside the theory itself (Gödel's own
machinery), so this sidesteps Tarski's undefinability barrier entirely.

- **B0** (`BOOLOS-B0-WELLDEFINEDNESS.md`): well-defined, proved on paper
  *and* machine-checked (`rayo-lean/Rayo/BoolosB0Core.lean`) — the exact
  step Rayo's own account skips. Found a real subtlety along the way:
  formulas must be counted up to variable-renaming or the construction is
  infinite (now `METHODOLOGY.md` C8, project-wide).
- **B1** (`rayo-lean-boolos/RayoBoolos/TNames.lean`): the provability-naming
  predicate formalized as genuine object-language logic, sorry-free.
- **B3** (domination): `BOOLOS-B3-PAPER-VERIFICATION.md` fully verifies the
  argument on paper — and catches a real bug: naming costs `O(n)` symbols,
  not a fixed constant, so the fix is to pre-inflate the target function to
  `f(n²)` before naming it (squaring avoids re-introducing a costly numeral
  — the "safe route" `LAPTOP-HANDOFF.md` documents precisely). **Fully
  mechanized, sorry-free**: `BoolosBig_PA` exists as a real, monotone
  `ℕ → ℕ` function (`RayoBoolos/BoolosBig.lean`), and
  `BoolosBig_PA_dominates` proves the literal target —
  `∃ N, ∀ m > N, BoolosBig_PA m ≥ f m` for every PA-provably-total,
  monotone `f` — via the `n²` pre-inflation (`graphSq`, proved to add only
  `O(1)` overhead, no numeral) composed with the `O(n)` numeral bound and
  `Nat.sqrt`. `#print axioms` on every theorem in the chain shows only
  `[propext, Classical.choice, Quot.sound]`, the project's standard bar for
  Foundation-based work.

### The Rayo fork — truth, MK-strength (`RAYO-RIGOR-PLAN.md`)

Attempt Rayo's own route directly: a real, honest chance this just doesn't
hold up, per the plan's own exit conditions.

- **R0** (`RAYO-R0-WELLDEFINEDNESS.md`): it *is* consistent and does name a
  specific number — but only relative to a commitment the popular
  description hides. "Satisfies" for first-order formulas secretly needs a
  second-order truth predicate, and by Tarski that can't be first-order
  set theory itself — it needs roughly **Morse-Kelley (MK) strength**
  (independently checked against the literature). Grant that, and Rayo's
  number is real and well-defined; withhold it and the construction names
  nothing.
- **Growth rate, given the commitment** (`RAYO-GROWTH-RATE.md`): using the
  *same* direct-naming-plus-pre-inflation argument as Boolos B3, Rayo
  eventually dominates every ZFC-provably-total function, and by naming
  ordinals intrinsically it climbs *every* fixed ordinal notation in
  `KAPPA-TABLE.md` (ε₀, Buchholz, Γ₀, BMS, System F's PTO) rather than
  sitting at one rung. It strictly transcends the whole definable-total
  class — and unlike Boolos, this falls out immediately from Tarski, no
  diagonalization needed. Paper only (Lean unavailable in that session).

### The throughline

Both forks are the *identical* naming schema (`BN(R,n)`'s unique-denotation
machine) running on different fuel. Boolos burns **provability-in-PA**
(Tarski-safe, cheap, fully mechanizable) and tops out at growth class ε₀.
Rayo burns **truth-in-V** (Tarski-forbidden without an extra realist
commitment, only paper-verified so far) and transcends every fixed ordinal
notation there is. The entire gap between "caps at ε₀" and "beyond
everything nameable" traces to **one variable — the strength of what
"names" is allowed to mean** — not a different mechanism, not a cleverer
trick. That is real, sharpened evidence for Part 1's open question: the
jump is a sharp, Tarski-drawn step between two commitment levels, not a
smooth dial you can turn partway.

## Open threads, as of this writing

1. **The Boolos fork is done** — B0, B1, and B3 (`BoolosBig_PA_dominates`)
   are all mechanized, sorry-free, matching the project's standard axiom
   bar. Took three rounds to close the last bridging lemma (`fSize` under
   substitution); the eventual fix was a `Foundation` API mismatch between
   two notations for the same connectives, not a real mathematical
   obstacle.
2. **The successor-chain naming check** (`LAPTOP-HANDOFF.md` Task 2) — is
   minimal FOST naming actually `O(k)`, not `~3^k`? Self-contained, no
   Mathlib, ready to run.
3. **The Mathlib/`Foundation` dependency paid off** — it delivered the full
   B3 proof, so `LAPTOP-HANDOFF.md` Task 3's question is settled in favor
   of keeping it. Task 2 (below) doesn't need it regardless.
4. **Rayo's growth-rate result is paper-only** — no Lean session has had
   toolchain access at the same time as attempting it yet.

## Map

| what | where |
|---|---|
| the formal question | `BN-function.md` |
| κ(R) convention, all definitional choices flagged | `METHODOLOGY.md` |
| the six-system comparison, no compactness law | `KAPPA-TABLE.md` |
| naming 0-6 in bare FOST, mechanized | `RAYO-EXPLAINER.md`, `rayo-lean/Rayo/K0-K6.lean` |
| Gödel-coding formulas as data | `rayo-lean/Rayo/Encoding.lean` |
| formula reuse / compression, mechanized | `rayo-lean/Rayo/Reuse.lean`, `ReuseSix.lean` |
| B0 core (finite-max fact), mechanized | `rayo-lean/Rayo/BoolosB0Core.lean` |
| diagonalization scoping + prior-art audit | `DIAGONALIZATION-PLAN.md`, `DIAGONALIZATION-STAGE0-FINDINGS.md` |
| Boolos fork plan / B0 proof / B3 paper-check | `BOOLOS-FUNCTION-PLAN.md`, `BOOLOS-B0-WELLDEFINEDNESS.md`, `BOOLOS-B3-PAPER-VERIFICATION.md` |
| Boolos fork Lean (B1, B3) | `rayo-lean-boolos/RayoBoolos/{TNames,Domination,BoolosBig}.lean`, `BOOLOS-B1-B3-REPORT.md` |
| Rayo fork plan / R0 / growth rate | `RAYO-RIGOR-PLAN.md`, `RAYO-R0-WELLDEFINEDNESS.md`, `RAYO-GROWTH-RATE.md` |
| next Lean steps, precisely scoped | `LAPTOP-HANDOFF.md` |
| dated narrative of every run | `DEVLOG.md` (repo root) |
