# How fast does Rayo(n) grow? A paper analysis

The growth-rate half of the Rayo fork, which `RAYO-R0-WELLDEFINEDNESS.md`
explicitly left open (its §8: "resolves well-definedness only, not growth
rate"). Companion to `BOOLOS-B3-PAPER-VERIFICATION.md`, which did the same job
for the Boolos fork. Paper only (no Lean; toolchain egress-blocked here per
`BOOLOS-B0-WELLDEFINEDNESS.md` §7). **Everything below is conditional on R0's
well-definedness commitment** — the impredicative/MK truth predicate for V. If
that is withheld, `Rayo(n)` trivializes (R0 §4) and "growth rate" is moot; so
throughout, assume `V ⊨ ZFC` and the MK satisfaction class exists (R0's realist
reading).

**Bottom line.** `Rayo` **eventually dominates every function that is total and
definable in V** — in particular every ZFC-provably-total function (§2), and via
intrinsic ordinal definitions it passes the fast-growing hierarchy at *every
fixed ordinal notation* — ε₀, the Buchholz ordinal, Γ₀, the proof-theoretic
ordinals of BMS and System F — which is exactly *why* it dominates the ordinal
and type-theory systems in `KAPPA-TABLE.md` (§3). It is itself **not**
definable-total, so it strictly transcends that whole class, and — unlike
Boolos's fork — this transcendence is immediate from Tarski, no diagonalization
needed (§4). The honest ceiling: **no single proof-theoretic ordinal
characterizes `Rayo`** — its growth is tied to truth-in-V and outruns every
fixed ordinal notation (§5). The gap between Boolos's ε₀ and Rayo's
above-every-notation is due **entirely to the strength of the naming predicate**
(provability-in-PA vs truth-in-V), not to a different naming mechanism — which
sharpens the `KAPPA-TABLE.md` diagonalization-family finding.

**Plain-English version.** Rayo's number grows faster than any function ordinary
mathematics (even all of ZFC set theory) can prove will always finish — and then
keeps going, past every "named" level of infinity mathematicians have a notation
for. The reason is simple once you see it: to describe a huge number, a short
set-theory formula can just *point at* an enormous mathematical object directly,
and set theory has unimaginably large objects to point at. The catch (the thing
that makes it Rayo and not something tamer) is that "which number does this
formula describe" secretly relies on a notion of mathematical truth that set
theory can't define about itself — the exact commitment the R0 note pinned down.
So the growth is real and enormous, but it rides on that commitment.

---

## 1. The question, and what R0 leaves open

From `RAYO-R0-WELLDEFINEDNESS.md` §1: `Rayo(n) = 1 + sup{ m : some one-free-
variable first-order set-theory formula φ, |φ| ≤ n, names m }`, where "names" is
truth-in-V unique denotation. R0 showed this is well-defined given the MK
commitment. The remaining question is **how fast `Rayo` grows as a function of
`n`** — two directions:

- **Lower (domination):** which functions does `Rayo` eventually exceed?
- **Upper (transcendence):** is `Rayo` itself in the class it dominates, or
  strictly beyond it?

Both have clean answers.

---

## 2. Lower bound: Rayo dominates every function total-and-definable in V

The argument is the direct-naming route of `BOOLOS-B3-PAPER-VERIFICATION.md` §2,
transported to set theory. Let `f : ℕ → ℕ` have a set-theory graph formula
`γ_f(y, x)` (fixed size `c_f`, independent of `n`) with `V ⊨ ∀x ∃!y γ_f(y, x)`
and `V ⊨ γ_f(f(k), k)` for all `k` (von Neumann numerals). For each `k`:

1. **Name the input `k`.** A **successor chain** names `k` in `O(k)` symbols:
   ```
     χ_k(z) :≡ ∃w₀…w_{k-1} ( "w₀ = ∅" ∧ "w₁ = w₀∪{w₀}" ∧ … ∧ "z = w_{k-1}∪{w_{k-1}}" )
   ```
   each clause `"a = b∪{b}"` being `∀t(t∈a ↔ (t∈b ∨ t=b))`, a fixed `O(1)`
   block; `k` of them chained is `O(k)` symbols, and the chain pins `z` to the
   von Neumann `k` uniquely.
2. **Name `f(k)`.** Compose: `φ_k(y) :≡ ∃z( χ_k(z) ∧ γ_f(y, z) )`, one free
   variable `y`, size `c_f + O(k)`. Since `f` is total-functional in V, `φ_k`
   names `f(k)`: `V ⊨ ∀y(φ_k(y) ↔ y = f(k))`.

So `Rayo(c_f + a·k) ≥ f(k)` for a constant `a` (the successor-chain's per-step
cost). This is **linear in `k`, the same shape as Boolos's `O(n)` numeral**, and
the same repair applies (`BOOLOS-B3-PAPER-VERIFICATION.md` §3): run the argument
on the pre-inflated `F(k) := f(k²)` — total-and-definable whenever `f` is, graph
size `c_f + O(1)`, no large constant — to absorb the linear factor. Then for `m
= c_f + a·k`, `Rayo(m) ≥ f(k²) ≥ f(m)` for all large `m`. Hence:

> **`Rayo` eventually dominates every function total and definable in V.**

Every **ZFC-provably-total** function is such a function: it has a Σ₁ graph, and
if `V ⊨ ZFC` then its totality (a ZFC theorem) holds in V. So `Rayo` eventually
dominates every ZFC-provably-total function — and, by the same argument with any
sound stronger theory `T` (`V ⊨ T`), every `T`-provably-total function too.

> **A correction I owe, and a flagged side-observation.** Earlier in this
> project's discussion I said the input-naming cost in FOST was the `~3ᵏ`
> K0–K6 blow-up. That is the cost of the *enumerate-predecessors* strategy, not
> the cheapest: the successor chain above is `O(k)`. This does not touch K0–K6's
> results (they are exhibited upper bounds, "never claimed minimal" —
> `RAYO-EXPLAINER.md`), but it does mean the *minimal* naming cost `n_k` is `O(k)`
> or below, far under the enumerate-predecessors `~3ᵏ`. Whether `n_k` is
> genuinely `Θ(k)` or cheaper (e.g. `O(log k)` via inline-definable arithmetic)
> is open (`rayo-notes/literature-notes.md` found nothing citable on minimal
> `n_k`), and reconciling the successor-chain cost against the K0–K6 table's
> `~3ᵏ` growth is worth a dedicated look — flagged here, not resolved, and not
> load-bearing for this note (any `O(k)`-or-below bound makes the domination go
> through).
>
> **Update: now checked, at k = 6.** `rayo-lean/Rayo/K6Chain.lean` mechanizes
> exactly the successor-chain formula sketched above for k = 6, proves it names
> 6 (sorry-free, same `Formula`/`Sat` machinery and correctness-statement shape
> as `K6.lean`'s own `phi6_names_six`), and counts it under the project's frozen
> symbol convention: **388** symbols, against `K6.lean`'s enumerate-predecessors
> `n_6 = 11,128` — about **28.7× shorter**, in the low-hundreds range this
> note's `O(k)` prediction called for, not the low thousands. Detail and the
> full derivation are in `RAYO-EXPLAINER.md`'s "Is enumerate-predecessors the
> cheapest strategy?" section and `K6Chain.lean`'s header. This confirms `n_6`
> (and, by the same construction scaled to any `k`, `n_k`) is `O(k)` or below;
> whether it is the *true minimum* (versus, say, an `O(log k)` construction) is
> still open.

---

## 3. How far: past every fixed ordinal notation

Domination (§2) is via naming `f` at an input; a second route shows *how high*
`Rayo` reaches, by naming huge numbers **intrinsically**, with no input to
encode. The fast-growing hierarchy `f_α` is definable by a fixed set-theory
formula `Φ(y, a, k)` ("`y = f_a(k)`") over any definable system of ordinal
notations. For an ordinal `α` with a defining formula `δ_α` of size `s_α`, the
formula
```
    "y = f_α(k₀)" :≡ ∃a( δ_α(a) ∧ Φ(y, a, k̄₀) )      (k₀ a fixed small numeral)
```
names `f_α(k₀)` in `s_α + O(1)` symbols. So `Rayo(s_α + O(1)) ≥ f_α(k₀)`.

As `n` grows, the ordinals definable in `≤ n` symbols climb without bound through
**every fixed notation** — ε₀, the Buchholz ordinal `ψ(Ω_ω)`, Γ₀, the
Bachmann–Howard ordinal, the proof-theoretic ordinals of BMS and of System F/CoC
— and far beyond any *particular* recursive ordinal, up toward the limits of
set-theoretic definability. Therefore

> `Rayo(n) ≥ f_{α(n)}(k₀)`, where `α(n)` = the largest ordinal a `≤ n`-symbol
> formula defines — a value that eventually exceeds `f_β` for **every fixed
> ordinal `β`**.

This is exactly why `Rayo` sits atop the `KAPPA-TABLE.md` ordinal ladder:
single-row BMS (ε₀), multi-row BMS (Buchholz), System F/CoC (its PTO) each live
at *one fixed* ordinal; `Rayo` passes each of them as soon as `n` is large enough
to *define* that ordinal, then keeps climbing. It doesn't compete at a fixed
rung — it walks up the whole ladder and off the top.

---

## 4. Upper bound: Rayo strictly transcends — and Tarski gives it for free

Is `Rayo` itself total-and-definable in V (so that §2–3 are just "dominates
things like itself"), or strictly beyond? **Strictly beyond**, and the proof is
immediate:

- If `Rayo : ℕ → ℕ` were definable in V by a set-theory formula, then (via the
  naming machinery) "the value of `Rayo` at the number named by the longest
  in-budget formula" would give a short in-budget formula naming a number `≥
  Rayo(n)`, contradicting `Rayo(n)`'s definition as one *more* than any in-budget
  naming (R0 §3's stratification argument, read as a growth statement). More
  directly: `Rayo`'s definition runs through truth-in-V, which by **Tarski's
  undefinability theorem is not definable in V at first order**. So `Rayo` is not
  definable-total, hence — by §2's contrapositive — not dominated by any
  definable-total function. It strictly transcends the entire class of §2.

**The asymmetry worth noting.** For the Boolos fork, strict transcendence needed
Boolos's **diagonalization** (`BOOLOS-B3-PAPER-VERIFICATION.md` §4), because
provability *is* first-order-expressible, so Tarski does not directly forbid a
provably-total bound. For Rayo it is the reverse: the naming predicate is
truth-in-V, which Tarski forbids at first order outright, so transcendence falls
out with **no diagonalization at all**. The very feature that made Rayo's
*well-definedness* hard (needing the MK truth predicate, R0) makes its
*transcendence* easy. This is a clean structural mirror of the two forks.

---

## 5. The honest ceiling: no single ordinal characterizes Rayo

For the sub-Turing systems in `KAPPA-TABLE.md`, growth has a crisp
proof-theoretic-ordinal characterization: single-row BMS is exactly `ε₀`,
multi-row BMS the Buchholz ordinal, System F/CoC its PTO, and (Boolos fork)
`BoolosBig_PA` is `≈ ε₀` (`= PTO(PA)`). **`Rayo` has no such characterization**,
and that is the finding, not a gap in the analysis:

- Its growth outruns `f_β` for *every* fixed recursive ordinal `β` (§3), so no
  fixed ordinal notation bounds it.
- Its true "strength" is truth-in-V itself, which transcends any theory whose
  theorems are true in V (§2 works for every sound `T`), so it is not pinned by
  the proof-theoretic ordinal of *any* fixed theory.
- Its exact rate is not even arithmetically definable (it is tied to a truth
  predicate for V, R0 §4), so unlike Busy Beaver (uncomputable but arithmetic)
  it is not capturable at any finite level of the arithmetic hierarchy.

So the right statement is qualitative: **`Rayo` dominates the union of all
fixed-ordinal-notation systems and every sound theory's provably-total
functions, bounded above only by truth-in-V.** That is precisely the sense in
which `BN-function.md` calls first-order set theory "the strongest admissible R
commonly used."

---

## 6. What this adds to the κ-table, and honest limits

**Sharpens the diagonalization-family finding (`KAPPA-TABLE.md`).** §2–§4 show
Boolos and Rayo use the *same* naming mechanism — direct naming, `O(k)` input
cost, pre-inflation to dominate — and even the *same* proof shape. The entire
growth gap (Boolos `= ε₀`; Rayo beyond every notation) comes from **one thing:
the strength of the naming predicate** — first-order provability-in-PA
(Tarski-safe, PA-strength) versus truth-in-V (Tarski-forbidden, MK-strength).
Same machine, different fuel. This is the cleanest possible evidence for that
section's claim that, in the diagonalization family, *commitment strength is what
buys growth* — and that the step between the two rungs is the sharp,
Tarski-drawn, qualitative jump the section describes, not a smooth dial.

**Limits, kept honest.**
- §2's domination is a genuine theorem-shape argument; §3's "how far" is a
  **lower bound**, not a tight rate (Rayo may be faster still via namings outside
  the fast-growing hierarchy).
- "Definable ordinal / definable-total function" is made precise only *through*
  the truth-in-V predicate — so the entire analysis inherits R0's MK commitment
  and is void without it. This is not a side condition; it is the same
  load-bearing assumption R0 isolated, now controlling the growth story too.
- Standard facts assembled (fast-growing hierarchy, proof-theoretic ordinals,
  Tarski undefinability, soundness of ZFC in V), not a new theorem. The
  contribution is the assembly and the Boolos/Rayo mirror, which — like R0 — does
  not appear to have been written down for Rayo's construction.
- Paper, not Lean.

## Sources

Builds on this project's own `RAYO-R0-WELLDEFINEDNESS.md` (the MK commitment and
Tarski stratification), `BOOLOS-B3-PAPER-VERIFICATION.md` (the direct-naming
domination shape and the pre-inflation repair), `KAPPA-TABLE.md` (the
diagonalization-family axis and the ordinal ladder), `RAYO-EXPLAINER.md` (K0–K6
naming costs), and `rayo-notes/literature-notes.md` (no citable minimal-`n_k`
result). Background facts (the fast-growing hierarchy and proof-theoretic
ordinals of PA/BMS/System F, Tarski's undefinability theorem, soundness of a
theory true in V) are standard — see any proof-theory reference; stated here as
standard, not re-proved.
