# B3, verified on paper: the direct-naming domination argument

Independent paper check of the B3 argument in
`rayo-lean-boolos/BOOLOS-B1-B3-REPORT.md` §4 — the "materially simpler route
than Boolos's own diagonalization" the laptop run found, specified and believed
correct there but **not** mechanized (its Lean proof stuck on a de-Bruijn
substitution bookkeeping lemma) and **not** independently checked. That report
explicitly left two things open: *is the argument sound and complete for the
literal B3 claim*, and *is it a full substitute for Boolos (1989) or a strictly
weaker corollary*. This note answers both.

**Bottom line.** The three-step strategy is **sound** — I verified each step
(§2). The **conclusion holds** — `BoolosBig_PA` eventually dominates every
PA-provably-total function. But the report's write-up has **one real gap**
(§3): given its own finding that Foundation's numeral costs `O(n)`, the naming
formula has size *linear* in `n`, so the report's stated additive-constant form
`BoolosBig_PA(n + c) ≥ f(n)` is **not justified as written**; recovering genuine
domination `BoolosBig_PA(m) ≥ f(m)` needs one extra step the report skips
(pre-inflating the function, e.g. to `f(n²)`), which is standard and which I
supply. And the Boolos-1989 question resolves cleanly (§4): the direct route is
a legitimate proof of the *domination* statement but is **strictly weaker** than
Boolos's theorem — it carries neither strict transcendence nor the incompleteness
payload, both of which need the diagonalization it drops. The report's instinct
was right.

**Plain-English version.** The laptop found a shortcut proof that this naming
function outgrows everything ordinary arithmetic can handle — sidestepping the
hard self-referential trick Boolos originally used. I checked it. The core idea
is correct and the conclusion is true. There's one arithmetic slip: because
writing the number `n` in this system costs about `n` symbols (not `log n`), the
proof's "costs a fixed constant extra" line is too optimistic — it's really "a
constant *times* `n`." That doesn't sink the result; you just feed the argument
a faster-growing function to swallow the factor, and it goes through. Separately:
this shortcut proves the *"grows insanely fast"* part, but not the deeper thing
Boolos's original proof also delivered (a new proof of Gödel incompleteness) —
that genuinely needs the self-referential trick, and the shortcut gives it up.
For what this project needs (the growth rate, for the κ-table), the shortcut is
exactly the right tool.

---

## 1. The claim and the strategy under test

From `BOOLOS-B0-WELLDEFINEDNESS.md`: a one-free-variable PA-formula `φ`
**T-names** `k` iff `PA ⊢ ∀x(φ(x) ↔ x = k̄)`, and
`BoolosBig_PA(n) = sup{ k : some φ with |φ| ≤ n T-names k }`.

**B3 (literal claim, `BOOLOS-B0-WELLDEFINEDNESS.md` §6):** `BoolosBig_PA`
eventually dominates every PA-provably-total function.

**The direct-naming strategy (report §4).** Let `f : ℕ → ℕ` be PA-provably
total via a `Σ₁` graph `θ(y,x)`: `PA ⊢ ∀x ∃!y θ(y,x)`, and `ℕ ⊨ θ(f(n), n)` for
all `n`. Then for each `n`:

1. **Specialize totality** at `x := n̄`: `PA ⊢ ∃!y θ(y, n̄)`.
2. **Σ₁-completeness** turns the true `Σ₁` instance into a proof:
   `PA ⊢ θ(f(n)‾, n̄)`.
3. **Combine** `∃!` with the concrete witness: `PA ⊢ ∀y(θ(y,n̄) ↔ y = f(n)‾)`,
   i.e. `θ(·, n̄)` T-names `f(n)`.

No self-reference anywhere.

---

## 2. Steps 1–3 are sound (checked)

- **Step 1.** Universal instantiation of the closed term `n̄` into
  `PA ⊢ ∀x ∃!y θ(y,x)` gives `PA ⊢ ∃!y θ(y, n̄)`. ✓ (Ordinary ∀-elimination;
  `n̄` is a closed term, so no capture issue.)
- **Step 2.** `θ(f(n)‾, n̄)` is a *closed `Σ₁` sentence* (substituting numerals
  into a `Σ₁` formula preserves `Σ₁`), and it is *true* in `ℕ` by correctness of
  `f`. `Σ₁`-completeness of PA (indeed of `Q`/`IΣ₁`) proves every true `Σ₁`
  sentence, so `PA ⊢ θ(f(n)‾, n̄)`. ✓ (This is exactly Foundation's
  `sigma_one_completeness_iff_param`, which the report identifies as the key
  lemma.)
- **Step 3.** From `PA ⊢ ∃!y θ(y,n̄)` and the witness `PA ⊢ θ(f(n)‾, n̄)`:
  uniqueness gives `PA ⊢ ∀y'(θ(y',n̄) → y' = f(n)‾)` (the unique satisfier must
  be the exhibited one), and the witness gives the converse
  `PA ⊢ ∀y(y = f(n)‾ → θ(y,n̄))` by substitution; conjoining,
  `PA ⊢ ∀y(θ(y,n̄) ↔ y = f(n)‾)`. ✓ (Routine first-order reasoning inside PA.)

So `φ_n := θ(·, n̄)` T-names `f(n)`, with exactly one free variable. The naming
half of the argument is correct. **This is the part whose *mechanization*
stuck** (a substitution-normal-form mismatch in Foundation's `Rew` API, per the
report) — but the *mathematics* of Steps 1–3 is sound, so the stuck lemma is a
genuine bookkeeping-only gap, as the report claimed.

---

## 3. The gap: size is linear, not additive — and the fix

The report's next move: "`θ(·, n̄)` has size `|θ| + O(n)` … this gives, for
every PA-provably-total `f`, a constant `c` with `BoolosBig_PA(n + c) ≥ f(n)`
for every `n` — the standard 'eventually dominates' shape."

**This step is not justified as written, and the report's own Step-2 finding is
what breaks it.** The report itself established that Foundation's
`Semiterm.numeral n` is a successor/`1+1+…+1` chain of **`O(n)`** symbols, not a
positional `O(log n)` numeral. So the numeral `n̄` inside `φ_n = θ(·, n̄)`
contributes `c_num · n + O(1)` symbols for some constant `c_num ≥ 1` (with
Foundation's `1+1+…+1`, `c_num = 2`), giving

```
    |φ_n| = c_num · n + |θ| + O(1).
```

That is **linear in `n` with coefficient `c_num`**, not `n` plus an additive
constant. What the construction actually yields is therefore

```
    BoolosBig_PA(c_num · n + b) ≥ f(n),        b = |θ| + O(1).      (★)
```

For `c_num = 1` this coincides with the report's additive form; for the actual
`c_num = 2` it does **not**, and the distinction matters: from (★),
`BoolosBig_PA(m) ≥ f((m − b)/c_num)` — a lower bound in terms of `f` of a
*smaller* argument. For the fast-growing `f` that are the whole point (the `f_α`,
`α < ε₀`), `f((m−b)/c_num)` is astronomically below `f(m)`, so (★) does **not**
by itself give "`BoolosBig_PA(m) ≥ f(m)` eventually" — the standard meaning of
"dominates."

**The fix (standard, and it closes the conclusion).** Apply the *same*
construction not to `f` but to a pre-inflated function that outpaces the linear
factor. Take

```
    F(n) := f(n²).
```

`F` is PA-provably total whenever `f` is (compose `f`'s totality proof with
totality of squaring — `×` is in the language), and its `Σ₁` graph
`θ_F(y,x) :≡ ∃z(z = x·x ∧ θ_f(y,z))` has size `|θ_f| + O(1)` — crucially **no
large numeral**, so no circular constant. Applying (★) to `F`:

```
    BoolosBig_PA(c_num · n + b') ≥ F(n) = f(n²),   b' = |θ_F| + O(1).
```

Put `m = c_num · n + b'`, so `n ≥ (m − b')/c_num`. Then for all large `m`
(precisely `m` with `((m−b')/c_num)² ≥ m`, i.e. `m ⪆ c_num²`),

```
    BoolosBig_PA(m) ≥ f(n²) ≥ f( ((m−b')/c_num)² ) ≥ f(m),
```

using monotonicity of `BoolosBig_PA` and of `f`. Hence **`BoolosBig_PA(m) ≥ f(m)`
for all sufficiently large `m`** — genuine eventual domination. ∎

So the conclusion is true; only the report's *route to it* needs the extra
pre-inflation line. (Any super-linear provably-total pre-inflation works — `n²`,
`2ⁿ`, …; `n²` is the cleanest because it adds `O(1)` to the graph and no numeral.
The naive alternative — pre-inflating by a *linear* factor whose constant is
written as a numeral inside the graph — actually **fails**, because under `O(n)`
numeral cost that constant's own encoding grows the graph faster than it helps;
this is a small trap worth recording, and it is exactly why the `n²` route,
which needs no large constant, is the safe one.)

**Net:** the mechanization, had it cleared the Step-1–2 substitution lemma,
would still have needed this pre-inflation to reach a *domination* statement —
the additive-constant form as written is not provable. Recommend the laptop
target `F(n) = f(n²)` (or any super-linear provably-total pre-inflation) when it
resumes `Domination.lean`, and state the theorem as
`∀ f provably-total, ∃N ∀m>N, BoolosBig_PA(m) ≥ f(m)`, not the `n + c` form.

---

## 4. Is this Boolos's theorem? No — the report's instinct, confirmed and sharpened

The report flags, without proving, that the direct route "is not a formalization
of Boolos's own proof, and does not carry Boolos's additional payload." Checking
against what Boolos (1989, *A New Proof of the Gödel Incompleteness Theorem*)
actually establishes:

- **What the direct route proves:** a **lower bound** — `BoolosBig_PA` is `≥`
  every PA-provably-total `f` (eventually). Equivalently, `BoolosBig_PA` grows at
  least at fast-growing-hierarchy rate `ε₀` (the proof-theoretic ordinal of PA;
  PA's provably-total functions are exactly the `f_α`, `α < ε₀`). This is the
  headline "grows insanely fast" property, and it is genuinely non-trivial — it
  rides on `Σ₁`-completeness and the naming machinery. It is *exactly* B3's
  literal claim.
- **What Boolos additionally proves, and the direct route does not:**
  1. **Strict transcendence.** Boolos's diagonalization shows the naming/Berry
     function is *not itself* bounded by any PA-provably-total function — it
     genuinely escapes the class, rather than merely sitting on top of it as an
     upper envelope. The direct route gives `≥`, never `not ≤`; it says nothing
     about whether `BoolosBig_PA` is itself provably total.
  2. **A new proof of Gödel's first incompleteness theorem.** Boolos's payoff is
     that the Berry number is definable but *not provably* nameable within
     budget, yielding a true-but-unprovable sentence. The direct route produces
     no such sentence — it only ever *builds* provable namings, never derives a
     contradiction from a hypothetical short one, so it has no incompleteness
     consequence.

  Both (1) and (2) rest on the **self-referential diagonalization** the direct
  route deliberately omits (that omission is precisely why it is "materially
  simpler"). So the two are not interchangeable: the direct route is the **easy
  lower-bound half** of Boolos's result, bought by giving up the diagonalization
  and hence the transcendence and incompleteness.

**Verdict on the report's open question:** confirmed — the direct route is a
sound proof of the *literal B3 domination claim* but a **strictly weaker
statement** than Boolos's theorem, missing exactly the diagonalization-dependent
payload. **For this project this is fine and even preferable:** B3's role is to
pin the *growth rate* that feeds `KAPPA-TABLE.md` (Phase 4), and the domination
lower bound is precisely that. The incompleteness payload is not needed here.
But any write-up must label the result "the domination lower bound," **not**
"Boolos's theorem" or "a new incompleteness proof."

---

## 5. What this means for the machine-checked status

- **B0** (well-definedness): paper-proved (`BOOLOS-B0-WELLDEFINEDNESS.md`), core
  combinatorial lemma Lean-verified (`rayo-lean/Rayo/BoolosB0Core.lean`,
  sorry-free).
- **B1** (`TNames`): Lean-verified against `Foundation`, sorry-free
  (`rayo-lean-boolos/RayoBoolos/TNames.lean`) — the real mechanized win.
- **B3** (domination): the *strategy is sound and the conclusion holds*, now
  independently paper-verified here **with a corrected size step** (§3). Still
  **not mechanized**: the Lean proof needs (a) the stuck Step-1–2 substitution
  bookkeeping lemma, and (b) the §3 pre-inflation, and should state the
  `∀m>N` domination form, not the additive `n+c` form.
- **Honest gap between paper and machine:** B3 is paper-verified, not
  Lean-verified. This note does not change that — it raises confidence the
  mechanization is worth finishing and tells it exactly what to prove.

---

## 6. Summary

1. **Steps 1–3 sound** (§2): `θ(·,n̄)` really does T-name `f(n)`; the stuck Lean
   lemma is bookkeeping-only, as the report said.
2. **One real gap, and its fix** (§3): the `O(n)` numeral cost the report itself
   found makes the naming formula *linear* in `n`, so the stated additive
   `BoolosBig_PA(n+c) ≥ f(n)` is unjustified; pre-inflating to `f(n²)` recovers
   genuine domination `BoolosBig_PA(m) ≥ f(m)` eventually. **Conclusion holds;
   route needs the extra step.**
3. **Boolos-1989 question resolved** (§4): the direct route proves the literal
   B3 domination (growth `≈ ε₀`) but is **strictly weaker** than Boolos's
   theorem — no strict transcendence, no incompleteness proof, both of which need
   the dropped diagonalization. The project wants only the domination, so the
   route is the right one — but must be labeled as the lower bound, not Boolos's
   theorem.
