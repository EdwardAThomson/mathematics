# Handoff to the laptop (Lean) session

Instructions for the toolchain-enabled machine, written by the remote (paper-only)
session. The remote session cannot run Lean (org egress blocks the Lean release
host); everything here is the *verified-artifact* work that belongs on the
laptop. Read the referenced paper notes first — they contain the corrected
mathematics you'll mechanize.

**Before starting:** `git pull` (the remote branch
`claude/large-numbers-section-nmhu8n` has been merged to `main`; make sure you
have `BOOLOS-B3-PAPER-VERIFICATION.md`, `RAYO-GROWTH-RATE.md`, and the updated
`KAPPA-TABLE.md`). Keep this project's standing bar: **no `sorry`/`admit` in
anything reported done**, and record `#print axioms` per theorem.

---

## Task 1 (primary): finish B3 — mechanize the domination theorem

**Goal.** Machine-check `BoolosBig_PA` eventually dominates every PA-provably-total
function, in `rayo-lean-boolos/`, building on the already-verified
`RayoBoolos/TNames.lean` (B1).

**Read first:** `BOOLOS-B3-PAPER-VERIFICATION.md` in full — it verified the
argument on paper and **found a real correction** you must apply (below), plus
`rayo-lean-boolos/BOOLOS-B1-B3-REPORT.md` §4 (your prior run's own account of the
strategy and exactly where it stuck).

**The corrected target theorem — do NOT prove the additive form.** The report's
draft aimed at `BoolosBig_PA(n + c) ≥ f(n)` (additive constant `c`). That is
**not provable** given Foundation's `Semiterm.numeral n` costing `O(n)`
(established in your own report §2): the naming formula is *linear* in `n`, not
`n + O(1)`. Prove instead the genuine domination form:

```
    theorem boolosBig_dominates (f : ℕ → ℕ) (P : ProvablyTotal f) :
        ∃ N, ∀ m, N < m → f m ≤ BoolosBig_PA m
```

**The fix that closes it (paper-verified, `BOOLOS-B3-PAPER-VERIFICATION.md` §3):**
apply the naming construction not to `f` but to the **pre-inflated**
`F(n) := f(n²)`. `F` is PA-provably-total whenever `f` is (compose `f`'s totality
with squaring), its graph `θ_F(y,x) :≡ ∃z(z = x·x ∧ θ_f(y,z))` has size
`|θ_f| + O(1)` with **no large numeral** (so no circular-constant trap — the
naive linear pre-inflation *fails*, see §3), and `n²` more than absorbs the
linear numeral factor. Concretely: if `BoolosBig_PA(a·n + b) ≥ F(n) = f(n²)`,
then for `m = a·n + b` and large `m`, `f(n²) ≥ f(m)` since `n² ≥ m`.

**The work breaks into three pieces (the report only reached the first, and it
stuck there):**

1. **The naming (`provablyTotal_names`) — resume the stuck proof.** Steps 1–3 of
   the argument are mathematically sound (re-verified, `BOOLOS-B3-PAPER-
   VERIFICATION.md` §2). Your report §4 pinned the snag precisely: a
   substitution-associativity mismatch between `graphAt n = P.graph ⇜ ![#0,
   Semiterm.numeral n]` and the composed `Rew.subst` that specializing `total`
   produces — a `simp`-stuck goal on the `BinderNotation.finSuccItr`-shaped
   bound-variable reindexing under one `∀¹`/`∃¹`. Discharge it with Foundation's
   own composition lemmas `subst_comp_subst` / `Rew.ext` /
   `TransitiveRewriting.comp_app`, which `Bootstrapping/FixedPoint.lean` uses for
   the same kind of goal — model the `Rew` bookkeeping on that file. This is
   bookkeeping only; the math underneath is correct.
   - Uses (already located in your report §2): `Theory.Proof.specialize`
     (Step 1), `sigma_one_completeness_iff_param` (Step 2), then `∃!` + witness →
     biconditional (Step 3, not yet attempted — it comes after the stuck lemma).

2. **A symbol-length function + the numeral bound (new — not started).** To
   connect a naming formula to `BoolosBig_PA` you need `|·|` on
   `ArithmeticSemisentence` and the key lemma `|Semiterm.numeral n| ≤ a·n + O(1)`
   (this is your report's own `O(n)` finding, now needed as a *proved* bound, not
   a remark). Then `|graphAt n| ≤ |θ_f| + a·n + O(1)`.

3. **Define `BoolosBig_PA` and assemble.** Define
   `BoolosBig_PA(m) = sup{ k : ∃φ, |φ| ≤ m ∧ TNamesMeta φ k }` (the B0 §3 object;
   reuse the finiteness/monotonicity core already verified in
   `rayo-lean/Rayo/BoolosB0Core.lean` — port or import its combinatorial lemma so
   the `sup` is a well-defined `max`). Then: `provablyTotal_names` (piece 1)
   applied to `F = f∘(·²)` gives a formula of size `≤ |θ_F| + a·n` naming
   `f(n²)`, so `BoolosBig_PA(|θ_F| + a·n) ≥ f(n²)`; combine with monotonicity and
   the `n² ≥ m` bound to get `boolosBig_dominates`.

**Honest scope note:** the report made it sound like B3 is "one stuck lemma away."
It is not — piece 1 is the stuck lemma, but pieces 2–3 (a formalized symbol-length
function, the numeral bound, and the `BoolosBig_PA` definition wired to
`BoolosB0Core`) are real, unstarted work. Budget accordingly; if piece 1 alone is
a heavy lift against Foundation's `Rew` API, consider whether the whole of Task 1
is worth it versus recording the domination as paper-verified (it already is) and
mechanizing only pieces you can close cleanly.

**Acceptance:** `lake build` clean; `boolosBig_dominates` sorry-free; `#print
axioms` recorded (Foundation-based, so `[propext, Classical.choice, Quot.sound]`
expected — that's fine here, unlike the self-contained `rayo-lean/`). Commit the
now-closeable `Domination.lean` (it was withheld before only because it had a
`sorry`).

---

## Task 2 (secondary, self-contained — no Mathlib): the n_k minimal-naming question

**The question** (`RAYO-GROWTH-RATE.md` §2, flagged not resolved): is the minimal
FOST naming cost `n_k` actually `O(k)` (via a **successor chain**), far below the
K0–K6 table's `~3ᵏ` enumerate-predecessors cost? If so it's a real efficiency
finding (K0–K6 are exhibited upper bounds, never claimed minimal —
`RAYO-EXPLAINER.md` — so this is *consistent*, but the gap would be large).

**Do this in the self-contained `rayo-lean/`** (no Mathlib needed — same style as
K0–K6):

1. Build the successor-chain naming formula for a concrete `k` (start `k = 6` to
   compare against `K6.lean`): `φ_k(x)` asserting `∃w₀…w_{k-1}` a chain with
   `w₀ = ∅`, `w_{i+1} = wᵢ ∪ {wᵢ}`, `x = w_{k-1} ∪ {w_{k-1}}`, using the existing
   `Rayo.Formula`/`Sat` machinery.
2. Prove it names `k`: `∀ e, Sat e φ_k ↔ e 0 = ⟨von Neumann k⟩`, sorry-free, same
   discipline as `K0.lean`–`K6.lean` (`#print axioms` → `propext`/`Quot.sound`
   only).
3. Count `|φ_6|` under the project's symbol convention and compare to
   `n_6 = 11128`. Report the number.

**Two possible outcomes, both useful:** (a) `|φ_6| = O(k)` (~a few hundred, not
11128) and it verifies → a genuine finding; update `RAYO-EXPLAINER.md` and
`METHODOLOGY.md` honestly (minimal `n_k` is `O(k)`, the `~3ᵏ` table is a
suboptimal-for-large-k strategy). (b) A convention subtlety makes it not cheaper
or not valid → *that's* the answer, and it explains why K0–K6 used
enumerate-predecessors. Either way, record it. **Do not** silently overwrite the
K0–K6 numbers — they're correct upper bounds; this is about the *minimum*.

---

## Task 3 (operator decision, not Claude): Mathlib/Foundation commitment

`rayo-lean-boolos/` depends on Mathlib + `Foundation` (heavy, but already cached
and building for you). Task 1 needs it; Task 2 does not. Decide whether finishing
Task 1 is worth keeping/maintaining that dependency, or whether the paper-verified
B3 (`BOOLOS-B3-PAPER-VERIFICATION.md`) plus the verified B1 (`TNames.lean`) is a
sufficient stopping point for the Boolos fork. Recommendation from the remote
side: the infrastructure is already built and B1 is done, so Task 1 is the natural
finish — but see Task 1's honest scope note; it's more than one lemma.

---

## When done

Update `rayo-lean-boolos/BOOLOS-B1-B3-REPORT.md` (or add a B3-DONE note) with the
final `lake build` + `#print axioms` output, flip B3's status from "stuck" to
mechanized in `BOOLOS-B3-PAPER-VERIFICATION.md` §5 and `KAPPA-TABLE.md`'s
diagonalization-family row, and add a `DEVLOG.md` entry. If Task 2 lands a
finding, reconcile `RAYO-EXPLAINER.md`/`METHODOLOGY.md` as noted. Then the remote
side can pick up the write-up (#5) with everything verified behind it.
