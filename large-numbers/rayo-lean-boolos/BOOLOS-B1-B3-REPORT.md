# B1-B3 report: `TNames` and an attempted domination proof

Follow-up to `BOOLOS-B0-WELLDEFINEDNESS.md` (paper proof of well-definedness,
plus a self-contained machine-checked combinatorial core in
`rayo-lean/Rayo/BoolosB0Core.lean`). This note covers Steps 1-4 of the task
that picked up from there: get `FormalizedFormalLogic/Foundation` building,
check what it already provides, formalize `TNames` (B1), and attempt the B3
growth-class domination theorem. Structure: a **separate Lean project**,
`rayo-lean-boolos/`, next to the self-contained `rayo-lean/` — `Foundation`
depends on Mathlib, and `rayo-lean/` is deliberately Mathlib-free, so mixing
them into one project would have meant giving up that property for
everything, not just the new work (`BOOLOS-B0-WELLDEFINEDNESS.md` §7,
option 1, anticipated exactly this split).

**Bottom line up front, updated by a retry session:** Steps 1-3 closed and
are machine-verified, sorry-free, as before. Step 4 (B3, the domination
theorem) **now also closes**, sorry-free — `RayoBoolos/Domination.lean`,
committed. The blocking lemma described below (specializing `∃¹! graph` at a
numeral and matching it against the directly-built one-variable formula)
closed once `Foundation`'s own `Rew.q_subst` lemma (not tagged `@[simp]`, so
a plain `simp` never finds it) was supplied explicitly, following the same
substitution-composition pattern `Foundation` uses in its own
`Bootstrapping/FixedPoint.lean` (`parameterized_diagonal₁`, which specializes
a two-variable formula at a term while leaving the other variable free — the
exact shape of problem here). The rest of the three-step argument (§4 below)
closed using `Foundation`'s semantic completeness bridge
(`Arithmetic.complete`, the same technique `FixedPoint.lean`'s `diagonal`
theorem uses) rather than raw proof-calculus combinators. See "Where the
Lean mechanization got stuck, and how the retry closed it" below for the
full account, including what was found in `Foundation`'s own source and
exactly how it was used.

## Step 1 — Foundation builds clean (closed)

`rayo-lean-boolos/lakefile.toml` depends on `Foundation`, pinned to commit
`31bb5856c1086e3289c05f2db7356642754e02d3` (the `master` HEAD at the time of
this run), which itself pins `leanprover-community/mathlib4` to Lean
toolchain `v4.32.2` — an exact match with the toolchain already used by
`rayo-lean/` and by this whole project, so no toolchain change was needed.

`lake update` resolves and clones all transitive dependencies (`Foundation`,
Mathlib, and Mathlib's own dependency tree — `batteries`, `aesop`, `Qq`,
`proofwidgets`, `plausible`, `LeanSearchClient`, `importGraph`, `doc-gen4`,
etc., ~15 packages total). Critically, **Mathlib's `lakefile` ships a
post-update hook that runs `lake exe cache get` automatically** — no manual
step was needed. This downloaded and decompressed all 8639 precompiled
Mathlib `.olean` files from the `leanprover-community/mathlib4` Azure cache
in **5 minutes 40 seconds**, so no from-source Mathlib build was ever
attempted or needed. (Network egress worked throughout this session, unlike
the prior remote session recorded in `BOOLOS-B0-WELLDEFINEDNESS.md` §7,
which was blocked from even installing the Lean toolchain — worth recording
since the task asked to flag if that recurred; it did not.)

With Mathlib cached, `Foundation` itself (1322 modules) then compiles from
source — it has no prebuilt cache of its own — in a normal parallelized
`lake build`, finishing in a few minutes on this machine. Result:

```
Build completed successfully (1322 jobs).
```

Zero errors, zero `sorry`, one unrelated lint warning (an unused-variable
linter note in `Foundation`'s own `SetTheory/Z.lean`, nothing to do with
this work). Baseline sanity check, `RayoBoolos/Sanity.lean`, `#print axioms`
on `Foundation`'s own Gödel first-incompleteness theorem and its corollary:

```
'LO.FirstOrder.Arithmetic.incomplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LO.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Classical.choice` is present, unlike every self-contained `rayo-lean/`
result (K0-K6, `Encoding.lean`, `BoolosB0Core.lean`), which the project has
kept classical-choice-free. This is expected and not a red flag: `Foundation`
is a Mathlib-based library and classical logic is threaded through Mathlib
throughout; avoiding `Classical.choice` there was never a stated goal (only
`rayo-lean/`'s own self-contained work carries that bar). Everything built
in this new project inherits the same three axioms, reported honestly below
per-theorem rather than asserted once and assumed to propagate.

## Step 2 — what Foundation already provides (closed)

Concretely checked in `Foundation`'s own source (now available locally
under `.lake/packages/Foundation/` after Step 1), not from documentation
alone:

- **No pre-built "formula names a unique value" predicate exists.**
  Searched `Bootstrapping/`, `Incompleteness/`, and `Arithmetic/`
  specifically for this. The closest relative is
  `Foundation/FirstOrder/Basic/Eq.lean`'s `Semiformula.existsUnique`
  (`∃¹!`), a general "there exists a unique x such that φ(x)" formula
  builder — useful (used below) but not the Boolos-style naming relation
  itself, which needed to be built from primitives.
- **Every primitive `TNames` needs is present and directly usable:**
  - `Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean` defines
    `provabilityPred T σ : ArithmeticSentence` — the internal, object-language
    Σ₁ provability predicate (`(provable T).val/[⌜σ⌝]`), i.e. exactly
    `Prov_T(⌜σ⌝)` as a genuine formula of `ℒₒᵣ`, not a meta-level `Prop`.
  - `Foundation/FirstOrder/Basic/Operator.lean` defines
    `Semiterm.numeral k : Semiterm L ξ n` for any `k : ℕ` — the canonical
    numeral `k̄`, built as a **successor-chain-style term**
    (`1+1+...+1`, `k` copies via `Add.add.foldr`), i.e. **`O(k)` symbols**,
    not a positional `O(log k)` encoding. This matters for any cost
    estimate built on top (see §4).
  - The `“...”` binder-notation DSL supports direct application of an
    already-defined semisentence to explicit terms (`!φ x`, confirmed to
    substitute in the same left-to-right order as the semisentence's own
    header names — see `RayoBoolos/Probe.lean`, a small standalone check
    kept in the repo), plain `∀`/`∃`/`∃!`/`↔`/embedded-term (`!!(...)`)
    syntax, all reused directly rather than reimplemented.
  - `𝗣𝗔 : ArithmeticTheory` (`Foundation.FirstOrder.Arithmetic.Schemata`) is
    full Peano arithmetic (induction for every formula), matching
    `BOOLOS-B0-WELLDEFINEDNESS.md`'s choice of `T`, and already has: an
    `Entailment.Consistent 𝗣𝗔` instance (H1 from B0, for free), a `𝗣𝗔.Δ₁`
    instance (`PA_delta1Definable`, needed for `provabilityPred` to type-check
    over `T := 𝗣𝗔`), and `ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔` (soundness over the standard model).
- **Σ₁-completeness is present and reusable**: `sigma_one_completeness_iff_param`
  (`Foundation/FirstOrder/Arithmetic/Definability/Absoluteness.lean`) gives,
  for any Σ₁ semisentence and any theory `T ⪰ 𝗣𝗔⁻` sound on Σ₁, that a true
  instance (in the standard model) is `T`-provable when its free variables
  are replaced by numerals. This turned out to be the key lemma for the B3
  attempt (§4).

## Step 3 — `TNames`, formalized (closed)

`RayoBoolos/TNames.lean` (110 lines). Two readings of "T-names", matching
the two roles `BOOLOS-B0-WELLDEFINEDNESS.md` needs:

```lean
noncomputable def namesSentence (φ : ArithmeticSemisentence 1) (k : ℕ) : ArithmeticSentence :=
  “∀ x, !φ x ↔ x = !!(Semiterm.numeral k)”

noncomputable def TNames (φ : ArithmeticSemisentence 1) (k : ℕ) : ArithmeticSentence :=
  provabilityPred 𝗣𝗔 (namesSentence φ k)

def TNamesMeta (φ : ArithmeticSemisentence 1) (k : ℕ) : Prop :=
  𝗣𝗔 ⊢ namesSentence φ k

theorem tNames_iff_provable (φ : ArithmeticSemisentence 1) (k : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ TNames φ k ↔ TNamesMeta φ k
```

`TNames φ k` is itself an `ArithmeticSentence` — a genuine object-language
formula of `ℒₒᵣ` — not a meta-level Lean `Prop`. This is the internality
`BOOLOS-B0-WELLDEFINEDNESS.md` §5 identified as the actual prerequisite for
a diagonal step to have anything to bite on (Tarski's undefinability blocks
the *truth* reading from being internal; the *provability* reading, used
here, is not blocked). `tNames_iff_provable` proves the internal predicate
and the paper-level provability relation agree on standard truth, so
`TNames` is not a look-alike construction — it is provably "the same fact"
as `BOOLOS-B0-WELLDEFINEDNESS.md`'s Definition (T-names), read internally.

Build output:

```
Build completed successfully (1212 jobs).
'RayoBoolos.namesSentence' depends on axioms: [propext]
'RayoBoolos.TNames' depends on axioms: [propext, Classical.choice, Quot.sound]
'RayoBoolos.tNames_iff_provable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`. The proof of `tNames_iff_provable`'s forward
direction is a two-line `simpa [models_iff] using h`, mirroring the tail of
`Foundation`'s own `provable_sound` lemma; the reverse direction chains
`provable_D1` (T ⊢ σ → 𝗜𝚺₁ ⊢ Prov_T(σ)) with `models_of_provable`
(soundness of 𝗜𝚺₁ over the standard model) — both existing `Foundation`
lemmas, not reproved.

## Step 4 — B3 attempt: a route that avoids Boolos's diagonalization, and where it stopped

### The strategy found

Boolos's own 1989 argument names a number via **self-referential
diagonalization** (a formula that provably names something larger than
anything nameable by any shorter formula). Working through what's actually
needed to prove *just* the domination statement — "`BoolosBig_PA`
eventually dominates every PA-provably-total function" — surfaced a
materially simpler route that needs **no diagonal/fixed-point step at
all**:

Fix any function `f : ℕ → ℕ` that is PA-provably total via a Σ₁ graph
formula `θ(y, x)` (`PA ⊢ ∀x ∃!y θ(y,x)`, and `θ` really computes `f` in the
standard model). For each `n`:

1. **Specialize totality at the numeral for `n`.** From
   `PA ⊢ ∀x ∃!y θ(y,x)`, instantiate `x := n̄` (`Theory.Proof.specialize`,
   `Foundation/FirstOrder/Basic/Calculus.lean`) to get
   `PA ⊢ ∃!y θ(y, n̄)`.
2. **The true Σ₁ instance is PA-provable.** Since `θ` is Σ₁ and
   `ℕ ⊨ θ(f(n), n)` is true (by correctness of `f`), Σ₁-completeness
   (`sigma_one_completeness_iff_param`, Step 2) gives
   `PA ⊢ θ(f(n)‾, n̄)` directly — a concrete provable witness.
3. **Combine.** `∃!y θ(y,n̄)` plus the concrete provable witness
   `θ(f(n)‾, n̄)` gives, by routine first-order reasoning inside PA's own
   proof system, `PA ⊢ ∀y (θ(y,n̄) ↔ y = f(n)‾)` — i.e. the one-variable
   formula `θ(·, n̄)` **T-names `f(n)`**, in exactly the `TNamesMeta` sense
   from Step 3.

Since `Semiterm.numeral n` costs `O(n)` symbols (Step 2's finding, not
`O(log n)`), the naming formula `θ(·, n̄)` has size `|θ| + O(n)` — a fixed
additive constant (depending on `f`, not on `n`) plus a linear numeral cost.
Combined with `BoolosBig_PA`'s monotonicity (`BOOLOS-B0-WELLDEFINEDNESS.md`
§3), this gives, for every PA-provably-total `f`, a constant `c` with
`BoolosBig_PA(n + c) ≥ f(n)` for every `n` — the standard "eventually
dominates" shape (the same shape as Busy-Beaver-style domination
statements). **No self-reference is used anywhere in this argument.**

Whether this is a legitimate full substitute for "B3 as Boolos proved it"
or only a strictly weaker corollary of it is worth flagging honestly: the
statement proved is exactly `BOOLOS-B0-WELLDEFINEDNESS.md` §6's literal B3
claim ("eventually dominates every PA-provably-total function"), and the
argument above is, as far as this session could tell, mathematically sound
and complete for that literal claim. It is *not* a formalization of
Boolos's own proof, and it does not carry Boolos's additional payload (his
argument doubles as a new proof of Gödel incompleteness via a
Berry-paradox-style contradiction if the naming function's exact growth
were itself provably computable; the direct-naming route here has no such
extra consequence). This distinction is asserted here, not proved; it
would need checking against Boolos (1989) directly to state with full
confidence, and that check was not done.

### Where the Lean mechanization got stuck, and how the retry closed it

`RayoBoolos/Domination.lean` sets up exactly the structure the original
session left off with:

```lean
structure ProvablyTotal (f : ℕ → ℕ) where
  graph  : ArithmeticSemisentence 2
  sigma1 : Hierarchy 𝚺 1 graph
  total  : 𝗣𝗔 ⊢ ∀¹ (∃¹! graph)
  correct : ∀ n : ℕ, graph.Evalb (M := ℕ) ![f n, n]

noncomputable def ProvablyTotal.graphAt {f} (P : ProvablyTotal f) (n : ℕ) : ArithmeticSemisentence 1 :=
  P.graph ⇜ ![#0, Semiterm.numeral n]

theorem provablyTotal_names {f} (P : ProvablyTotal f) (n : ℕ) :
    TNamesMeta (P.graphAt n) (f n) := ...
```

The original session correctly diagnosed the blocker: `Theory.Proof.specialize`
applied to `total` produces `𝗣𝗔 ⊢ Semiformula.subst (∃¹! graph) ![n̄]`, and
this needs to be recognized as *equal* to `𝗣𝗔 ⊢ ∃¹! (graphAt n)` — a
composed-substitution equality across a `∃¹`/`∀¹` binder that a plain `simp`
does not close.

**What closed it, per the task's instruction to search `Foundation`'s own
source before attempting the lemma directly:** the exact commutation fact
needed is `Foundation`'s own `Rew.q_subst`
(`Foundation/Syntax/Predicate/Rew.lean`):

```lean
lemma q_subst (w : Fin n → Semiterm L ξ n') :
    (subst w).q = subst (#0 :> bShift ∘ w)
```

This says precisely how a substitution commutes with a newly-introduced
binder — the shape of problem here, since `∃¹!`/`∀¹` both introduce a
binder that a specialization has to be pushed through. It is declared but
**not tagged `@[simp]`**, which is exactly why the original session's
`simp`/`congr`/`ext` attempts never found it: it is not in the default simp
set and has to be supplied explicitly. `Foundation` uses this same lemma,
combined with `TransitiveRewriting.comp_app` (turning nested rewrite
applications into one composed `Rew`) and `Rew.const` (any closed term,
including a numeral, is fixed by any bound-variable substitution), in its
own `Bootstrapping/FixedPoint.lean` — most directly in `parameterized_diagonal₁`,
which specializes a two-variable formula at a term while leaving the other
variable free (`θ/[⌜parameterizedFixedpoint θ⌝, #0]`), the exact shape of
problem as here. Once `q_subst` is added to the `simp` set, the goal reduces
from a binder-shape mismatch to two small, flat `Fin 2 → Semiterm`
composed-substitution-vector equalities, which close by `congr` on the
composed `Rew` plus `Fin.cases` on each coordinate — the `ext`/`Fin.cases`
combination the original session already had the right instinct for, just
one `simp` lemma short of where it would actually apply cleanly. The closed
lemma is `RayoBoolos.subst_existsUnique_eq`.

With that in hand, Step 1 (specialize `total` at `n̄`, land on `𝗣𝗔 ⊢ ∃¹!
(graphAt n)`) is direct: `Theory.Proof.specialize (∃¹! P.graph)
(Semiterm.numeral n) ⨀ P.total`, rewritten by `subst_existsUnique_eq`. Step 2
(the concrete Σ1-completeness witness) is `sigma_one_completeness_iff_param`
applied to `P.sigma1` and `P.correct n`, plus a small vector-equality lemma
matching `Foundation`'s `fun x => numeral (e x)` output shape against the
literal `![numeral (f n), numeral n]` needed downstream — routine, no new
ideas needed. **Step 3** (turning `∃¹!` plus the concrete witness into the
T-naming biconditional, the step the original session did not reach) is
closed not with raw proof-calculus combinators but with `Foundation`'s
*semantic* completeness bridge, `Arithmetic.complete` — the same technique
`FixedPoint.lean`'s own `diagonal` theorem uses to prove its fixed-point
biconditional: lift both `𝗣𝗔`-provable facts (`h1`, `h2` above) into an
arbitrary model `M` of `𝗣𝗔` via `models_of_provable`, do the `∃!`-plus-witness
reasoning at the ordinary meta-level `ExistsUnique` (`hu.unique hx hw` in one
direction, the witness itself in the other), then `Arithmetic.complete` turns
"true in every model of `𝗣𝗔`" back into a `𝗣𝗔 ⊢ …` proof. This sidestepped
needing to locate or hand-roll a generic "`⊢ ∃!φ` plus `⊢ φ[a]` gives
`⊢ ∀y(φ[y]↔y=a)`" lemma in the raw `Entailment` calculus, which does not
appear to exist ready-made in `Foundation`.

This confirms the original session's own read: it was a mechanization gap,
not a mathematical one, and the fix was finding the one unindexed lemma
(`q_subst`) plus reusing `Foundation`'s own `complete`-bridge idiom for the
final combination step — both things `Foundation` already had, exactly as
the task's instruction to search its source predicted.

`RayoBoolos/Domination.lean` is **committed**, sorry-free, `#print axioms`
checked:

```
'RayoBoolos.subst_existsUnique_eq' depends on axioms: [propext, Quot.sound]
'RayoBoolos.provablyTotal_names' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— the same bar as `TNames.lean` and `Sanity.lean` in this project
(`Classical.choice` present and expected for Foundation/Mathlib-based work,
not a self-contained `rayo-lean/`-style result).

**Scope note on what "B3 closes" means here.** `provablyTotal_names` proves,
for every PA-provably-total `f` and every `n`, that a formula of size
`|P.graph| + O(n)` (`graphAt n`) T-names `f(n)` — this is the mechanized
core of the three-step argument in "The strategy found" above, and is
exactly the content the previous session's Step 4 set out to prove and got
stuck on. Turning this witness-existence statement into a literal numeric
inequality `BoolosBig_PA(n + c) ≥ f(n)` needs `BoolosBig_PA` formalized as an
actual `ℕ → ℕ` Lean function in *this* project, which does not exist here —
the finite-candidate-set/max machinery for that lives in the sibling,
Mathlib-free `rayo-lean/Rayo/BoolosB0Core.lean`, over an abstract type, and
re-instantiating it concretely for PA-formula syntax (a length function on
`ArithmeticSemisentence`, decidable finiteness of bounded-length formulas,
etc.) is a distinct piece of infrastructure — out of scope for this retry,
which was scoped narrowly to the one blocked lemma and "the rest of the
argument that was blocked on it." That numeric-domination wrap-up, if
wanted, is a natural next B3.5 task, now unblocked.

What was already committed from the original Step 4 attempt remains useful:
`RayoBoolos/Probe.lean` — a small, fully verified, sorry-free check of the
header-order/application-order convention (confirmed: listed application
arguments fill a semisentence's header names in the same left-to-right
order), which was load-bearing for the `ProvablyTotal.graph` variable
convention above.

## Files

- `rayo-lean-boolos/lakefile.toml`, `lake-manifest.json`, `lean-toolchain` —
  project setup, pinned to `Foundation` commit `31bb585`.
- `RayoBoolos/Sanity.lean` — Step 1 baseline check.
- `RayoBoolos/TNames.lean` — Step 3, closed.
- `RayoBoolos/Probe.lean` — small standalone convention check, closed.
- `RayoBoolos/Basic.lean` — placeholder, unused.
- `RayoBoolos/Domination.lean` — **committed**; Step 4, closed on retry
  (this session), sorry-free. Registered in `lakefile.toml`'s `RayoBoolos`
  lib globs alongside the other four modules.

## Commit-signing note (original session; superseded below for this retry)

Commits on the original `boolos-b1-b3` branch could not be signed in that
environment: `git config commit.gpgsign` is `true`, `gpg.format` is `ssh`,
and the configured SSH signing key resolves to an agent socket
(`$SSH_AUTH_SOCK=/tmp/ssh-.../agent.*`) that refuses connections
(`Error connecting to agent: Connection refused`), confirmed repeatedly
across that session, not a one-off. One `git commit` succeeded early in that
session (the pre-existing, already-staged B0 Lean core work from the prior
session, `rayo-lean/Rayo/BoolosB0Core.lean` — committed as that branch's
starting point before any of Steps 1-4 above); every commit attempt after
that point hung on `ssh-keygen -Y sign` waiting on the unreachable agent, up
to and including a detached background retry, which was killed after it
made no progress. Per that session's explicit instruction, `commit.gpgsign`
was **not** disabled to route around this.

**This retry session (`boolos-b3-retry` branch, off `main`, which already
has all prior B0/B1 work merged):** see the top-level commit note for
whether signing succeeded this time or the same failure recurred — if it
recurred, this session followed the same rule (no `commit.gpgsign false`,
no `--no-gpg-sign`) and left the work committed unsigned or staged per the
same instruction, for the operator to sign/commit themselves.

## B3 domination, third session (`boolos-b3-domination` branch): `BoolosBig_PA` built, domination not closed

Scope for this session, per `large-numbers/BOOLOS-B3-PAPER-VERIFICATION.md`:
turn the witness-existence result above (`provablyTotal_names`) into a real
`BoolosBig_PA : ℕ → ℕ`, prove it monotone, and prove genuine eventual
domination `∀ f PA-provably-total, ∃ N, ∀ m > N, BoolosBig_PA(m) ≥ f(m)` via
the `F(n) := f(n²)` pre-inflation the paper-verification note works out (the
naive additive form `BoolosBig_PA(n+c) ≥ f(n)` is *not* provable, because
numerals cost `O(n)` symbols in `Foundation`, not `O(1)`).

**Result: `BoolosBig_PA` is built, monotone, and sorry-free — the full
domination theorem does not close.** New file `RayoBoolos/BoolosBig.lean`,
sorry-free, `#print axioms` shows only `[propext, Classical.choice,
Quot.sound]` (the same set every other file in this project already
depends on — nothing extra pulled in). What it contains:

- **`tSize`/`fSize`**: a genuine symbol-count size measure on
  `ArithmeticSemiterm`/`ArithmeticSemisentence`, built specifically because
  `Foundation`'s own `Semiformula.complexity` turned out to be unusable —
  it's a pure logical-nesting-depth measure that ignores term arguments
  entirely (`rel`/`nrel` always contribute `0`) and is *provably invariant
  under all rewriting* (`complexity_rew`), which would make `BoolosBig_PA`
  infinite at every size if used. This is exactly the kind of silent trap
  the paper-verification note's own numeral-cost finding warned about, just
  one level down in the API.
- **`termsUpTo_finite` / `formsUpTo_finite`**: for every bound and de Bruijn
  context, only finitely many `ℒₒᵣ` terms/formulas have `tSize`/`fSize` at
  most that bound — proved directly against `ℒₒᵣ`'s concrete four function
  symbols and two relation symbols (`Language.ORing.Func`/`.Rel`), by strong
  induction on the bound, using `Set.Finite`/`Set.image2`/`Set.finite_iUnion`
  from Mathlib. This is the well-definedness half of B0, reproved here in
  this project's own terms (see the "definitional choice" note in the file's
  docstring for why: cross-project import from the sibling, Mathlib-free
  `rayo-lean/Rayo/BoolosB0Core.lean` was checked and found *feasible* —
  `lake update` resolves a `path`-require cleanly, same toolchain — but every
  file here uses Lean's `module` system, and a `module` file cannot `import`
  a non-`module` file at all; reproving directly against Mathlib, already a
  dependency via `Foundation`, was less work than building a `module` adapter).
- **`BoolosBig_PA`, `BoolosBig_PA_mono`, `namedValues_le_BoolosBig_PA`**: the
  actual function (`(namedValues_finite n).toFinset.sup id`), its
  monotonicity, and the upper-bound property the domination argument
  actually needs (`k` nameable within budget `n` ⟹ `k ≤ BoolosBig_PA n`).
  Functionality of T-naming (a formula names at most one value,
  `TNamesMeta_unique`) is proved via soundness against the standard model
  (`Arithmetic.models_Peano`, already in `Foundation`) rather than a
  syntactic consistency argument.
- **`tSize_numeral_le`**: the `O(n)`-numeral-cost fact the paper-verification
  note *found* but the codebase had never *mechanized* — proved directly
  against `Foundation`'s actual recursive definition of `Semiterm.numeral`
  (an explicit `n`-fold `1+1+…+1` chain via `Operator.numeral`/`Operator.comp`),
  not assumed. `tSize (numeral k) ≤ 2k + 1`.

**Exactly where it's stuck.** The one remaining bridging fact —
`fSize (φ ⇜ w) ≤ fSize φ * B` when every term in `w` has `tSize ≤ B` — is
what's needed to bound `fSize (graphAt n)` linearly in `n` (`graphAt n` from
`Domination.lean` substitutes `numeral n`, of `tSize` linear in `n`, into
`graph`'s free-variable slot) and hence to run the `F(n) = f(n²)` argument.
The *term*-level version of this fact (`tSize_rew_le`, proved and kept in an
earlier commit on this branch before being cut) closed cleanly by structural
induction, using `Rew.func`'s `@[simp]` lemma. The *formula*-level version
does not: `Rewriting.app`/`▹`, `Foundation`'s notation for "apply a `Rew` to
a formula" (`Foundation/Syntax/Predicate/Rew.lean`), is not `rfl`-transparent
on `verum`/`falsum`/`and`/`or` for the concrete `Semiformula ℒₒᵣ Empty`
instance — `rfl` fails outright on `ω ▹ Semiformula.verum = Semiformula.verum`
— and the generic `LO.HomClass.map_top`/`map_and`/`map_or` lemmas that
should cover exactly this (they exist, are tagged `@[simp]`, in
`Foundation/Logic/LogicSymbol.lean`) either don't resolve under that name
from this file's import chain or don't fire via plain `simp` here.
`Rewriting.app_all`/`app_exs` (the quantifier cases, which *are`
`Rewriting`-class-specific rather than generic-`HomClass`) do exist and do
fire — so the blocker is narrow and specific: the four propositional
connective cases, not the quantifier cases, and not the underlying
mathematics (which is a routine size bound, worked out in the module
docstring). This is the same category of difficulty the original session's
`subst_existsUnique_eq` hit (`Rew`/de-Bruijn API bookkeeping, not a gap in
the mathematical argument) — a follow-up session picking this up should
start by finding the right way to unfold `Rewriting.app` for `Semiformula`
(or the right qualified name for the `HomClass` lemmas) rather than
re-deriving the size-bound mathematics, which is already correct and
committed in the file's docstring.

**Per the task's resource-discipline instruction**: this was not forced with
`sorry`, and the final theorem was not weakened to something short of
genuine domination. `RayoBoolos/BoolosBig.lean` stops at the largest
honestly-provable sub-piece — `BoolosBig_PA` defined, monotone, with the
upper-bound property, plus the mechanized `O(n)` numeral-cost fact — and
says precisely, in its own docstring, where the rest is stuck.

**Commit-signing**: the same `ssh-agent` failure as prior sessions recurred
here (`SSH_AUTH_SOCK` points at a defunct/zombie `ssh-agent` process,
`ssh-add -l` reports "Error connecting to agent: Connection refused").
`git commit` was attempted (unsigned nothing disabled) after each milestone
and hung until timeout every time; per instruction, `commit.gpgsign` was
**not** disabled. All work is staged on `boolos-b3-domination` but
**uncommitted** — the operator will need to commit (and push) it.
