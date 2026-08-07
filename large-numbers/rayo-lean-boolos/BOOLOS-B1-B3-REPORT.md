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

**Bottom line up front:** Steps 1-3 closed and are machine-verified,
sorry-free. Step 4 (B3, the domination theorem) did not close. A materially
*easier* proof strategy than Boolos's own diagonalization was found and its
three-step mathematical argument is fully specified and believed correct
(§4 below), but its Lean mechanization got stuck on a routine
de-Bruijn-substitution bookkeeping lemma inside `Foundation`'s `Rew`/
`Rewriting` API, and was abandoned rather than forced through with `sorry`.

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

### Where the Lean mechanization got stuck

`RayoBoolos/Domination.lean` (not committed — see below) set up:

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

Steps 1 and 2 of the argument above **do produce well-typed Lean proof
terms** (`Theory.Proof.specialize` composed with `total`; and
`sigma_one_completeness_iff_param` applied to `correct n` and `sigma1`) —
the terms genuinely type-check as *proofs of something*, and the "something"
is provably the right statement up to a substitution-associativity
mismatch: `Foundation` represents "substitute the outer free variable of
`∃¹!graph`, then re-derive the resulting one-variable statement" as one
composed `Rew.subst`, while `graphAt n` (built directly via `⇜`) is a
*different but equal* composed substitution — equal by the general
`subst_comp_subst`/`Rew.ext`/`TransitiveRewriting.comp_app` composition
laws that `Foundation` itself uses internally (e.g. in
`Bootstrapping/FixedPoint.lean`'s `diagonal` theorem), but the specific
combination of `simp`/`congr`/`ext`/`Fin.cases` needed to discharge the
resulting index-shift goals (`BinderNotation.finSuccItr`-shaped bound
variable reindexing under one `∀¹`/`∃¹` binder) was not found within the
budget spent on it — repeated attempts left a `simp`-stuck goal on the
bound-variable component of the `Rew` extensionality lemma. Step 3 (turning
`∃!` plus a concrete witness into the T-naming biconditional, purely inside
`PA`'s own object-level proof calculus) was not attempted at all, since
Step "1+2 combined" did not close first.

This is exactly the kind of friction that comes from working against an
unfamiliar library's own internal normal form for de Bruijn substitution
composition, not a sign that the underlying mathematical fact is false or
that `Foundation` lacks the tools — `Foundation` visibly proves harder
instances of the same kind of fact throughout `Bootstrapping/FixedPoint.lean`
and `Incompleteness/InductionSchemeDelta1.lean`. It is a mechanization gap,
not a mathematical one, and closing it would plausibly take a focused
follow-up session rather than a fresh attempt from scratch, now that the
three-step argument and the exact place it snags are both pinned down here.

**`RayoBoolos/Domination.lean` is deliberately *not* committed** — it
contained a `sorry` at the point this session stopped, and this project's
standing rule (matching K0-K6, `Encoding.lean`, `BoolosB0Core.lean`, and
this same session's `TNames.lean`) is no `sorry`/`admit` in anything
reported as done. What *is* committed from Step 4's work is
`RayoBoolos/Probe.lean` — a small, fully verified, sorry-free check of the
header-order/application-order convention (confirmed: listed application
arguments fill a semisentence's header names in the same left-to-right
order), which is genuinely useful, stands alone, and was load-bearing for
figuring out the `ProvablyTotal.graph` variable convention above.

## Files

- `rayo-lean-boolos/lakefile.toml`, `lake-manifest.json`, `lean-toolchain` —
  project setup, pinned to `Foundation` commit `31bb585`.
- `RayoBoolos/Sanity.lean` — Step 1 baseline check.
- `RayoBoolos/TNames.lean` — Step 3, closed.
- `RayoBoolos/Probe.lean` — small standalone convention check, closed.
- `RayoBoolos/Basic.lean` — placeholder, unused.
- `RayoBoolos/Domination.lean` — **not committed**; the Step 4 attempt,
  described above, left mid-proof with one `sorry`.

## Commit-signing note

Commits on this branch could not be signed in this environment: `git
config commit.gpgsign` is `true`, `gpg.format` is `ssh`, and the configured
SSH signing key resolves to an agent socket
(`$SSH_AUTH_SOCK=/tmp/ssh-.../agent.*`) that refuses connections
(`Error connecting to agent: Connection refused`), confirmed repeatedly
across the session, not a one-off. One `git commit` succeeded early in the session (the pre-existing,
already-staged B0 Lean core work from the prior session,
`rayo-lean/Rayo/BoolosB0Core.lean` — committed as this branch's starting
point before any of Steps 1-4 above); every commit attempt after that point
hung on `ssh-keygen -Y sign` waiting on the unreachable agent, up to and
including a detached background retry, which was killed after it made no
progress. Per this task's explicit instruction, `commit.gpgsign` was
**not** disabled to route around this. The work is committed as far as
signing allowed and otherwise staged/present in the working tree on branch
`boolos-b1-b3`; the operator will need to commit (or re-sign) the remainder
themselves, or restore SSH-agent access in this environment and re-run the
commit.
