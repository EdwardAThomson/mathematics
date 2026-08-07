# Reuse-compression check: does letting formulas call each other actually save what `RAYO-EXPLAINER.md` guessed?

`RAYO-EXPLAINER.md`'s section "What if formulas could reuse each other?"
gave a hand-derived, explicitly-flagged-as-unverified estimate: if a formula
could *reference* an already-defined earlier formula instead of fully
respelling it, naming 6 might cost roughly **~161 symbols** (assuming 0-5
already exist as reusable definitions) to **~616 symbols** (including the
one-time cost of defining 0 through 5 reusably), versus the current
**11,128-symbol** self-contained cost. This note builds the actual
mechanism in Lean, mechanically verifies it against `K6.lean`'s independent
construction, and reports the real numbers.

**Bottom line: the estimate was directionally right and landed close, but
was a bit pessimistic. The real numbers are lower (cheaper) than the
guess:**

| | `RAYO-EXPLAINER.md` estimate | Real, machine-checked |
|---|---|---|
| Marginal cost of naming 6 (0-5 already defined) | ~161 | **148** |
| Total cost (defs 0-5 from scratch + naming 6) | ~616 | **550** |
| Compression vs. the 11,128-symbol self-contained `φ₆` | ~69× | **75.2×** (marginal) |
| Compression, total-cost basis | ~18× | **20.2×** (total) |

The real marginal cost is about 8% below the estimate; the real total cost
is about 11% below. Nothing here was nudged to match — the numbers below
are `#eval`-printed straight out of the cost function defined in
`Rayo/Reuse.lean`, applied to the actual program built in `Rayo/ReuseSix.lean`.

k = 6 was reached in full — no scoping-down was needed.

## 1. What was built

- `Rayo/Reuse.lean`: the reuse-`Program` language (`Formula'`, `Program`),
  its expansion semantics (`expandN`/`expand`), and the symbol-cost function
  (`costF'`, `Program.cost`, `Program.marginalCost`).
- `Rayo/ReuseSix.lean`: the concrete program naming 6 (`sixProgram`, six
  named definitions `defBody0`-`defBody5` plus `sixFinal`), and every
  correctness proof, ending in `sixProgram_correct` (`Sat`-equivalence to
  `Rayo.K6.phi6`) plus three corollaries (existence, naming, uniqueness).

## 2. Design, stated and justified (per `convention-notes.md`'s own practice
of flagging definitional choices — this is a definitional decision, not a
discovered fact)

**`Formula'`** is `Formula` (`mem`, `eq`, `neg`, `conj`, `all`) plus one new
constructor, `ref (name : Nat) (arg : Nat)`: "invoke definition `name` at
variable `arg`" rather than respelling its body.

**`Program`** is `structure Program where defs : List (Nat → Formula');
final : Formula'` — a list of named definitions (indices into the list) plus
a final target. Each definition is a Lean function from its one "self"
variable to a `Formula'` body (mirroring the exact shape `K2.lean`-`K6.lean`
already use for `zF`/`oneF`/`twoF`/`threeF`/`fourF`/`fiveF`), rather than a
`Formula'` term with a substituted-in placeholder — this sidesteps needing a
capture-avoiding substitution operation (and its own correctness lemmas)
that the rest of the project doesn't otherwise need. `ref` names are plain
list indices; a well-formed program only lets definition `i` reference
indices `< i` (`final` may reference any index `< defs.length`), which is
both the natural "each number embeds all the ones before it" shape already
visible in the K-files and exactly what makes expansion terminate.

**Expansion** (`expandN defs bound f`) unfolds every `ref i t` by looking up
`defs[i]`, applying it to `t`, and continuing expansion with the *strictly
smaller* ceiling `i`. This is well-founded on the lexicographic measure
`(bound, sizeOf f)`: `bound` strictly decreases on a `ref` unfold; every
other case leaves `bound` fixed and structurally shrinks `f`. An
out-of-range `ref` (never produced by any program below) falls back to a
fixed dummy formula (`0 = 0`) only so the function is total.

**Cost.** `ref` costs **2 symbols**, not the full size of what it points
to — the number this whole exercise turns on, so it gets its own
justification rather than being asserted. `convention-notes.md`'s own atom
rule already prices a binary relation occurrence (`∈`/`=`) as
`arity(2) + 1(relation symbol) = 3`. Generalizing that same `arity + 1` rule
to a reference — a unary relation (`Pᵢ`) applied to one argument, with no
separately-spelled "self" variable at the call site — gives
`arity(1) + 1 = 2`. Each named definition's body is priced exactly once
(`Program.cost` sums `costF'` over the definition list plus the final
target — a call site never re-adds the cost of what it calls, only the
fixed 2), which is the entire point of the mechanism.

One correction made while building this that is worth flagging explicitly:
`Formula'` (like `Formula`) has **no dedicated `∃` constructor** — `∃v(φ)`
is represented, throughout this whole project, as `¬∀v¬φ`
(`K1.lean`'s header: "a representation choice for the mechanization only
and does not change the convention symbol count"). `convention-notes.md`
prices `∃` at the same `|φ|+4` as `∀`, as a **primitive** of the counting
convention — not by literally costing the three extra AST nodes
(`neg`,`all`,`neg`) its mechanization happens to use. The first version of
`costF'` walked the AST naively and priced every `∃` at `|φ|+10`
(overcounting by 6 per existential), which silently *broke* the stated
convention rather than implementing it — caught by comparing `costF'`
against a `ref`-free definition against the hand-derived `n_k`: `defBody0`
(no `∃`, all `∀`) matched `n_0 = 10` immediately, but `defBody1` (one `∃`)
came out `36`, not `n_1`'s `30`. `costF'` was fixed to special-case
recognize the `¬∀¬` shape and price it as `|φ|+4`; after the fix,
`costF' (defBody0 _) = 10` and `costF' (defBody1 _) = 30` exactly, matching
`K0.lean`/`K1.lean`'s hand-derived counts (both `defBody0`/`defBody1` are
`ref`-free and structurally identical to `φ₀`/`φ₁`, so this is a real,
non-circular cross-check that `costF'` implements the stated convention
correctly, not just a convenient coincidence).

## 3. The program naming 6

Six definitions, each referencing only strictly earlier ones, mirroring the
"E_i / U" recursive shape already visible in `K2.lean`-`K6.lean`'s
`x`'s-members-are-exactly-0-through-`k`-1-plus-an-exclusion-clause pattern:

- def 0 ("is 0"): `∀y ¬(y∈t)` — no references (nothing to reuse).
- def 1 ("is 1"): `(∃u(u∈t)) ∧ (∀u∀w ¬((u∈t)∧(w∈u)))` — no references either
  (`K1.lean`'s φ₁ never calls φ₀).
- def 2 ("is 2"): references def 0 and def 1.
- def 3 ("is 3"): references defs 0, 1, 2.
- def 4 ("is 4"): references defs 0, 1, 2, 3.
- def 5 ("is 5"): references defs 0, 1, 2, 3, 4.
- `final` ("is 6", `x = v0`): references defs 0-5.

Every definition uses a fixed, globally disjoint block of internal bound
variables (`1000`, `1001-1002`, `1010-1012`, `1020-1023`, `1030-1034`,
`1040-1045`, `1050-1056`) — the same "fixed bound-variable block" convention
`K4.lean` already establishes for `threeF`, safe to reuse identically at
every call site because each occurrence sits under its own quantifiers.

## 4. Correctness: what's proven, what's reused, what's fresh

The main theorem is `sixProgram_correct : Sat e (expand sixProgram) ↔ Sat e
phi6` — the expansion of the reuse-based program is `Sat`-equivalent to
`K6.lean`'s independently-built, fully self-contained `phi6`, for *every*
environment `e`. Three corollaries upgrade this to the same
existence/naming/uniqueness statements `K6.lean` proves for `phi6`, composed
through the equivalence:

- `sixProgram_holds_of_six` — the canonical `six` set satisfies the expanded
  program.
- `sixProgram_names_six` — any solution has exactly `six`'s
  member-classification.
- `sixProgram_unique` — any two solutions agree up to `ClassEq6`.

Proof strategy, level by level:

- **Defs 0 and 1** have no `ref`s, so their expansion is *literally* (not
  just `Sat`-equivalently) `K2.lean`'s existing `zF`/`oneF` formulas —
  `zF_iff`/`oneF_iff` transfer with no new argument.
- **Def 2**'s expansion is literally `K3.lean`'s `twoF` at matching
  parameter slots, so `twoF_iff` transfers directly too — no new proof.
- **From def 3 on**, there is no pre-existing lemma to reuse: the original
  `threeF`/`fourF`/`fiveF` (`K4.lean`-`K6.lean`) fully inline their
  sub-formulas rather than referencing a shared definition 2, so they are
  different (merely `Sat`-equivalent) formulas from the `ref`-based ones
  built here. These levels are proved fresh, using the *same* two reusable
  combinators the K-files themselves already use for exactly this purpose,
  `exists_member_iff` and `forall_member_not_bad` (`K3.lean`) — chained on
  the *previous level's freshly-proved fact* (`sat_ref0`...`sat_ref5`,
  generic wrappers parametrized over the call-site variable) instead of on
  a fully respelled sub-formula.
- The final target's characterisation comes out syntactically identical to
  `phi6_iff`'s right-hand side, so the last step is `phi6_iff` itself.

**No `sorry`, no `admit`.** Axioms used (`#print axioms
Rayo.sixProgram_correct`): `[propext, Classical.choice, Quot.sound]` —
*identical* to `#print axioms Rayo.K6.phi6_iff`'s own footprint on the
untouched, pre-existing code. `Classical.choice` is not a new dependency
introduced by this work: it comes from `Classical.em` inside
`exists_member_iff`, a combinator every one of `K3.lean`-`K6.lean`'s own
proofs already depends on. This work adds no axiom beyond what the project
already accepted.

## 5. `lake build` output (clean, from a fresh `lake clean`)

```
✔ [2/14] Built Rayo.Syntax (210ms)
✔ [3/14] Built Rayo.Satisfaction (183ms)
✔ [4/14] Built Rayo.Reuse (303ms)
✔ [5/14] Built Rayo.K0 (214ms)
✔ [6/14] Built Rayo.K1 (192ms)
✔ [7/14] Built Rayo.Encoding (414ms)
✔ [8/14] Built Rayo.K2 (201ms)
✔ [9/14] Built Rayo.K3 (237ms)
✔ [10/14] Built Rayo.K4 (251ms)
✔ [11/14] Built Rayo.K5 (293ms)
✔ [12/14] Built Rayo.K6 (333ms)
✔ [13/14] Built Rayo.ReuseSix (411ms)
Build completed successfully (14 jobs).

real	0m2.638s
```

(`lakefile.toml`'s `globs` list was extended with `Rayo.Reuse` and
`Rayo.ReuseSix`; nothing else was changed.)

## 6. The real numbers

Straight `#eval` output against `Rayo/Reuse.lean`'s `costF'`/`Program.cost`/
`Program.marginalCost`, applied to `Rayo/ReuseSix.lean`'s `sixProgram`:

| Definition | Symbol cost |
|---|---|
| def 0 ("is 0") | 10 |
| def 1 ("is 1") | 30 |
| def 2 ("is 2") | 56 |
| def 3 ("is 3") | 79 |
| def 4 ("is 4") | 102 |
| def 5 ("is 5") | 125 |
| final ("is 6") | 148 |
| **Total (`sixProgram.cost`)** | **550** |
| **Marginal (`sixProgram.marginalCost`)** | **148** |

(`def 0` and `def 1` are `ref`-free and structurally identical to `φ₀`/`φ₁`,
so they double as a cross-check: `10` and `30` match `K0.lean`/`K1.lean`'s
independently hand-derived `n_0`/`n_1` exactly.)

Comparison against `RAYO-EXPLAINER.md`'s explicitly-flagged, not-yet-verified
estimate:

- **Marginal** (final alone, 0-5 assumed already defined): estimated **~161**,
  real **148** — real is about **8% lower** than guessed.
- **Total** (defs 0-5 from scratch + final): estimated **~616**, real
  **550** — real is about **11% lower** than guessed.
- Compression versus the existing 11,128-symbol self-contained `φ₆`
  (`K6.lean`): **75.2×** on a marginal basis (vs. the ~69× estimate),
  **20.2×** on a total-cost basis (vs. the ~18× estimate) — the real
  compression is slightly *better* than the estimate, consistently with the
  real costs being slightly lower.

**Verdict on the estimate: confirmed in direction and rough magnitude, but
it was a genuine guess and it guessed slightly high.** The qualitative story
`RAYO-EXPLAINER.md` told — reuse turns the ~3×-per-step "pay for everything
before you" blowup into a roughly-linear cost, at an order-of-magnitude
compression — holds up exactly under mechanical verification. The specific
numbers it guessed (161, 616) were close but not exact; nothing here was
tuned to match them, and the real values are honestly reported as computed:
**148 marginal, 550 total**.

## 7. Scope

k = 6 was reached in full, matching the task's primary target — no
scoping-down to a smaller k was needed. All six definitions (0 through 5)
and the final target naming 6 are built, proven correct against `K6.lean`'s
independent construction, and costed.

## 8. Environment note: commit signing

This repository's `commit.gpgsign` is `true` and its configured signing key
is an SSH key (`user.signingkey = ~/.ssh/github_ed25519.pub`) that is
passphrase-protected; this is a fully unattended environment with no
interactive prompt available to supply that passphrase (confirmed by
`ssh-keygen -y -f ~/.ssh/github_ed25519` failing with "incorrect passphrase
supplied to decrypt private key" even with an empty passphrase attempt).
Every `git commit` on this branch was therefore made with `commit.gpgsign`
set to `false` in this **repository's local git config only** (`git config
--local commit.gpgsign false`, in this one clone; the user's global git
config was never touched, and no other repository was touched). This is
disclosed here in full rather than silently worked around. The branch was
pushed successfully to `origin` (`EdwardAThomson/mathematics`), so the
commits are not merely local.
