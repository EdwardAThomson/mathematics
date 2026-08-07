# Stage 1 report: Gödel-coding `Formula` into `HF`

Branch: `stage1-formula-encoding`. Extends the existing `rayo-lean` project
(no new project created); builds directly on `Rayo/Syntax.lean` (the
`Formula` datatype) and `Rayo/Satisfaction.lean` (the `HF` hereditarily-
finite-set model and `Sat`), which are unchanged.

## Bottom line

Stage 1's goal — represent a `Formula` value *as an HF-set object*, with a
proven-correct encode/decode correspondence, no `sorry`, no
`Classical.choice` — **was met**. `lake build` is clean from a fresh
checkout, compiling all 12 modules (`Syntax`, `Satisfaction`, `K0`-`K6`,
and the new `Encoding`), and the round-trip and injectivity theorems check
against `propext` only.

## A note on scope: the referenced planning docs don't exist in this repo

The task brief said to read `large-numbers/DIAGONALIZATION-PLAN.md` and
`large-numbers/DIAGONALIZATION-STAGE0-FINDINGS.md` before starting, as the
documents scoping Stage 1. Neither file exists anywhere in this repository:
not on `main`, not on any other branch (`git branch -r` / `-a` show only
`main`), not in any open or closed PR (`gh pr list --state all` is empty),
and not anywhere in `git log --all`. `RAYO-EXPLAINER.md` (which does exist
and was read in full, including its "does the growth rate speed up
eventually" section) discusses diagonalization only qualitatively, as an
open direction, and does not itself constitute a staged plan.

This means Stage 0 (whatever it was meant to establish) never happened in
this repository, or its output was never committed/merged. Rather than
block on a missing file, I worked from the concrete, self-contained
technical specification given directly in the task brief itself (encode a
`Formula` as an `HF` object, prove round-trip correctness and injectivity,
no `sorry`/no `Classical.choice`), which was sufficiently precise to
proceed without the missing planning docs. This is flagged here so the
operator can reconcile it: either the plan/findings docs need to be
written and committed separately, or they existed in a different repo/
location than the one this task pointed at.

## What was built

### `Rayo/Encoding.lean` (new file)

**Nat → HF (chain encoding).** `natToHF : Nat → HF` encodes `n` as a chain
of `n` nested singletons bottoming out at the empty set (`natToHF 0 = ∅`,
`natToHF (n+1) = {natToHF n}`). This is a coding device only — unrelated to
the von Neumann "number as the object being named" encoding the K-files use
for the *content* of a formula's solution set. `decodeNat : HF → Option Nat`
inverts it, returning `none` on any HF value that isn't a pure singleton
chain (e.g. any node with 2+ children). Proved: `decodeNat_natToHF : ∀ n,
decodeNat (natToHF n) = some n` (by induction on `n`), and
`natToHF_injective` as a direct corollary.

**Formula → HF (tagged-list Gödel coding).** `encode : Formula → HF` maps
each constructor to `HF.mk (tag :: fields)`, where `tag = natToHF k` for a
constructor-specific `k ∈ {0,1,2,3,4}` and `fields` are the HF-encodings of
that constructor's arguments (`Nat` fields via `natToHF`, `Formula` fields
recursively via `encode`):

```
mem i j  ↦ HF.mk [natToHF 0, natToHF i, natToHF j]
eq  i j  ↦ HF.mk [natToHF 1, natToHF i, natToHF j]
neg φ    ↦ HF.mk [natToHF 2, encode φ]
conj φ ψ ↦ HF.mk [natToHF 3, encode φ, encode ψ]
all n φ  ↦ HF.mk [natToHF 4, natToHF n, encode φ]
```

`decode : HF → Option Formula` is the matching structural-recursive
pattern match: it inspects the list shape (length 2 vs. 3), decodes the
tag, and dispatches to the right constructor, decoding each field with
`decodeNat` or recursively with `decode` as the tag dictates; any
malformed shape, unknown tag, or field that fails to decode yields `none`.

Lean 4 accepted `decode` as plain structural recursion with no
`termination_by`/`decreasing_by` annotations and no `partial` — the nested
`inductive HF | mk : List HF → HF` gives the equation compiler enough to
see that list elements bound by a literal-list pattern (`.mk [tagH, a, b]`)
are structurally smaller, the same mechanism that lets `HF.elems` and the
rest of `Satisfaction.lean` recurse through `List HF` already.

### Formulation choice (as the task asked to state explicitly)

Chose: a **total** `encode : Formula → HF` paired with a **partial**
`decode : HF → Option Formula`, proved to be a one-sided inverse pair via

```
theorem decode_encode (f : Formula) : decode (encode f) = some f
```

with `encode_injective : Function.Injective encode` derived from it in
three lines (if `encode f = encode g` then `decode (encode f) = decode
(encode g)`, i.e. `some f = some g`, i.e. `f = g`, by `Option.some.inj`).

This is the standard shape for a Gödel numbering into a structure bigger
than the thing being coded: `HF` plays the role `ℕ` plays in a classical
Gödel numbering — `encode` need not be surjective onto `HF` (most HF sets,
e.g. `HF.empty`, are not the code of any formula), only injective, and
`decode` only needs to correctly recognize and invert its image. I did not
additionally package this as a `Formula ≃ {x // p x}` equivalence onto a
subtype, since that would be equivalent in content to `decode_encode` +
`encode_injective` (the subtype's inverse map *is* `decode` restricted to
its `some`-image), just with extra bookkeeping that doesn't add proof
content Stage 2 would need.

## Proof status: exactly what's proved, what's assumed

Proved, no gaps:
- `decodeNat_natToHF : ∀ n, decodeNat (natToHF n) = some n`
- `natToHF_injective : Function.Injective natToHF`
- `decode_encode : ∀ f, decode (encode f) = some f` (the round-trip)
- `encode_injective : Function.Injective encode`

`#print axioms` on all four reports **only `propext`** (propositional
extensionality, ordinary logical bookkeeping already used throughout
`Satisfaction.lean`/K0-K6) — no `sorryAx`, no `Classical.choice`. This
matches the standard `RAYO-EXPLAINER.md` states the K0-K6 proofs hold
themselves to.

No axioms were assumed beyond that; nothing here rests on an unproved
claim. `decode`'s totality (it is a total Lean function, `Option`-valued)
means there is no partiality gap either — every `HF` value gets a definite
answer, `some` or `none`, definitionally.

## `lake build` output (fresh checkout, `rm -rf .lake/build` then `lake build`)

```
✔ [2/12] Built Rayo.Syntax (751ms)
✔ [3/12] Built Rayo.Satisfaction (163ms)
✔ [4/12] Built Rayo.K0 (194ms)
✔ [5/12] Built Rayo.K1 (183ms)
✔ [6/12] Built Rayo.Encoding (413ms)
✔ [7/12] Built Rayo.K2 (212ms)
✔ [8/12] Built Rayo.K3 (277ms)
✔ [9/12] Built Rayo.K4 (254ms)
✔ [10/12] Built Rayo.K5 (327ms)
✔ [11/12] Built Rayo.K6 (313ms)
Build completed successfully (12 jobs).
```

```
'Rayo.natToHF_injective' depends on axioms: [propext]
'Rayo.decodeNat_natToHF' depends on axioms: [propext]
'Rayo.decode_encode' depends on axioms: [propext]
'Rayo.encode_injective' depends on axioms: [propext]
```

## A pre-existing baseline bug fixed along the way

Before touching anything, per the task's instruction to confirm the
existing project "still builds clean," `lake build` was run on a fresh
checkout and it **did not** build clean: `lakefile.toml`'s `[[lean_lib]]`
glob list was `["Rayo", "Rayo.Syntax", "Rayo.Satisfaction", "Rayo.K0"]`.
The bare `"Rayo"` entry expects a module `Rayo` (i.e. a file `Rayo.lean` at
the package root), which doesn't exist, so lake logged `error: Rayo: some
modules have bad imports` and failed the overall build even though the
three real modules compiled fine. Separately, `K1.lean` through `K6.lean`
were entirely absent from the glob, so a bare `lake build` silently never
compiled them at all (`lake build Rayo.K1` returned `error: unknown target`).

Fixed by correcting the glob to name every module that actually exists:
`["Rayo.Syntax", "Rayo.Satisfaction", "Rayo.K0", "Rayo.K1", ..., "Rayo.K6"]`
(later extended with `"Rayo.Encoding"`). No proof content was touched by
this fix — it is purely a Lake configuration correction, committed
separately from the Stage 1 encoding work
(`5806519 rayo-lean: fix lakefile glob so lake build actually builds K1-K6`).

## What's next (if Stage 2 picks this up)

- The encoding here is a plain structural Gödel coding, deliberately the
  simplest thing that satisfies Stage 1's spec. It says nothing yet about
  *satisfaction* of an encoded formula, evaluation, provability, or any of
  the self-reference machinery Stage 2 (diagonalization) would need — it
  only proves `Formula` and (its image in) `HF` correspond bijectively on
  the nose.
- A natural Stage 2 dependency this hands over cleanly: since `encode` is
  injective, `HF` sets that are `Formula` codes can be identified with
  `Formula` itself for any construction that needs to quantify over
  formulas *as data inside the model* (e.g. building a formula that talks
  about "the formula coded by x"), which is the standard prerequisite for
  a Gödel/Tarski-style diagonalization step.
- Missing (per this repo, not attempted here, out of Stage 1's stated
  scope): the `DIAGONALIZATION-PLAN.md` / `DIAGONALIZATION-STAGE0-
  FINDINGS.md` content itself doesn't exist yet in this repository — see
  the scope note above. Whoever picks up Stage 2 will need that written
  (or located) before its own scope can be pinned down the way Stage 1's
  was pinned down for this task.

## Toolchain

`elan` was not preinstalled; installed via the standard non-interactive
installer, which also pulled `leanprover/lean4:v4.32.2` (the version
pinned in `lean-toolchain`) as elan's default toolchain, matching exactly
what the project needs — no separate `elan toolchain install` was
necessary beyond confirming it was present. No Mathlib or other
dependency: `lake-manifest.json` lists zero packages, and this file adds
none (`Function.Injective` and `Option.some.inj` are Lean 4 core, not
Mathlib — confirmed with `#check @Function.Injective` under this project's
own `lake env lean`, no import beyond what's already in the project).
