# Phase R0: is Rayo's own construction well-defined?

Phase R0 of `RAYO-RIGOR-PLAN.md` (the higher-risk fork of
`DIAGONALIZATION-PLAN.md`) — the "make Rayo's actual trick rigorous" task. The
plan is explicit that this phase is paper-only, genuinely open-ended, and
*"might resolve into 'this doesn't hold up as stated' rather than 'this is hard
but true.'"* This note is the attempt, and it lands in between: **the
construction is consistent (no paradox) and it does define a specific number —
but not from "first-order set theory" as the popular description says. Its
well-definedness rests on a second-order / set-theoretic-realist commitment
that the popular accounts leave out, and without that commitment the
construction trivializes.** That is a real, reportable R0 finding
(`RAYO-RIGOR-PLAN.md` exit condition R0.4, case 2), not a failure.

No Lean here (paper phase; and the Lean toolchain is egress-blocked in this
environment anyway — see `BOOLOS-B0-WELLDEFINEDNESS.md` §7). This is an
assembly of standard set-theory facts into a precise verdict, which — per
`DIAGONALIZATION-STAGE0-FINDINGS.md` §3, "no formalization of Rayo's function
exists anywhere ... asserted in prose, not proven" — nobody appears to have
written down for Rayo's construction specifically.

**Plain-English summary.** Rayo's number is usually sold as "the biggest number
you can pin down with a googol symbols of *first-order* set theory." The catch
this note makes precise: to even say *which* numbers a formula pins down, you
need a notion of "true in the universe of sets," and — by a classical theorem
of Tarski — that notion is **not itself expressible in first-order set
theory**. Rayo supplies it from one level up (a second-order "satisfaction"
predicate). That extra level is doing essential work, and whether it exists at
all is a real assumption about set theory (a "there is one correct truth"
stance). Grant that assumption and Rayo's number is a genuine, specific number
and there's no paradox. Withhold it and the construction collapses — it names
nothing. So Rayo's number is well-defined *relative to a commitment the popular
one-line description hides*, not from bare first-order set theory.

---

## 1. The actual claim, stated precisely

The microlanguage (`rayo-notes/literature-notes.md` §2, corroborated against
the published sources): first-order formulas over the single binary relation
`∈`, with `=, ¬, ∧, ∃` and parentheses, variables `x₁, x₂, …`, interpreted
over the **von Neumann universe V** (the domain is all sets; `∈` is real
membership). Numbers are von Neumann naturals (`0 = ∅`, `k+1 = k ∪ {k}`).

> **Naming.** A formula `φ` with one free variable `x₁` **names** `m ∈ ℕ` iff
> (a) some assignment sending `x₁ ↦ m` satisfies `φ`, and (b) every satisfying
> assignment sends `x₁ ↦ m`. (`literature-notes.md` §2: unique denotation.)

> **The function and the number.**
> ```
>   Rayo(n) = 1 + sup{ m ∈ ℕ : some one-free-variable φ with |φ| ≤ n names m }
>   Rayo's number = Rayo(10^100).
> ```

The essential structural point, easy to lose: **the formulas being counted are
first-order**, but the word **"satisfies"** in the naming definition is a
**truth-in-V** predicate for those first-order formulas, and *that* predicate
is where the second-order machinery lives. Rayo's construction is a definition
of that satisfaction predicate. Following the published presentations (Googology
Wiki; Wikipedia; the sources below), it is the second-order statement

```
  Sat(φ, s)  :≡  ∀R [ SatRel(R) → R(φ, s) ]
```

where `SatRel(R)` says the relation/class `R` obeys the Tarski recursion
clauses — `R("xᵢ∈xⱼ", s) ↔ s(xᵢ)∈s(xⱼ)`, `R("¬ψ",s) ↔ ¬R(ψ,s)`,
`R("ψ∧χ",s) ↔ R(ψ,s)∧R(χ,s)`, `R("∃xᵢ ψ",s) ↔ ∃(xᵢ-variant t of s) R(ψ,t)`,
and the `=` clause. The `∀R` quantifier is **second-order** (over relations on
the domain), and this is exactly what evades Tarski's undefinability theorem:
truth-in-V is not first-order definable, but the *intersection of all
satisfaction relations* is second-order definable.

Two obligations must be discharged to call this well-defined
(`RAYO-RIGOR-PLAN.md` R0.2): **(a)** no route from the construction to `False`
(consistency — the Berry-paradox worry), and **(b)** it actually pins down a
specific number matching the intended meaning, not merely "doesn't crash."

---

## 2. Which second-order semantics? (the choice R0.1 forces)

`Sat`'s `∀R` ranges over "all relations `R`." *Which* relations exist is not
neutral, and Rayo's account never says (`DIAGONALIZATION-STAGE0-FINDINGS.md`
§4). Framed over V, the honest translation of the plan's "full vs. Henkin"
choice is a choice of **class theory**:

- **Full / standard second-order semantics ≈ Morse–Kelley (MK).** Second-order
  quantifiers range over *all* subclasses of the domain; class comprehension is
  **impredicative** (a class may be defined by a formula that itself quantifies
  over all classes). This is the reading matching Rayo's stated **realist**
  intent — the sources below say Rayo's number is "understood in terms of a
  platonistic or realist view of set theory, in which there is a single correct
  way to interpret the truth of sentences in first-order set theory."
- **Henkin / predicative semantics ≈ NBG (von Neumann–Bernays–Gödel).**
  Second-order quantifiers range only over a *designated* sub-collection of
  classes; comprehension is **predicative** (no class quantifiers in the
  defining formula). Tamer, closer to a many-sorted first-order theory — but,
  as R0.1 warns, a real departure from Rayo's apparent intent.

This is not bookkeeping: §5 shows it changes whether there is anything to be
well-defined *about*.

---

## 3. Obligation (a): consistency — no Berry paradox

**Claim: the construction is consistent, unconditionally (either semantics). No
route to `False`.**

The Berry worry is: "Rayo's number = the least number bigger than everything
namable in ≤ googol symbols" looks like "the least number not namable in
< googol symbols," which classically self-refers into paradox. It does **not**
here, because of a **Tarskian stratification** that the construction respects:

- The formulas that do the naming live in the **object language** (first-order
  over `∈`).
- The definition of `Rayo's number` — the `sup` over what those formulas name —
  lives in the **metalanguage** (it quantifies over *all* object formulas and
  uses the second-order `Sat`). By Tarski's undefinability theorem, this
  metalinguistic definition is **not** itself equivalent to any first-order
  object formula.

So the object language never contains a formula asserting its own naming-power,
and the paradox never forms. Concretely: could some object formula `φ` of
`≤ 10^100` symbols name `Rayo's number R` itself? If it could, then `R` would be
among the numbers named in-budget, so `R ≤ sup = R − 1` — contradiction; hence
**no in-budget formula names R**, and the construction is self-consistent by
design. This is forced, not lucky: `R`'s only canonical description is the
metalinguistic (second-order) one, which Tarski keeps out of the first-order
object language; and the brute-force "enumerate the predecessors of `R`"
formula that *does* exist is astronomically longer than a googol (it grows
`~3ᵏ`, from the `rayo-lean` K0–K6 measurements, and `R` is far larger than any
tower). Rayo's own account keeps exactly this stratification — its "non-semantic
substitute for the notion of being named" (`DIAGONALIZATION-STAGE0-FINDINGS.md`
§3) is precisely the device that expresses naming without letting the object
language name its own Berry number. **(a) holds, and needs no choice from §2.**

---

## 4. Obligation (b): it names a specific number — and this is where it bites

**Claim: (b) holds iff a unique satisfaction relation for the first-order
language over V exists in the range of `Sat`'s `∀R`. That is exactly the §2
choice, and it is a substantive set-theoretic commitment.**

`Sat` is only the intended truth-in-V predicate if the Tarski clauses have a
**unique** solution `R` and it is **in range**. Break it into the two semantics:

- **Under full semantics / MK.** Impredicative comprehension forms the class
  `Sat = {(φ,s) : ∀R(SatRel(R) → R(φ,s))}` outright, and induction on formula
  structure shows it is the *unique* relation obeying the clauses. So
  `MK ⊢ ∃!R SatRel(R)`, `Sat` is that relation, naming is the intended relation,
  and `Rayo(n)` is a definite natural number. This is the **same** fact that
  makes MK prove `Con(ZFC)` — MK's first-order **satisfaction class / truth
  predicate for V** — a standard result in the metatheory of class theories
  (and the subject of active work, e.g. the arxiv paper below on Kelley–Morse
  and satisfaction/class-choice). Rayo's construction is, in effect, *running
  MK's truth predicate for V.*

- **Under predicative / Henkin semantics / NBG.** The impredicative `Sat` class
  need **not** be in the designated collection — indeed NBG cannot prove it
  exists, since NBG is conservative over ZFC and a truth class for V would give
  `Con(ZFC)` (standard: Novak–Mostowski–Shoenfield conservativity). If the true
  satisfaction relation is not in range, `Sat`'s `∀R` **degenerates**: with no
  in-range `R` obeying the clauses, `∀R(SatRel(R) → R(φ,s))` is *vacuously true*
  for every `φ, s` (dually, the `∃R` form is vacuously false). Feed that into
  the naming definition (§1): clause (b) `∀s(Sat(φ,s) → s(x₁)=m)` becomes
  `∀s(s(x₁)=m)`, which is false — so **no formula names any number**, the named
  set is empty, and `Rayo(n)` collapses to a trivial value. Not "a different,
  smaller Rayo's number" — the construction stops naming anything at all.

**Verification note (checked 2026-08-07).** Because this section is
load-bearing — for the verdict here and for `KAPPA-TABLE.md`'s new
diagonalization-family row — the MK claim was checked against the literature
rather than asserted from memory, including against the one paper whose title
(*"the surprising weakness of Kelley–Morse set theory"*) could have undercut it.
It does not. Confirmed: **every model of KM carries a truth-predicate class `Tr`
coding first-order truth over V, obtained precisely from KM's impredicative
class comprehension, and KM ⊢ Con(ZFC)** (Hamkins; Gitman; the arXiv paper
below). The "weakness" that paper establishes is about **class-choice and
elementary transfinite recursion** principles — the things KM does *not* prove —
**not** about the basic first-order truth class, which is exactly the object
§4 uses. Two precision riders, neither affecting the verdict: (i) the uniqueness
invoked above is uniqueness of the first-order truth class under the *standard*
(internal-ℕ) formula-indexing, proved by ordinary induction on formula
complexity — not a transfinite class-recursion, so the ETR weakness is
irrelevant to it; (ii) the well-known non-uniqueness of *satisfaction classes
over nonstandard models* (Krajewski and successors) is a separate
model-theoretic phenomenon about nonstandard formula codes, orthogonal to KM's
internal proof that its first-order `Tr` for the real V is unique. So the §4
claim stands as stated.

So **(b) is conditional**: it holds precisely under the impredicative /
full-semantics / realist reading, and fails (trivializes) otherwise. The choice
in §2 is the difference between "Rayo's number is a specific enormous natural
number" and "Rayo's number names nothing."

---

## 5. The R0 verdict

Assembling §3–§4:

> **Rayo's construction is consistent (no paradox), and under full second-order
> semantics — equivalently, an impredicative class theory (MK) providing a
> truth predicate for V, equivalently the set-theoretic realism Rayo intends —
> it does define a specific natural number. But its well-definedness is *not*
> inherited from "first-order set theory": the essential work is done by a
> second-order satisfaction predicate whose existence is a nontrivial
> set-theoretic commitment (MK-over-NBG strength; a truth class for V; a single
> correct truth-in-V). Under a predicative / Henkin background that withholds
> that commitment, the construction trivializes and names nothing.**

Mapping to `RAYO-RIGOR-PLAN.md`'s exit conditions R0.4: this is **case 2** —
"the standard-semantics version is provable, but only with set-theoretic
assumptions beyond a fixed background theory; Rayo's number as popularly
described is not a single well-defined natural number without additional
specification the popular accounts omit." The specific omitted specification is
now named: *an impredicative second-order background providing a satisfaction
relation for the whole universe.* Two riders:

- **The popular one-liner is misleading in a locatable way.** "First-order set
  theory, a googol symbols" hides that the *definition of naming* is
  second-order and set-theoretically loaded. The first-order formulas are the
  cheap part; the truth predicate over V is the expensive part.
- **Even granting full semantics, the value is universe-relative.** Truth-in-V
  is not absolute across models of set theory, so `Rayo(n)`'s value can differ
  between models. It is a definite natural number *inside* a fixed realist
  universe, not an absolute one computable from the axioms — which is why the
  realist framing in the sources is load-bearing, not decorative.

None of this is a *new theorem* — it is Tarski's undefinability, the MK truth
class, and NBG conservativity, three standard facts, assembled into a verdict
about Rayo's construction that (per Stage 0) had not been assembled before.

---

## 6. A correction this forces in `RAYO-EXPLAINER.md`

`RAYO-EXPLAINER.md` ("does the growth rate speed up eventually?") describes the
real Rayo construction as building "something self-referential — roughly, 'the
smallest number that no formula shorter than N symbols can name'" and contrasts
it with the K0–K6 enumerate-predecessors strategy. R0 sharpens this, and one
phrasing there should be reconciled:

- **The self-reference is entirely at the meta level**, not inside the object
  formulas. The object formulas Rayo counts are ordinary first-order set-theory
  formulas; they do **not** invoke `Sat` internally (they can't — `Sat` is
  second-order, and Tarski blocks a first-order formula from expressing
  truth-in-V). The Berry-like "smallest number no short formula names" lives in
  the *metalinguistic* definition of `Rayo's number`, above the object language.
- **The growth comes from set theory's ontological reach, not from internal
  diagonalization.** First-order set theory over V can name titanic numbers in
  few symbols because it can *refer to* huge sets — cardinalities of iterated
  power sets, large-cardinal-indexed constructions, and so on — not because
  individual formulas run a Busy-Beaver-style self-reference. So "diagonalization
  beats enumeration" is true **as a statement about the meta-level definition**
  (`Rayo` outruns any fixed naming strategy), but it should not be read as the
  object formulas doing self-reference the way `RAYO-EXPLAINER.md`'s wording can
  suggest. The `rayo-lean` K0–K6 work measured one concrete object-level
  strategy; Rayo's advantage over it is set-theoretic expressive power plus the
  meta-level `sup`, not an object-level diagonal trick.

(Recommend adding a one-paragraph reconciliation note to `RAYO-EXPLAINER.md` if
this R0 finding is accepted — not silently editing the frozen explainer.)

---

## 7. Why the Boolos fork (#2) is genuinely the safer one — now precise

R0 explains, sharply, *why* `BOOLOS-FUNCTION-PLAN.md` is lower-risk. The single
hardest thing here is obligation (b): needing a **truth predicate for V**, which
forces an MK-strength second-order commitment. Boolos's construction makes one
swap — **truth → provability** (`BOOLOS-B0-WELLDEFINEDNESS.md` §5) — and

- `Prov_T(⌜ψ⌝)` **is** first-order expressible (Σ₁, an arithmetized proof
  search), so **no satisfaction class is needed** and Tarski never bites;
- consistency of the base theory (a far weaker commitment than a truth class for
  V) suffices for its well-definedness, which Boolos B0 discharged in ordinary
  arithmetic.

So the two forks differ exactly at the commitment R0 isolates: **Rayo needs
truth-in-V (MK-ish); Boolos needs only a provability predicate (PA-ish).** That
is the real content of "safer," and it is why #2 could close its B0 on paper
with nothing exotic while #3's R0 closes only relative to set-theoretic realism.

---

## 8. Honest limits

- **Scope.** R0 resolves *well-definedness* — obligations (a) and (b). It does
  **not** prove Rayo's *growth rate* (that `Rayo` dominates the functions of any
  particular hierarchy); that is a separate, harder question and is not touched
  here.
- **Standard facts, novel assembly.** The three load-bearing facts (Tarski
  undefinability; MK proves a truth class for V / `Con(ZFC)`; NBG is
  conservative over ZFC) are textbook metatheory of class theories. The
  contribution is assembling them into a precise verdict on Rayo's construction,
  which had not been done (Stage 0). No claim of a new theorem.
- **A defensible reading, not the only one.** Rayo's account is underspecified
  (§2), so this analysis commits to the full-semantics/realist reading as the
  one matching his stated intent. A committed Henkin-semantics reading would
  reach the "trivializes" branch; a reading that builds the truth predicate into
  a *fixed* strong background theory (e.g. working inside MK from the start)
  would make (b) unconditional at the cost of conceding the omitted commitment
  openly. All three are consistent with §5's verdict; they differ only in which
  clause of it they emphasize.
- **Paper, not machine-checked.** Unlike K0–K6 / Stage 1, nothing here is
  Lean-verified.

---

## 9. Handoff: R1–R3 (Lean), if this is pursued

`RAYO-RIGOR-PLAN.md` R0.4 says a closed R0 proceeds to R1. Given the verdict,
the honest scoping for a mechanized follow-up is:

1. **What R0 licenses formalizing is a *relative* result**, not "Rayo's number
   is well-defined" full stop. The Lean-checkable statements are: (a) the
   consistency/stratification argument (§3), which is clean and does not need a
   truth class; and (b) the conditional "given a satisfaction class for the
   object language over a model, naming is functional and `Rayo(n)` is a
   well-defined `ℕ`" (§4, MK branch) — *plus* its converse degeneration (§4, NBG
   branch), which is the more novel half.
2. **The satisfaction machinery** (`RAYO-RIGOR-PLAN.md` R1): the nearest real
   precedent is Paulson's ZF-Constructible Isabelle `Sat` **for a set-sized
   model M** — which is the *right* object for a Lean-checkable relative result,
   and sidesteps truth-in-full-V (which is not formalizable as a single Lean
   `Prop` for the same Tarski reason). Check `Foundation`'s
   `SetTheory/TransitiveModel.lean` first (`RAYO-RIGOR-PLAN.md` R1). Both routes
   need Mathlib, so — as with the Boolos fork — this is a separate,
   Mathlib-scale sub-project, not an extension of the self-contained
   `rayo-lean`.
3. **Recommendation.** The paper R0 verdict is the valuable, novel deliverable
   and stands on its own (it is the first precise well-definedness account of
   Rayo's construction). A mechanized R1–R3 would verify the *relativized*
   version over a set model — worth doing for assurance, but it will not, and
   cannot, verify "Rayo's number is well-defined over V" as a bare Lean theorem;
   that is Tarski-blocked, and saying so is part of the finding. If a single
   next step is wanted, formalize the **degeneration** direction (§4, NBG
   branch) over a toy model — it is the part no prior work states and it is the
   sharpest way to make "the commitment is load-bearing" machine-checked.

---

## 10. Summary

- **R0 attempted and closed — as a verdict, not a vindication.** Rayo's
  construction is **consistent** (§3, unconditional — the Berry paradox is
  blocked by Tarskian object/meta stratification) and **names a specific
  number** (§4) **only under an impredicative second-order / set-theoretic-
  realist commitment** (full semantics ≈ MK ≈ a truth predicate for V). Under a
  predicative/Henkin background it **trivializes and names nothing**.
- **The popular description is incomplete in a locatable way (§5):** "first-order
  set theory + a googol symbols" hides that *naming* is defined by a second-order
  truth predicate over V whose very existence is the load-bearing assumption. So
  Rayo's number is well-defined *relative to* that commitment, and its value is
  universe-relative even then — not a single absolute number derivable from bare
  first-order set theory.
- **This is the plan's exit-condition case 2** (`RAYO-RIGOR-PLAN.md` R0.4): a
  real, reportable finding, and — per `DIAGONALIZATION-STAGE0-FINDINGS.md` §3 —
  the first precise well-definedness account of Rayo's construction anywhere.
- **It explains, precisely, why the Boolos fork (#2) is safer (§7):** Boolos
  needs only a first-order provability predicate; Rayo needs a truth predicate
  for V.
- **It corrects one imprecision in `RAYO-EXPLAINER.md` (§6):** the self-reference
  is meta-level, not inside the object formulas; Rayo's growth is set theory's
  ontological reach, not object-level diagonalization.
- **Limits (§8):** resolves well-definedness only (not growth rate); standard
  facts in novel assembly (no new theorem); paper, not Lean.

## Sources

Primary account: Agustín Rayo, "The Big Number Duel," ch. 9.4 of *On the Brink
of Paradox* (MIT Press, 2019), via `rayo-notes/literature-notes.md` (corrected
citation). Construction and realist-interpretation framing cross-checked
against:

- [Rayo's number — Wikipedia](https://en.wikipedia.org/wiki/Rayo%27s_number)
- [Rayo's number — Googology Wiki (Fandom)](https://googology.fandom.com/wiki/Rayo's_number)
- [Rayo's number — Googology Wiki (Miraheze)](https://googology.miraheze.org/wiki/Rayo's_number)
- [Pranav Maddineedi, "One more large number: Rayo's Number" (Medium)](https://medium.com/@pmaddineedi/one-more-large-number-rayos-number-rayo-10-100-or-the-smallest-number-greater-than-maximal-7a96e93f320e)
- [Joel David Hamkins et al., "Class choice and the surprising weakness of Kelley–Morse set theory" (arXiv)](https://arxiv.org/pdf/2601.23165) — the paper checked against in §4's verification note; its "weakness" is class-choice/ETR, not the first-order truth class.
- [Joel David Hamkins, "Kelley-Morse set theory implies Con(ZFC) and much more"](https://jdh.hamkins.org/km-implies-conzfc/) — the KM truth-class ⟹ `Con(ZFC)` fact §4 relies on.
- [Victoria Gitman, "Kelley-Morse set theory and choice principles for classes"](https://victoriagitman.github.io/files/kelleymorse2.pdf) — KM's truth-predicate class `Tr` and the class-choice landscape.

Standard metatheory used in §3–§4 (Tarski's undefinability theorem; MK proves a
first-order truth/satisfaction class for V and hence `Con(ZFC)`; NBG is
conservative over ZFC and so proves neither) is textbook — see any standard
reference on class theories (e.g. Kunen, *Set Theory*; the MK/NBG literature) —
and was **checked against the sources above** (§4 verification note,
2026-08-07), not merely asserted from memory.
