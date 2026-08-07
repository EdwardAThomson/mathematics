# Work breakdown: rigorously grounding Rayo's own construction

Higher-risk of the two forks from `DIAGONALIZATION-PLAN.md`. Read
`DIAGONALIZATION-STAGE0-FINDINGS.md` §3-4 first — the short version: nobody
has ever given Rayo's specific construction a fully rigorous proof, informal
or mechanized. This plan starts with mathematics, not Lean, and there is a
real, honest chance Phase R0 does not close at all. That is a legitimate
outcome of attempting this, not a failure of the plan.

**Read first:** `BN-function.md`, `RAYO-EXPLAINER.md`,
`DIAGONALIZATION-PLAN.md`, `DIAGONALIZATION-STAGE0-FINDINGS.md`,
`rayo-notes/literature-notes.md` (the corrected citation and what Rayo's
actual account, ch. 9.4 of *On the Brink of Paradox*, says). Do not re-derive
what they establish, and do not start from the old, wrong "On Specifying
Truth-Conditions" citation the literature notes already flag as incorrect.

## Phase R0 — State the actual claim, and attempt to prove it on paper

This is the phase that might not succeed, and it should be attempted
*before* any Lean, specifically so a failure here is cheap rather than
discovered after a large formalization investment.

1. **Fix which second-order semantics is meant.** Rayo's own account never
   pins this down (per the Stage 0 audit), and the Googology Wiki objection
   is a real one: standard second-order semantics (quantifying over *all*
   subsets of the domain) is not categorically axiomatizable, so different
   background choices can give different answers. Decide explicitly:
   full/standard semantics (set-theoretically loaded, closer to Rayo's
   apparent intent, reopens exactly the "which model" ambiguity) or Henkin
   semantics (quantifies only over a designated sub-collection of subsets —
   tamer, closer to a many-sorted first-order theory, but a real departure
   from what Rayo's popular description seems to intend, and worth stating
   plainly as a departure if chosen). This choice is not optional
   bookkeeping — it changes what is even being proven.
2. **Precisely state the well-definedness claim.** Two separate things,
   both needed: (a) the construction does not lead to contradiction — no
   route from its existence to `False`; (b) it succeeds at naming a
   specific number consistent with its intended informal meaning, not
   merely "doesn't crash."
3. **Attempt the actual proof.** Rayo's own words (the corrected citation):
   the construction "relied on a second order language... to characterize a
   non-semantic substitute for the notion of being named" — this is a
   description of a strategy, not a theorem. Try to turn it into one: a
   genuine fixed-point/diagonal argument establishing (a) and (b) above for
   whichever semantics was chosen in step 1.
4. **Honest exit conditions, decide these before starting:**
   - If a real proof is found: proceed to Phase R1, and treat this proof
     sketch itself as a genuinely new contribution — nobody has published
     one.
   - If the standard-semantics version turns out not to be provable, or
     only provable with extra set-theoretic assumptions beyond a fixed
     background theory: that is a real, reportable finding (essentially,
     "Rayo's number as popularly described is not a single well-defined
     natural number without additional specification the popular accounts
     omit") — worth writing up on its own even without going further.
   - Set a real time-box for this phase and honor it. Unlike Phase B0 in
     `BOOLOS-FUNCTION-PLAN.md`, there is no known correct proof to reproduce
     here — this is genuinely open-ended mathematical work, and open-ended
     mathematical work does not obey resource caps the way a formalization
     of known math does. A time-box exists so the *attempt* is bounded, not
     because the underlying question is.

## Phase R1 — Formalize the required satisfaction machinery (only if R0 succeeds)

The closest existing precedent, per Stage 0, is Lawrence Paulson's
ZF-Constructible Isabelle library: a real satisfaction predicate
`M, ms ⊨ φ`, defined by recursion on formula syntax, for a *set-sized model*
M — not truth-in-the-full-universe-V, which is the harder thing Rayo's
construction actually needs, but the nearest real starting point found
anywhere. Two live options, both nontrivial:
- Port/adapt Paulson's Isabelle approach to Lean — a genuine cross-proof-
  assistant translation effort, not a mechanical one.
- Build the satisfaction-in-a-model machinery fresh in Lean, checking first
  whether `Foundation`'s `SetTheory/TransitiveModel.lean` (noted but not
  investigated in depth by the Stage 0 audit) already provides useful
  scaffolding — this is the first concrete thing to check before assuming
  a from-scratch build is necessary.

## Phase R2 — Formalize the diagonal/self-reference lemma from R0

Whatever R0 actually established, formalized as a Lean theorem.

## Phase R3 — Apply to one concrete tiny case

Verify the mechanism actually produces a specific named number end to end,
and compare against `rayo-lean/`'s existing K0-K6 table — not to reach a
large number, just to confirm the whole pipeline works on something checkable.

## The honest bottom line to carry into this

This plan is not "harder version of `BOOLOS-FUNCTION-PLAN.md`" — it is
structurally different, because Phase R0 might resolve into "this doesn't
hold up as stated" rather than "this is hard but true." Whoever picks this
up should be prepared for that as a genuine, useful endpoint, not treat it
as the plan having failed.
