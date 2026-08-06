# Phase 0, decomposed into inquiry items

Draft. Each item below is sized so a plimsoll `inquiry` item's `verify` can be
a real, non-vacuous check: "the source was fetched (a command ran, exited 0,
its output is recorded) and `FINDINGS.md` carries a well-formed entry for this
item's id" — never "the claim is true." Sufficiency of the audit as a whole
(is Phase 0 done, does anything need reopening) is a human call made by
pausing the run and reading `FINDINGS.md`, not something an item verifies.

## Evidence contract (shared by every item below)

Each item's `FINDINGS.md` entry must carry, at minimum:

- `source`: the exact URL(s) or document fetched
- `fetched`: the date it was fetched (these are live/community pages —
  Phase 0 in `PLAN.md` already flags this thread as "believed... as of
  writing," and community pages can simply have changed)
- `claim`: a direct quote or tightly-anchored paraphrase of what the source
  says, not a restatement from memory of the video transcript
- `status`: one of `proven` / `certified-lower-bound` / `conjectural` /
  `community-consensus` / `unverified-claim` / `not-found`
- if the source could not be reached or the claim could not be located:
  record that explicitly as `not-found` with what was tried — never omit the
  entry (a missing row reads as "not investigated," which is worse than
  "investigated, found nothing usable")

`verify` for each item: the fetch command's own receipt (exit 0, output
hash) plus a structural check that `FINDINGS.md` has an entry for that id
with all five fields non-empty.

## Items

**0a — BB(1)-BB(5), proof status.** For each of $BB(1)$ through $BB(5)$ on
bbchallenge.org: confirm "proven exact," and record the specific proof
citation and date (the 2024 5-state proof by name/reference, not just "2024
proof").

**0b — BB(6), current best certified lower bound.** Record the witness
machine (its transition table or a link to it), who found it, and whether the
bound is community-verified, peer-reviewed, or still informal. This is
separate from 0a because it is a different kind of claim (a lower bound, not
an exact value) that can go stale independently.

**0c — Bignum-bakeoff leaderboard, current state.** Pull the Code Golf
StackExchange "Pole Position: fewest bytes, biggest number" thread's current
top entries: byte count, author, language/encoding (BLC vs. other), claimed
growth-rate class for each.

**0d — Cross-check the three transcript-derived figures.** `BN-function.md`
currently states, from paraphrasing the video transcripts rather than the
thread itself: 49 bytes reaching Buchholz's ordinal, 52 bytes reaching BMS,
233 bytes beating Loader's number. Confirm or correct each of the three
against the actual thread (author, exact byte count, exact claim). If any
figure is wrong, that is a finding requiring a follow-up correction to
`BN-function.md` §7/§9, not a silent fix.

**0e — Googology Wiki: FOOT / BIG FOOT.** Locate the comparison/ranking page,
record the growth-rate ordering it asserts and on what basis (a cited proof,
a cited external claim, or unsourced wiki consensus) — per the repo's
standing rule that Googology Wiki claims
need their cited basis checked, not just quoted.

**0f — Googology Wiki: Rayo's function variants.** Same treatment, for
whatever ranking page(s) cover Rayo's function and its named variants.

**0g — Googology Wiki: oodle / array notation hierarchy.** Same treatment.

## Notes on sizing

0a/0b split rather than merge Busy Beaver into one item because "exact value,
proven" and "lower bound, unproven" are independently-failable claims (the
sizing rule in `SPEC.md`: two verifications that can fail independently are
two items). 0c and 0d are split because 0c is open-ended discovery (whatever
the current leaderboard shows) and 0d is a targeted correctness check against
three specific numbers already committed to `BN-function.md` — different
failure modes, so different items. The three Googology Wiki pages are split
per page since each is an independent fetch with its own claim to check, not
because the underlying question differs.

This list is what Phase 0 of `PLAN.md` becomes when written as plimsoll
inquiry items; the full plimsoll prompt (goal, mode, phases 1-4, explicitly
out of scope) is the next piece to draft.
