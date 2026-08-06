# Phase 0 crosscheck: byte figures (transcript) vs the Pole Position thread

**Purpose.** BN-function.md and the DEVLOG lean on three "text-message byte
budget -> named number" figures that originate in the two CodeParade
transcripts, not in the bakeoff itself:

- **49 bytes -> Buchholz ordinal function**
- **52 bytes -> Bashicu Matrix System (BMS)**
- **233 bytes -> Loader's number**

This note pins each figure to its exact transcript line, then cross-checks it
against the "Pole Position" data already recorded in
`phase0/c-pole-position.md` (John Tromp's current BLC fixed-bit leaderboard,
revised 2026-01-28, plus the Code Golf SE #146279 "bigger than TREE(3)"
thread). It records a confirm/correct verdict per figure.

**Sources fetched / used for the cross-check** (no new network fetch was needed;
the Pole Position leaderboard was already fetched and transcribed in
`phase0/c-pole-position.md`):

- Transcript A: `Quest To Find The Largest Number.srt` (video 1). Fetched: it
  is a tracked file in this repo (local, no network).
- Transcript B: `Finding Even Larger Numbers.srt` (video 2). Local tracked file.
- Pole Position thread data: `phase0/c-pole-position.md`, which itself was
  **fetched** 2026-08-06 from `https://tromp.github.io/blog/2026/01/28/largest-number-revised`
  (current) and the osmarks.net 2020-04 mirror of Code Golf SE #146279 (archived).

**Status: COMPLETE.** All three transcript figures were located verbatim and
each was cross-checked against the Tromp BLC milestone table. Verdicts below.
The Pole Position source **status** is mixed and is carried over from
`phase0/c-pole-position.md`: the Tromp BLC figures are current (2026-01),
the Code Golf SE TREE(3) table is a stale 2020-04 archive.

---

## Figure 1 - "49 bytes -> Buchholz ordinal"

**Verdict: CONFIRMED (transcript-faithful) + one caveat flagged.**

**Transcript source (verbatim), video 1:**
> "surprisingly the Buckle's ordinal function only takes 49 bytes at most so
> there's still a ton of room to do way more to it"

So the transcript does assert **49 bytes** (stated as an upper bound, "at
most") for a term whose growth rate is the Buchholz ordinal function
psi(Omega_omega). The figure is restated correctly.

**Cross-check vs Pole Position (Tromp BLC milestone table,
`phase0/c-pole-position.md` §2):** Tromp reaches *"Buchholz's ordinal
(> TREE(3))"* in **100 bits = 12.5 bytes**. So 49 bytes is **~3.9x larger**
than the current leaderboard optimum for the same growth class. This is not a
contradiction: the 49-byte figure is CodeParade's own hand-built
text-message term ("at most"), predating / not equal to Tromp's optimized
record. The transcript figure is faithfully restated; it simply is **not** the
Pole Position record and should not be cited as one.

**Caveat flagged (unit-conflation trap).** Video 1 *also* states a **49-*bit***
figure for a different construction (Graham's number), and explicitly warns
"49 bits long, yes bits not bites." BN-function.md line ~148 says "real gains
appear already at 15-49 **bytes** of BLC." Read literally that range is
defensible in bytes (15-byte BLC Graham up to the 49-byte Buchholz term), but
the numeral 49 collides with the 49-*bit* Graham figure. See the flag at the
bottom of this file.

---

## Figure 2 - "52 bytes -> BMS"

**Verdict: CONFIRMED (transcript-faithful), consistent with Pole Position.**

**Transcript source (verbatim), video 2:**
> "it was eventually finished by none other than the same Pat kale who managed
> to fit it in under 52 bytes of BLC which is even smaller than the buck holes
> ordinal function we came up with before"

So: **under 52 bytes**, BMS via BLC, attributed to Pat Kale, and explicitly
noted to be smaller than the 49-byte... wait: the transcript says 52 bytes is
"even smaller than the buck holes ordinal function" - which is internally
inconsistent with 52 > 49 unless CodeParade is comparing to a *larger* earlier
Buchholz term than the 49-byte one; treat the "smaller than" clause as the
video's own loose phrasing, not a figure. The figure to check is **52 bytes**.

**Cross-check vs Pole Position (Tromp milestone table):** Tromp prices the
**Bashicu Matrix System** at **331 bits = 41.4 bytes**. The video's "under 52
bytes" is consistent with (an upper bound above) 41 bytes; ratio ~1.26x. The
Pat-Kale-port attribution matches `phase0/c-pole-position.md`, which credits
Kale with the BMS-to-BLC port. Confirmed and consistent.

---

## Figure 3 - "233 bytes -> Loader"

**Verdict: CONFIRMED (transcript-faithful) and a tight numerical match.**

**Transcript source (verbatim), video 2:**
> "how much space does loaders number take in BLC well John Trump ... was able
> to optimize it and create a number that exceeds loaders number in 233 bytes
> which unfortunately doesn't fit into a text message but it does fit nicely
> into a tweet"

So: **233 bytes**, a number exceeding Loader's number, attributed to John
Tromp. Restated correctly.

**Cross-check vs Pole Position (Tromp milestone table):** Tromp prices
**Loader's number** at **1850 bits = 231.25 bytes**, which rounds to ~232-233
bytes. The video's 233 bytes matches Tromp's current leaderboard figure to
within rounding (ratio 1.01x). The Tromp attribution matches. This is the one
figure of the three that coincides with the actual Pole Position record, not
just a conservative CodeParade construction.

---

## Summary table

| figure (transcript) | transcript verbatim? | Pole Position (Tromp) equivalent | verdict |
|---|---|---|---|
| 49 bytes -> Buchholz | yes, "49 bytes at most" (v1) | 100 bits = 12.5 B for same class | CONFIRM (transcript-faithful; ~3.9x the leaderboard optimum, not the record) |
| 52 bytes -> BMS | yes, "under 52 bytes" (v2) | 331 bits = 41.4 B | CONFIRM (consistent, conservative) |
| 233 bytes -> Loader | yes, "233 bytes" (v2) | 1850 bits = 231.25 B | CONFIRM (tight match to the record) |

**Bottom line:** none of the three figures is *wrong* as a restatement of the
transcripts, so no BN-function.md figure requires correction. Two of them
(49B Buchholz, 52B BMS) are CodeParade's own text-message constructions that
are looser than the current Pole Position record for the same growth class;
only the 233B Loader figure is also the leaderboard record.

---

## Flag (no silent edit applied)

BN-function.md line ~148 reads: *"real gains appear already at 15-49 bytes of
BLC."* The numeral **49** there is the 49-*byte* Buchholz figure (Figure 1),
but video 1 uses **49 bits** for Graham's number and explicitly warns "bits
not bites." Recommended clarification (flagged, **not** applied, because the
figure is not wrong and this is an OPEN run):

> change "15-49 bytes of BLC" to "~6-49 bytes of BLC (Graham's number in ~49
> *bits* = ~6 bytes, up to the ~49-*byte* Buchholz term)" — or drop the upper
> bound to avoid the bit/byte numeral collision.

Left for a human / a later item to accept or reject.
