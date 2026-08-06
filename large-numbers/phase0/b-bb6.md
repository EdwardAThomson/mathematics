# Phase 0 evidence: current best certified BB(6) lower bound

**Source(s) fetched:** https://wiki.bbchallenge.org/wiki/BB(6) (BusyBeaverWiki,
the community-maintained record page), cross-checked against Scott Aaronson,
"BusyBeaver(6) is really quite large" https://scottaaronson.blog/?p=8972
(2025-06-28), and Quanta Magazine, "Busy Beaver Hunters Reach Numbers That
Overwhelm Ordinary Math" https://www.quantamagazine.org/busy-beaver-hunters-reach-numbers-that-overwhelm-ordinary-math-20250822/

**Fetched:** 2026-08-06 (via WebFetch / WebSearch during item i_505e4a6948f9).
Note: the bbchallenge machine page renders client-side and returned no body to
WebFetch; the machine string and halt status below are taken from the
BusyBeaverWiki BB(6) page (last updated 2026-07-28) and the Aaronson post. The
numeric bound is a static mathematical fact, not a live figure.

## Reference system R

R = Busy Beaver, i.e. n-state 2-symbol single-tape Turing machines, same R as in
`phase0/a-bbchallenge.md`. BB(6) = S(6) = max number of steps before halting over
all halting 6-state 2-symbol machines. BB(6) is **not known exactly** (and, given
the "Antihydra" Collatz-like cryptid found June 2024, may be very hard to settle);
only lower bounds exist. This item records the current best *lower* bound.

## Current best certified BB(6) lower bound

| field | value |
|-------|-------|
| bound | **BB(6) = S(6) > Σ(6) > 2 ↑↑↑ 5** (2 pentated to 5; iterated tetration) |
| witness machine (bbchallenge std notation) | `1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE` |
| machine page | https://bbchallenge.org/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE |
| discoverer | **mxdys** (bbchallenge contributor) |
| date | **June 2025** |
| status | **halting** machine; lower bound is **community-confirmed and machine-checked via a Coq correctness proof** (see below). Not journal peer-reviewed. |

`2 ↑↑↑ 5` in tetration terms is a tower of "2 tetrated to 2 tetrated to ..."
five levels deep; it dwarfs the 2022 record `10 ↑↑ 15`, which was a single
tetration (a power tower of 10s of height ~15.6).

## Verification / peer-review status (the point of this item)

- **Machine-checked, not peer-reviewed.** The June 2025 mxdys results were
  accompanied by a **correctness proof in Coq** (a formal proof assistant), with
  source on GitHub. Aaronson's post (2025-06-28) reports the bound as coming
  "with a correctness proof in Coq." So the bound is *formally verified* (strong)
  but has **not** been through traditional journal peer review.
- **Community-confirmed.** The witness machine is catalogued on bbchallenge.org
  and on the community BusyBeaverWiki BB(6) page as the current champion, with a
  recorded **halt** status.
- Contrast with BB(5): BB(5) = 47,176,870 is *exact and Coq-proven* (item
  `a-bbchallenge`). BB(6) is *lower-bounded only*; the Coq proof here certifies
  that the witness machine halts after > 2↑↑↑5 steps, not that no 6-state machine
  runs longer.

## Record history (recent), for the (kappa, growth) table

| date | discoverer | bound | witness machine |
|------|-----------|-------|-----------------|
| 2022-06 | Pavel Kropitz (via sligocki analysis) | BB(6) > 10 ↑↑ 15 (~10↑↑15.6) | `1RB0LD_1RC0RF_1LC1LA_0LE1RZ_1LF0RB_0RC0RE` |
| 2025-06 (intermediate) | mxdys | BB(6) > 2 ↑↑ 2 ↑↑ 2 ↑↑ 9 | (superseded within days) |
| 2025-06 (current) | mxdys | **BB(6) > 2 ↑↑↑ 5** | `1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE` |

The June 2025 record was broken several times within about two weeks; the
`2↑↑↑5` figure is the current standing champion per the BusyBeaverWiki page.

## Bearing on the project

For the (kappa(R), growth-rate) table, R = 6-state Turing machines. The single
data point BB(6) here jumps from tetration (`10↑↑15`, 2022) to pentation
(`2↑↑↑5`, 2025) with **no change in kappa(R)** (still 6 states, 2 symbols): a
large realized growth increase came purely from a better witness machine, not
from paying more specification cost. That is direct evidence that, *within a
fixed R*, the achieved growth is a search/effort artefact, whereas the
BB(5)->BB(6) step (tens of millions -> pentation) shows the steep growth that
comes from spending one extra unit of kappa (one more state). Both readings feed
the "cheap vs expensive" question the goal poses.
