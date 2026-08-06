# Phase 0 evidence: bbchallenge.org audit of BB(1)–BB(5)

**Source(s) fetched:** https://bbchallenge.org and https://bbchallenge.org/story
(cross-checked against the official announcement thread
https://discuss.bbchallenge.org/t/july-2nd-2024-we-have-proved-bb-5-47-176-870/237,
Scott Aaronson's blog https://scottaaronson.blog/?p=8088, and Quanta Magazine
https://www.quantamagazine.org/amateur-mathematicians-find-fifth-busy-beaver-turing-machine-20240702/)

**Fetched:** 2026-08-06 (via WebFetch / WebSearch during item i_783211fe13d5).
Note: bbchallenge WebFetch responses are cached ~15 min; the values below are
static mathematical facts, not live figures.

## Reference system R

R = Busy Beaver, i.e. n-state 2-symbol single-tape Turing machines. BB(n) here
is the "step" busy beaver S(n) = max number of steps before halting over all
halting n-state 2-symbol machines. This is the ground-truth leaderboard named in
BN-function.md §9 ("`bbchallenge.org` leaderboards as ground truth").

## Table of known values and status

| n | BB(n) = S(n) | status | proof citation / date |
|---|--------------|--------|-----------------------|
| 1 | 1            | proven exact | Radó, 1962 (original Busy Beaver paper) |
| 2 | 6            | proven exact | Radó, 1962 |
| 3 | 21           | proven exact | Lin & Radó, 1963 |
| 4 | 107          | proven exact | Brady, 1983 |
| 5 | 47,176,870   | **proven exact (2024)** | see below |
| 6 | — | **NOT exact**: only lower-bounded (> 10↑↑15, Kropitz/"Antihydra"-class results); out of scope here | conjecture/lower bound only |

BB(1)–BB(4) had long been settled classically. BB(5) = 47,176,870 was
*conjectured* since Marxen & Buntrock (1990) and reasserted by Aaronson (2020);
it became **proven exact** only in 2024.

## The 2024 five-state proof (named)

- **Name:** "The Busy Beaver Challenge" (bbchallenge) collaborative proof of
  `BB(5) = 47,176,870`.
- **Date proven / announced:** **July 2nd, 2024.** bbchallenge.org states: "We
  have reached our goal of proving 'BB(5) = 47,176,870'" and "The search of
  BB(5) has been completed as of July 2nd 2024. Therefore we now know that no
  machine halts after more than 47,176,870 steps."
- **Formalization:** a **machine-checked Coq proof** ("See the formal Coq
  proof"). The Coq development was authored primarily by contributor **mxdys**,
  building on and using the contributions of more than 10 other bbchallenge
  contributors; it formally verifies the deciders that classify the ~180 million
  relevant 5-state machines.
- **Human-readable paper:** a paper presenting the BB(5) proof was posted to
  arXiv (bbchallenge notes it dated September 15th, 2025).
- **Independent coverage confirming the proof and date:** Quanta Magazine,
  "Amateur Mathematicians Find Fifth 'Busy Beaver' Turing Machine" (2024-07-02);
  Scott Aaronson, "BusyBeaver(5) is now known to be 47176870".

## Bearing on the project

Confirms the BN-function.md §9 claim that Busy Beaver is "known exactly only up
to BB(5) as of the 5-state proof in 2024; BB(6) is only lower-bounded." So for
the reference system R = small Turing machines, the exact-value column of the
(kappa(R), growth) table can use n = 1..5 as *proven* ground truth, and BB(6)+
only as lower bounds.
