# Phase 0 evidence: Code Golf "Pole Position" (fewest bytes, biggest number)

**What "Pole Position" means here.** There is no Code Golf challenge literally
titled "Pole Position"; that is this project's own shorthand (from the goal note
in `BN-function.md`) for the bignum-bakeoff class of challenge: *fix a small code
budget, maximize the number produced*. Two real, ongoing artefacts populate it,
and both are recorded below:

1. **Code Golf & Coding Challenges (Stack Exchange), "Golf a number bigger than
   TREE(3)"** — the community bakeoff most people mean. `code-golf` scoring, so
   the *winner is the shortest program* that deterministically outputs a number
   `>= TREE(3)`; each answer's "score" column is the growth-rate class it reaches.
2. **John Tromp's Binary Lambda Calculus fixed-bit leaderboard** — the purest
   "fixed budget -> biggest number" ranking: how large a number you can name in a
   fixed *bit* budget (e.g. 64 bits) of BLC. This is the BLC-native table the goal
   points at.

**Source(s) fetched:**
- `https://a.osmarks.net/content/codegolf.stackexchange.com_en_all_2020-04/A/element/146279.html`
  (osmarks.net archived mirror of the Code Golf SE question #146279, snapshot
  dated **2020-04**). The live `codegolf.stackexchange.com` was **NOT fetchable**
  from this environment ("Claude Code is unable to fetch from
  codegolf.stackexchange.com"), so the byte counts / authors below are from the
  2020-04 archive, not the live 2026 leaderboard.
- `https://tromp.github.io/blog/2026/01/28/largest-number-revised` (John Tromp,
  "The largest number representable in 64 bits", revised **2026-01-28**).

**Fetched:** 2026-08-06 (via WebFetch / WebSearch during item i_b89a9a28460f).

**Status: PARTIAL / archived.** The TREE(3) table reflects the **2020-04 mirror
snapshot**, which is stale relative to any edits made 2020-2026; the live SE page
could not be reached to confirm current standings. The Tromp BLC figures are from
a **2026-01-28** post and are current. Byte/bit counts are transcribed from a
fast-model read of the fetched pages and should be spot-checked against the live
sources before being used as exact leaderboard values.

## 1. Code Golf SE #146279 "Golf a number bigger than TREE(3)"

**Scoring rule (verbatim from the mirror):** "This is a code-golf so the goal is
to write the shortest program in any language that deterministically outputs a
number even bigger than it!" Constraints: no input, must terminate, infinite
memory assumed, numeric types may hold any finite value, no infinities as output.
So: **byte count is the score to minimize; every listed answer already exceeds
TREE(3)**, and the "reaches" column just says how far past it each one goes.

| rank (by bytes) | author | language | bytes | reaches (growth-rate class) |
|---|---|---|---|---|
| 1 (winner) | Simply Beautiful Art | Ruby | 135 | H_ψ(φ3(Ω+1))(9) (extended Madore OCF / Veblen) |
| 2 | Deedlit | Ruby | 140 | ~H_ψ(Ω^Ω^Ω)(81) (Buchholz hydra, below Bachmann-Howard) |
| 3 | Naruyoko | JavaScript | 190 | H_ψ(ε_{Ω+1})(9) (Hardy hierarchy on pair sequences) |
| 4 | Deedlit | Python 2 | 194 | ~H_ψ(Ω^Ω^Ω)(9) (Buchholz hydra) |
| 5 | PyRulez | Haskell | 252 | TREE(3)+1 (direct: tree homeomorphic-embedding search) |
| 6 | eaglgenes101 | Julia | 569 | Loader's number (port of `loader.c`) |

**Encoding note (BLC-or-other):** none of these six use BLC; they are ordinary
ASCII source in Ruby/Haskell/Python/Julia/JavaScript. The BLC entries live in the
sibling challenge "Shortest terminating program whose output size exceeds
Graham's number" (user Patcail, optimized by 2014MELO03 -> "Melo's number", a
**49-bit** BLC term), which feeds Tromp's fixed-bit leaderboard in §2.

**Reading for the (kappa, growth) table:** within this one fixed R (each answer's
own ad-hoc language + library), fewer bytes does *not* mean a weaker number: the
135-byte Ruby winner reaches a far higher fast-growing-hierarchy ordinal than the
569-byte Julia Loader's-number port. The byte count is dominated by how cleverly
the author encodes an ordinal-notation / hydra evaluator, i.e. by per-symbol
overhead, exactly the invariance-constant effect predicted in `BN-function.md` §6.

## 2. Tromp's Binary Lambda Calculus fixed-bit leaderboard (current, 2026-01)

Here R = Binary Lambda Calculus (Tromp), budget = **bits**, and the ranking is
"largest number namable in a fixed bit budget" — the true fewest-bytes/biggest-
number pole position.

| entry | BLC bits | authors | reaches (growth-rate class) |
|---|---|---|---|
| Melo's number | 49 | Patcail, 2014MELO03 | > Graham's number; ~f_{ω+1}(2↑↑6) in FGH |
| w218 | 61 | Discord users 50_ft_lock, Sam | ~f in the ω·2 range (paper: "[ω2↑↑18-1] 2"); 3 bits spare in 64 |

**Bit-by-bit milestones (BLC bits needed to reach each landmark):**

| landmark | BLC bits | growth class |
|---|---|---|
| Graham's number | 49 | ω+1 |
| Buchholz's ordinal (> TREE(3)) | 100 | ψ(Ω_ω)-region |
| Goodstein's function | 111 | ε_0 |
| Bashicu Matrix System | 331 | PTO(Z_2) |
| Loader's number | 1850 | PTO(Z_ω) |

Tromp also gives the functional-Busy-Beaver corollary that w218 (61 bits) lower-
bounds BBλ: `BBλ(61) >= 5(2^2^2^2^2^2^2^([ω2↑↑18-1] 2))+6`.

**Reading for the (kappa, growth) table:** this is the cleanest "cost buys growth"
series in the project so far. Holding R = BLC fixed, the *budget n* (bits) and the
reachable growth-rate ordinal climb together in a legible way: 49 bits -> ω+1
(Graham), 100 -> Buchholz (past TREE(3)), 111 -> ε_0, 331 -> PTO(Z_2), 1850 ->
PTO(Z_ω, Loader). That is a within-R growth-vs-budget curve; it is *not* a
kappa(R) curve (R, hence kappa, is fixed at BLC throughout). It complements the
across-R spine of the project's central table, which varies R and prices kappa(R).

## Bearing on the project

Both artefacts confirm the goal's premise that existing bakeoffs "track one fixed
R across n" and never price kappa(R): the TREE(3) challenge fixes "shortest ASCII
program" and ranks by bytes; Tromp fixes R = BLC and ranks by bits. Neither varies
R or charges for specifying R. They give this project two concrete, real
data-bearing columns (a bytes->growth curve in mixed ASCII languages, and a
clean bits->growth curve in BLC) to sit beside the Busy-Beaver columns in
`phase0/a-bbchallenge.md` and `phase0/b-bb6.md` when the (kappa(R), growth) table
is assembled.
