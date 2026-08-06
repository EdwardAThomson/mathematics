#!/usr/bin/env python3
"""phase3_check.py -- recompute small Busy Beaver values and check them against
the Phase 0 audited ground truth.

Purpose (Phase 3 of PLAN.md). The (kappa(R), growth) table in KAPPA-TABLE.md
takes the Busy Beaver leaderboard as ground truth for R = n-state 2-symbol
Turing machines. This script is the executable cross-check for the low end of
that column: it independently recomputes BB(n) = S(n) (the step busy beaver,
"max steps before halting over all halting n-state 2-symbol machines") for the
small n where that is feasible, and compares each result to the values audited
in phase0/a-bbchallenge.md.

Two kinds of recomputation, both real (no value is hard-coded as the "computed"
answer):

  * n = 1, 2  -- FULL BRUTE-FORCE ENUMERATION. Every n-state 2-symbol machine is
    generated and simulated; BB(n) emerges as the max halting step count over
    all halters. The number is discovered by search, not asserted.

  * n = 3, 4, 5 -- CHAMPION-WITNESS RECOMPUTATION. Full enumeration is
    infeasible in Python at these sizes (4-state alone is ~2.5e10 machines), and
    halting is undecidable in general. Instead the documented record machine for
    each n (bbchallenge standard notation) is simulated to its halt, and its
    step count is checked to equal the audited BB(n). This recomputes the fact
    "this specific machine runs exactly BB(n) steps"; combined with the audited
    result that these machines are the maxima, it witnesses the ground-truth
    value. The value 21 / 107 / 47,176,870 comes out of the simulator, not out
    of a literal.

Exit status:
  * 0  -- every recomputed value agrees with the audited ground truth.
  * 1  -- some recomputed value disagrees (a real mismatch, or the injected one).

--wrong-bb4:
  Substitutes a deliberately wrong BB(4) into the ground-truth table. The
  simulator still recomputes the champion's true step count (107), which no
  longer matches the corrupted table entry, so the check MUST reject it and exit
  non-zero. This is the negative control: it proves the comparison can fail, so a
  clean exit 0 means something.

Note on scope. The item names "small Turing machines / short BLC programs". Only
the Turing-machine side has a small-n audited ground-truth table in Phase 0
(phase0/a-bbchallenge.md gives BB(1..5)); the Phase 0 BLC data
(phase0/c-pole-position.md) is Tromp fixed-bit *leaderboard* figures for large
growth classes, not enumerable small-n values, so there is nothing of the same
shape to recompute-and-check for BLC. This script therefore checks the
Turing-machine / Busy Beaver column, which is exactly the KAPPA-TABLE.md row the
audited table anchors.

Ground truth traceable to phase0/a-bbchallenge.md:
  BB(1)=1 (Radó 1962), BB(2)=6 (Radó 1962), BB(3)=21 (Lin & Radó 1963),
  BB(4)=107 (Brady 1983), BB(5)=47,176,870 (bbchallenge, Coq-proven 2024).
"""

import argparse
import itertools
import sys

# --- Phase 0 audited ground truth (phase0/a-bbchallenge.md, table of known values) ---
GROUND_TRUTH = {
    1: 1,
    2: 6,
    3: 21,
    4: 107,
    5: 47_176_870,
}

# --- Documented record ("champion") machines, bbchallenge standard notation. ---
# Notation: states separated by "_"; each state is two 3-char transitions, the
# first for reading symbol 0, the second for reading symbol 1. A transition is
# <write><move><next>, e.g. "1RB" = write 1, move Right, go to state B; a next
# state of Z (or H) is the halt state. Start state is A on an all-0 tape.
# Verified in this file's own runs to halt at exactly the audited step counts.
CHAMPIONS = {
    2: "1RB1LB_1LA1RZ",                                  # S = 6
    3: "1RB1RZ_1LB0RC_1LC1LA",                            # S = 21
    4: "1RB1LB_1LA0LC_1RZ1LD_1RD0RA",                     # S = 107
    5: "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",             # S = 47,176,870 (Marxen & Buntrock)
}

HALT_SYMBOLS = "ZH"


def parse_machine(spec):
    """Parse a bbchallenge-notation string into {(state_index, read_symbol): (write, move, next)}."""
    tm = {}
    for state_index, block in enumerate(spec.split("_")):
        if len(block) != 6:
            raise ValueError(f"state block {block!r} is not 6 chars")
        for read_symbol in (0, 1):
            w, mv, nxt = block[read_symbol * 3 : read_symbol * 3 + 3]
            tm[(state_index, read_symbol)] = (int(w), mv, nxt)
    return tm


def run_machine(tm, step_cap):
    """Simulate a machine from the all-0 tape in start state A (index 0).

    Returns (steps, halted). Each executed transition counts as one step,
    including the transition that enters the halt state (bbchallenge S convention:
    the machine has taken `steps` transitions when it halts). If `step_cap` is
    reached without halting, returns (step_cap, False).
    """
    tape = {}
    pos = 0
    state = 0
    steps = 0
    while steps < step_cap:
        symbol = tape.get(pos, 0)
        write, move, nxt = tm[(state, symbol)]
        tape[pos] = write
        pos += 1 if move == "R" else -1
        steps += 1
        if nxt in HALT_SYMBOLS:
            return steps, True
        state = ord(nxt) - ord("A")
    return steps, False


def _all_machines(n):
    """Yield every n-state 2-symbol machine as a parsed tm dict.

    Each of the 2n transition cells chooses write in {0,1}, move in {L,R}, and a
    next state in {A..(n-1th)} or the halt state Z. Total: (4*(n+1))^(2n) machines.
    """
    next_states = [chr(ord("A") + i) for i in range(n)] + ["Z"]
    cell_choices = [
        (w, mv, nxt)
        for w in (0, 1)
        for mv in ("L", "R")
        for nxt in next_states
    ]
    for combo in itertools.product(cell_choices, repeat=2 * n):
        tm = {}
        for cell_index, (w, mv, nxt) in enumerate(combo):
            state_index, read_symbol = divmod(cell_index, 2)
            tm[(state_index, read_symbol)] = (w, mv, nxt)
        yield tm


def brute_force_bb(n, step_cap):
    """Compute BB(n) = S(n) by full enumeration. Max step count over halters.

    A machine that has not halted within step_cap is treated as non-halting and
    excluded. This is sound only when step_cap comfortably exceeds the true BB(n),
    which it does for n <= 2 (BB(2)=6); it is NOT a general halting decider.
    """
    best = 0
    for tm in _all_machines(n):
        steps, halted = run_machine(tm, step_cap)
        if halted and steps > best:
            best = steps
    return best


def champion_bb(n):
    """Recompute BB(n) by simulating the documented champion machine to its halt."""
    steps, halted = run_machine(parse_machine(CHAMPIONS[n]), step_cap=10 ** 9)
    if not halted:
        raise RuntimeError(f"champion for n={n} did not halt within cap (bad machine string?)")
    return steps


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--wrong-bb4",
        action="store_true",
        help="inject a deliberately wrong BB(4) into the ground truth; the check must then reject (negative control).",
    )
    parser.add_argument(
        "--skip-bb5",
        action="store_true",
        help="skip the BB(5) champion recomputation (its 47.2M-step run takes ~6s).",
    )
    args = parser.parse_args(argv)

    ground_truth = dict(GROUND_TRUTH)
    if args.wrong_bb4:
        bad = ground_truth[4] + 1  # 108, deliberately not the true BB(4)=107
        ground_truth[4] = bad
        print(f"[--wrong-bb4] injected BB(4) = {bad} (true value is {GROUND_TRUTH[4]}); the check must reject this.")

    # (n, method-label, computed-value-fn)
    checks = [
        (1, "brute-force enumeration", lambda: brute_force_bb(1, step_cap=50)),
        (2, "brute-force enumeration", lambda: brute_force_bb(2, step_cap=200)),
        (3, "champion witness", lambda: champion_bb(3)),
        (4, "champion witness", lambda: champion_bb(4)),
    ]
    if not args.skip_bb5:
        checks.append((5, "champion witness", lambda: champion_bb(5)))

    ok = True
    for n, method, compute in checks:
        computed = compute()
        expected = ground_truth[n]
        agree = computed == expected
        ok = ok and agree
        mark = "OK " if agree else "FAIL"
        detail = "" if agree else f"  <-- mismatch (audited BB({n}) = {GROUND_TRUTH[n]})"
        print(f"[{mark}] BB({n}) recomputed = {computed:>12,}  ground truth = {expected:>12,}  via {method}{detail}")

    if ok:
        print("\nAll recomputed Busy Beaver values agree with the Phase 0 audited ground truth.")
        return 0
    print("\nMismatch detected: recomputed value(s) disagree with the ground-truth table.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
