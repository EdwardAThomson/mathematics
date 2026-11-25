#!/usr/bin/env python3
"""Tables for CALCNAME2-NOTE.md section 3 from count_small_names.py dumps.
Usage: python3 analyse_small_names.py FULL_DUMP SMAX [OPS_DUMP ...]"""
import sys, math
from collections import defaultdict
full = {}
for line in open(sys.argv[1]):
    v, s, t = line.split(); full[int(v)] = (int(s), t)
SMAX = int(sys.argv[2])
cnt = defaultdict(lambda: defaultdict(int))
for v, (s, t) in full.items():
    cnt[v.bit_length()][s] += 1
print("| n | s = ⌊(log₂ n)²⌋ | n-bit numbers with K ≤ s | log₂ of that | fraction of n-bit numbers |")
print("|---|---|---|---|---|")
for n in [4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 32, 40, 48, 64]:
    s = int(math.log2(n) ** 2)
    if s > SMAX:
        continue
    c = sum(cnt[n][t] for t in range(1, s + 1))
    frac = c / 2 ** (n - 1)
    print(f"| {n} | {s} | {c:,} | {math.log2(c) if c else float('-inf'):.1f} | {frac:.2e} |")
print()
# fixed size, growing n
print("| s | values < 2^64 with K = s | ratio to previous |")
print("|---|---|---|")
per = defaultdict(int)
for v, (s, t) in full.items(): per[s] += 1
prev = None
for s in sorted(per):
    r = f"{per[s]/prev:.2f}" if prev else ""
    print(f"| {s} | {per[s]:,} | {r} |"); prev = per[s]
print()
for path in sys.argv[3:]:
    sub = {}
    for line in open(path):
        v, s, t = line.split(); sub[int(v)] = int(s)
    worse = sum(1 for v, (s, t) in full.items() if s <= SMAX and sub.get(v, 99) > s)
    tot = sum(1 for v, (s, t) in full.items() if s <= SMAX)
    print(f"{path}: {worse:,} of {tot:,} values have a larger least size without the missing symbols")
