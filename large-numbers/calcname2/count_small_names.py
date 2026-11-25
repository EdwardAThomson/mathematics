#!/usr/bin/env python3
"""
Count the numbers that have short names in the binary toy arithmetic B.

B (NAMING-RECORDS-SMALL-SYSTEM.md section 1): symbols 0 (arity 0), D0, D1, S
(arity 1), +, *, ^ (arity 2).  D0 x = 2x, D1 x = 2x+1.  Size = number of
symbols.  K(k) = least size of a closed term with value k.

Budget proxy: we only keep terms all of whose subterm values are < 2^W.  In
CalcName the evaluation proof is at most m <= N symbols, and every value met
in it is written as a numeral inside the proof, so every subterm value is
below 2^m.  Capping at 2^W is the same kind of restriction with m ~ W.  (It is
a proxy: the true evaluation-proof length also grows with the number of
rewrite steps, so the real constraint is somewhat tighter.)

Values-only dynamic programming: first[s] = values whose least size is s.
A value of size s is built from children of sizes summing to s-1, and only
the least size of each child matters, so combining the "first" sets is exact.

Usage: python3 count_small_names.py W SMAX [OPS] [DUMP]
OPS (default "+*^") lists the binary symbols allowed, to test which ones least
names really need.  DUMP, if given, is a file to write "value size" lines to.
Prints, for each size s, how many values first appear, and for bit lengths
n, how many n-bit numbers have K <= s, next to 2^(n-1) and 7^s-type bounds.
"""
import sys
from collections import defaultdict

W = int(sys.argv[1]) if len(sys.argv) > 1 else 24
SMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 14
CAP = 1 << W

OPS = sys.argv[3] if len(sys.argv) > 3 else "+*^"
# SMALLARG = t: allow + and * only when one argument has least size <= t
# (a "peeling" fragment: strip a small summand or a small factor).
import os
SMALLARG = int(os.environ.get("SMALLARG", "999"))
best = {}                 # value -> least size
first = defaultdict(set)  # size -> values of least size exactly s
top = {}                  # value -> top symbol of one least-size name

def add(v, s, sym):
    if v < CAP and v not in best:
        best[v] = s
        first[s].add(v)
        top[v] = sym

add(0, 1, "0")
for s in range(2, SMAX + 1):
    # unary
    for v in list(first[s - 1]):
        add(2 * v, s, "D0")          # D0 0 = 0 already present
        add(2 * v + 1, s, "D1")
        add(v + 1, s, "S")
    # binary: sizes a + b = s - 1
    for a in range(1, s - 1):
        b = s - 1 - a
        A, Bv = first[a], first[b]
        if not A or not Bv:
            continue
        small = min(a, b) <= SMALLARG
        for x in A:
            for y in Bv:
                if "+" in OPS and small:
                    add(x + y, s, "+")
                p = x * y
                if p < CAP and "*" in OPS and small:
                    add(p, s, "*")
                if "^" not in OPS:
                    continue
                if x <= 1:
                    add(x if y > 0 else 1, s, "^")
                elif y < W + 1:
                    q = x ** y
                    if q < CAP:
                        add(q, s, "^")
    print(f"s={s:2d}  new={len(first[s]):9d}  total={len(best):10d}", flush=True)

if len(sys.argv) > 4:
    with open(sys.argv[4], "w") as f:
        for v in sorted(best):
            f.write(f"{v} {best[v]} {top[v]}\n")

# counts by bit length
print()
print("n-bit numbers k (2^(n-1) <= k < 2^n) with K(k) <= s")
sizes = list(range(2, SMAX + 1))
hdr = "n  " + " ".join(f"{s:>8d}" for s in sizes) + "   2^(n-1)"
print(hdr)
cnt = defaultdict(lambda: defaultdict(int))
for v, s in best.items():
    n = v.bit_length()
    cnt[n][s] += 1
for n in range(1, W + 1):
    row, run = [], 0
    for s in sizes:
        run += cnt[n][s]
        row.append(run)
    print(f"{n:2d} " + " ".join(f"{r:8d}" for r in row) + f"   {1 << (n-1) if n else 1}")

# which numbers are compressible: K(k) < numeral size - 2, by top symbol
print()
print("top symbol of a least name, among numbers with K(k) <= numeral size - 3")
tc = defaultdict(int)
for v, s in best.items():
    if v > 0 and s <= v.bit_length() + 1 - 3:
        tc[top[v]] += 1
print(dict(tc))
