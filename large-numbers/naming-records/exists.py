#!/usr/bin/env python3
"""
Naming by a property ("there exists"), binary system B.

A *property name* is an equation  p(x) = c  where c is a closed term and p is
a term with exactly one occurrence of the variable x, built so that p is
strictly increasing in x (every operation on the path from the root to x is
S, D0, D1, +, multiplication by a term of value >= 1, x^e with e >= 1, or
b^x with b >= 2).  It names the unique k with p(k) = c, when there is one.

Size: |p| + |c| + 1 (x counts 1, '=' counts 1).

Proof that it names k:
  * the lemma proof (lemmas.py, with reuse) of  p(k) = m  and of  c = m,
    where m is the common value, sharing lemmas between the two;
  * the conclusion  p(k) = c  (one line, |p(k)| + |c|);
  * uniqueness ("p is strictly increasing, so no other x works") is one
    fixed lemma per shape of p.  It is NOT charged here; a real proof
    would add a constant-size block per name.  So D_exists below is a lower
    bound for what a quantified system would pay.

The witness k is guessed, not computed: the proof only checks p(k) = c.
That is the toy's version of "guess and verify".  The question is which
numbers get cheaper names this way than as terms (D from lemma_run / big_run).

Usage: python3 exists.py 10 10000000   (max name size, proof cap)
Writes out_BE<n>.json and prints a summary table.
"""
import json
import math
import sys

from naming_records import Binary, show, pretty
from lemmas import Lemmas, Overflow

nmax, cap = int(sys.argv[1]), int(sys.argv[2])
S = Binary(cap)
L = Lemmas(S)
closed = S.enumerate(nmax)          # closed terms by size
X = ("X",)

# patterns: nested tuples; ("X",) | (sym, child) | (sym, left, right) with
# exactly one X; closed children are term ids (ints).
pats = {1: [X]}
for n in range(2, nmax):
    cur = []
    for u in ("D0", "D1", "S"):
        for p in pats[n - 1]:
            cur.append((u, p))
    for b in ("+", "*", "^"):
        for i in range(1, n - 1):
            j = n - 1 - i
            for p in pats.get(i, []):            # pattern on the left
                for t in closed.get(j, []):
                    v = S.val[t]
                    if v is None:
                        continue
                    if b == "*" and v < 1:
                        continue
                    if b == "^" and v < 1:
                        continue
                    cur.append((b, p, t))
            for t in closed.get(i, []):          # pattern on the right
                v = S.val[t]
                if v is None:
                    continue
                if b == "*" and v < 1:
                    continue
                if b == "^" and v < 2:
                    continue
                for p in pats.get(j, []):
                    cur.append((b, t, p))
    pats[n] = cur
    print(f"patterns of size {n}: {len(cur):,}", file=sys.stderr, flush=True)

psize = {}


def size_of(p):
    if p == X:
        return 1
    if isinstance(p, int):
        return S.size[p]
    return 1 + sum(size_of(c) for c in p[1:])


def ev(p, x, lim):
    """p(x), saturated at lim+1."""
    if p == X:
        return x
    if isinstance(p, int):
        return S.val[p]
    sym = p[0]
    if len(p) == 2:
        a = ev(p[1], x, lim)
        r = {"S": a + 1, "D0": 2 * a, "D1": 2 * a + 1}[sym]
        return min(r, lim + 1)
    a, b = ev(p[1], x, lim), ev(p[2], x, lim)
    if sym == "+":
        r = a + b
    elif sym == "*":
        r = a * b
    else:
        if a <= 1:
            r = a if b > 0 else 1
        elif b * math.log2(a) > math.log2(lim + 2) + 1:
            r = lim + 1
        else:
            r = a ** b
    return min(r, lim + 1)


def inst(p, k_term):
    if p == X:
        return k_term
    if isinstance(p, int):
        return p
    return S.mk(p[0], *(inst(c, k_term) for c in p[1:]))


def show_p(p):
    if p == X:
        return "x"
    if isinstance(p, int):
        return pretty(S, p)
    if len(p) == 2:
        return f"{p[0]}({show_p(p[1])})"
    return f"({show_p(p[1])}{p[0]}{show_p(p[2])})"


def numeral(k):
    if k == 0:
        return S.zero
    return S.mk("D1" if k & 1 else "D0", numeral(k >> 1))


best = {}        # k -> (D, size, cost, name)
count = 0
for n in range(3, nmax + 1):
    for ps in range(1, n - 1):
        cs = n - 1 - ps
        for p in pats.get(ps, []):
            for c in closed.get(cs, []):
                target = S.val[c]
                if target is None:
                    continue
                # strictly increasing and p(x) >= x, so k is in [0, target]
                lo, hi = 0, target
                while lo < hi:
                    mid = (lo + hi) // 2
                    if ev(p, mid, target) < target:
                        lo = mid + 1
                    else:
                        hi = mid
                if ev(p, lo, target) != target:
                    continue
                k = lo
                count += 1
                sk = inst(p, numeral(k))
                # lemma proofs of p(k) = m and c = m, shared
                tot = 0
                ok = True
                seen = set()
                for u in (sk, c):
                    if S.is_normal(u) or u in seen:
                        continue
                    r = L.dag_cost(u, cap)
                    if r is None:
                        ok = False
                        break
                    # add the closure of u not already counted
                    stack = [u]
                    seen.add(u)
                    while stack:
                        v = stack.pop()
                        own, kids, _ = L.lem(v)
                        tot += own
                        for w in kids:
                            if w not in seen:
                                seen.add(w)
                                stack.append(w)
                if not ok:
                    continue
                tot += S.size[sk] + S.size[c]       # conclusion p(k) = c
                if tot > cap:
                    continue
                D = n + math.log2(tot)
                ob = best.get(k)
                if ob is None or D < ob[0] - 1e-12:
                    best[k] = (D, n, tot, f"{show_p(p)} = {pretty(S, c)}")
    print(f"size {n}: {count:,} property names with a solution so far", file=sys.stderr, flush=True)

with open(f"out_BE{nmax}.json", "w") as f:
    json.dump({"nmax": nmax, "cap": cap, "best": {str(k): v for k, v in best.items()}}, f)
print(f"{len(best):,} numbers have a property name of size <= {nmax}")
