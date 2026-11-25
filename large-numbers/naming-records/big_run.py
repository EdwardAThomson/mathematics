#!/usr/bin/env python3
"""Larger sizes: chain proofs and lemma proofs (with reuse) together, keeping
only the rows the tables need, so that millions of names fit in memory.

Usage: python3 big_run.py U 14 10000000   -> out_U14.json (chain), out_U14L.json (lemmas)
       python3 big_run.py B 11 10000000   -> out_B11.json, out_B11L.json

Kept rows: for each name size, the names on the cost/value Pareto frontier
(cheapest proof for each new record value), and for each value, the name
with the least  size + log2(proof length).  That is everything analyse.py
uses except section 6.  K (least name size per value, proof free) is stored
separately.
"""
import json
import math
import sys
import time

from naming_records import Unary, Binary, show, pretty
from lemmas import Lemmas

which, nmax, cap = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
S = Unary(cap) if which == "U" else Binary(cap)
L = Lemmas(S)
t0 = time.time()
by = S.enumerate(nmax)
print(f"enumerated {sum(len(v) for v in by.values()):,} names in {time.time()-t0:.0f}s",
      file=sys.stderr, flush=True)

K = {}
measures = ("chain", "lemma")
per_size = {m: {} for m in measures}      # m -> n -> {value: (cost, steps, id)}
bestD = {m: {} for m in measures}         # m -> value -> (D, size, cost, steps, id)
n_names = {m: 0 for m in measures}
for n in range(1, nmax + 1):
    for m in measures:
        per_size[m][n] = {}
    for t in by[n]:
        v = S.val[t]
        if v is None:
            continue
        if v not in K:
            K[v] = (n, t)
        if S.is_normal(t):
            res = {"chain": (n, 0), "lemma": (n, 0)}
        else:
            ch = S.li_cost(t)
            dg = L.dag_cost(t, cap)
            res = {"chain": ch[:2] if ch else None, "lemma": dg}
        for m in measures:
            r = res[m]
            if r is None:
                continue
            n_names[m] += 1
            c, st = r
            ps = per_size[m][n]
            old = ps.get(v)
            if old is None or c < old[0]:
                ps[v] = (c, st, t)
            D = n + math.log2(c)
            ob = bestD[m].get(v)
            if ob is None or D < ob[0] - 1e-12:
                bestD[m][v] = (D, n, c, st, t)
    print(f"size {n}: {len(by[n]):,} names, {time.time()-t0:.0f}s, "
          f"{len(S.ops):,} terms interned", file=sys.stderr, flush=True)

Kout = {str(v): (s, show(S, t)) for v, (s, t) in K.items()}
for m in measures:
    keep = {}
    for n in range(1, nmax + 1):
        # Pareto frontier of (cost, value) within this size
        best = -1
        for v, (c, st, t) in sorted(per_size[m][n].items(), key=lambda kv: (kv[1][0], -kv[0])):
            if v > best:
                best = v
                keep[t] = (n, v, c, st)
    for v, (D, n, c, st, t) in bestD[m].items():
        keep.setdefault(t, (n, v, c, st))
    rows = [{"size": n, "value": v, "cost": c, "steps": st,
             "term": show(S, t), "read": pretty(S, t)} for t, (n, v, c, st) in keep.items()]
    suffix = "" if m == "chain" else "L"
    name = f"{which}{nmax}{suffix}"
    with open(f"out_{name}.json", "w") as f:
        json.dump({"system": name, "nmax": nmax, "cap": cap, "n_names": n_names[m],
                   "rows": rows, "K": Kout}, f)
    print(f"{m}: {n_names[m]:,} names within cap, {len(rows):,} rows kept -> out_{name}.json",
          file=sys.stderr)
