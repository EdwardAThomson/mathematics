#!/usr/bin/env python3
"""Lemma-proof lengths for every name, in the row format analyse.py reads.

Usage: python3 lemma_run.py U 12 10000000   -> out_UL.json
       python3 lemma_run.py B 10 10000000   -> out_BL.json
Each row: size, value, cost (= dag: lemma proof with reuse), tree (no reuse),
chain (the evaluation chain of naming_records.py), lemmas (number of distinct
lemmas), term, read.  "steps" is set to the number of lemmas so analyse.py's
tables show it.
"""
import json
import sys

from naming_records import Unary, Binary, show, pretty
from lemmas import Lemmas

which, nmax, cap = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
S = Unary(cap) if which == "U" else Binary(cap)
L = Lemmas(S)
by = S.enumerate(nmax)
rows = []
for n in range(1, nmax + 1):
    for t in by[n]:
        if S.val[t] is None:
            continue
        if S.is_normal(t):
            dag, nl, tree = S.size[t], 0, S.size[t]
        else:
            r = L.dag_cost(t, cap)
            if r is None:
                continue
            dag, nl = r
            tree = L.tree_cost(t, 10**15)
        ch = S.li_cost(t)
        rows.append({"size": n, "value": S.val[t], "cost": dag, "tree": tree,
                     "chain": ch[0] if ch else None, "steps": nl,
                     "term": show(S, t), "read": pretty(S, t)})
    print(f"size {n}: {len(by[n])} terms, {len(L.info)} lemmas", file=sys.stderr, flush=True)
with open(f"out_{which}L.json", "w") as f:
    json.dump({"system": which + "L", "nmax": nmax, "cap": cap, "rows": rows}, f)
