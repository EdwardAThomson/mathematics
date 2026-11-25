"""For the record-holding names with evaluation proof <= LIMIT, search for a
shorter proof in any rewriting order (A*).  Usage: check_frontier.py B 1100"""
import json, sys, time
from naming_records import Unary, Binary

which, limit = sys.argv[1], int(sys.argv[2])
d = json.load(open(f"out_{which}.json"))
rows = sorted(d["rows"], key=lambda r: (r["cost"], -r["value"]))
front, best = [], -1
for r in rows:
    if r["value"] > best:
        best = r["value"]
        front.append(r)
S = Unary(limit) if which == "U" else Binary(limit)
by = S.enumerate(d["nmax"])
from naming_records import show
ids = {show(S, t): t for n in by for t in by[n]}
print("| witness | value | evaluation proof | shortest, any order |")
print("|---|---|---|---|")
for r in front:
    if r["cost"] > limit or r["steps"] == 0:
        continue
    t = ids[r["term"]]
    S.cap = r["cost"]
    try:
        a = S.astar_cost(t, 2_000_000)
        res = a[0] if a else "?"
    except OverflowError:
        res = "search limit"
    print(f"| `{r['term']}` | {r['value']} | {r['cost']} | {res} |", flush=True)
