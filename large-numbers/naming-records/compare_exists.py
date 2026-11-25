"""Numbers whose property name (exists.py) is cheaper than every term name
(lemma proofs, same size limit) or than its own numeral.  Usage: compare_exists.py out_BE10.json out_BL.json"""
import json, math, sys
E = json.load(open(sys.argv[1]))["best"]
d = json.load(open(sys.argv[2]))
Dt, Wt = {}, {}
for r in d["rows"]:
    D = r["size"] + math.log2(r["cost"])
    if r["value"] not in Dt or D < Dt[r["value"]]:
        Dt[r["value"]], Wt[r["value"]] = D, r
wins = []
for k, (D, n, cost, name) in E.items():
    k = int(k)
    ns = k.bit_length() + 1                      # the numeral is always a name
    Nk = ns + math.log2(ns)
    if Nk < Dt.get(k, math.inf):
        Dt[k] = Nk
        Wt[k] = {"read": "numeral", "size": ns, "cost": ns}
    if D < Dt[k] - 1e-9:
        wins.append((Dt.get(k, math.inf) - D, k, D, n, cost, name))
print(f"{len(E):,} numbers have a property name; {len(wins)} are cheaper that way than as any term name.\n")
print("| k | property name | size | proof | D | best term name | size | proof | D |")
print("|---|---|---|---|---|---|---|---|---|")
for sav, k, D, n, cost, name in sorted(wins, key=lambda w: w[1]):
    r = Wt.get(k)
    tn = f"`{r['read']}` | {r['size']} | {r['cost']:,} | {Dt[k]:.2f}" if r else "none | | |"
    print(f"| {k:,} | `{name}` | {n} | {cost:,} | {D:.2f} | {tn} |")
