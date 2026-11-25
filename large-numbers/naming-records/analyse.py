#!/usr/bin/env python3
"""Turn out_<system>.json (from naming_records.py) into Markdown tables.

Usage: python3 analyse.py U > tables_U.md
"""
import json
import math
import sys

from naming_records import Unary, Binary, show

which = sys.argv[1]   # U, B, or with a suffix (UL, BL: lemma proofs)
d = json.load(open(f"out_{which}.json"))
rows, nmax, cap = d["rows"], d["nmax"], d["cap"]
budgets = [b for b in (10, 100, 1000, 3000, 10**4, 3 * 10**4, 10**5, 10**6, 10**7)
           if b <= cap]


def numeral_size(k):
    return k + 1 if which[0] == "U" else k.bit_length() + 1


def numeral_record(n):
    """Largest k whose numeral has size <= n."""
    return n - 1 if which[0] == "U" else 2 ** (n - 1) - 1


def big(k):
    if k < 10**6:
        return str(k)
    return f"≈2^{math.log2(k):.1f}"


print(f"## System {which}: names of size <= {nmax}, proof length <= {cap:,}\n")
print(f"{d.get('n_names', len(rows)):,} names have a proof within the cap.\n")

# ---- 1. record table ------------------------------------------------------
print("### 1. Record: largest k named by a name of size <= n with proof length <= t\n")
print("| n \\ t | " + " | ".join(f"{t:,}" for t in budgets) + " | numeral alone |")
print("|---|" + "---|" * (len(budgets) + 1))
by_n = {}
for r in rows:
    by_n.setdefault(r["size"], []).append(r)
for n in range(1, nmax + 1):
    cand = [r for m in range(1, n + 1) for r in by_n.get(m, [])]
    cells = []
    for t in budgets:
        ks = [r["value"] for r in cand if r["cost"] <= t]
        cells.append(big(max(ks)) if ks else "–")
    print(f"| {n} | " + " | ".join(cells) + f" | {big(numeral_record(n))} |")
capcells = [str(t - 1) if which[0] == "U" else f"2^{t - 1}" for t in budgets]
print("| Prop. 1 cap | " + " | ".join(f"{c}" if which[0] == "U" else c for c in capcells) + " | |")
print()

# ---- 2. crossover budgets --------------------------------------------------
print("### 2. When does a compound name first beat the numeral?\n")
print("For each name size n: the cheapest proof of any name of size <= n whose "
      "value exceeds the largest numeral of size <= n, and the largest number "
      "nameable at that size given unlimited budget (within the cap).\n")
print("| n | numeral record | first beaten by | its value | proof length | "
      "largest k at size n | its name | its proof length |")
print("|---|---|---|---|---|---|---|---|")
for n in range(1, nmax + 1):
    cand = [r for m in range(1, n + 1) for r in by_n.get(m, [])]
    nr = numeral_record(n)
    beat = [r for r in cand if r["value"] > nr]
    top = max(cand, key=lambda r: (r["value"], -r["cost"]))
    if beat:
        b = min(beat, key=lambda r: (r["cost"], -r["value"]))
        bcell = f"`{b['term']}` = {b['read']} | {big(b['value'])} | {b['cost']:,}"
    else:
        bcell = "– | – | –"
    print(f"| {n} | {big(nr)} | {bcell} | {big(top['value'])} | `{top['term']}` = {top['read']} | {top['cost']:,} |")
print()

# ---- 3. the staircase at the largest size ---------------------------------
print(f"### 3. The record as the budget grows (names of size <= {nmax})\n")
print("Every budget at which the record goes up, after the numerals run out.\n")
print("| budget t | record k | log2 k | witness | size | steps |")
print("|---|---|---|---|---|---|")
frontier = []
best = -1
for r in sorted(rows, key=lambda r: (r["cost"], -r["value"])):
    if r["value"] > best:
        best = r["value"]
        frontier.append(r)
for r in frontier:
    if r["value"] <= numeral_record(nmax) and r is not frontier[-1]:
        # skip the plain-numeral part of the staircase except its top
        nxt = frontier[frontier.index(r) + 1]
        if nxt["value"] <= numeral_record(nmax):
            continue
    print(f"| {r['cost']:,} | {big(r['value'])} | {math.log2(max(r['value'],1)):.2f} | "
          f"`{r['term']}` = {r['read']} | {r['size']} | {r['steps']:,} |")
print()

# ---- 4. cheapest names -----------------------------------------------------
if "K" in d:          # big_run.py stores K and its witnesses directly
    K = {int(v): s for v, (s, _) in d["K"].items()}
    Kname = {int(v): w for v, (_, w) in d["K"].items()}
else:
    S = Unary(10**9) if which[0] == "U" else Binary(10**9)
    by = S.enumerate(nmax)
    K, Kname = {}, {}
    for n in range(1, nmax + 1):
        for t in by[n]:
            v = S.val[t]
            if v is not None and v not in K:
                K[v] = n
                Kname[v] = show(S, t)
Dk, Dw = {}, {}
for r in rows:
    D = r["size"] + math.log2(r["cost"])
    k = r["value"]
    if k not in Dk or D < Dk[k] - 1e-12 or (abs(D - Dk[k]) < 1e-12 and r["size"] < Dw[k]["size"]):
        Dk[k], Dw[k] = D, r
kmax = 0
while kmax + 1 in Dk:
    kmax += 1

print("### 4. Cheapest names: D(k) = size + log2(proof length)\n")
print(f"Every k from 0 to {kmax:,} has a name of size <= {nmax}. "
      "`K(k)` = least name size, proof free. `D(k)` = least size + log2(proof). "
      "`N(k)` = the numeral's own cost, size + log2(size).\n")
wins = []
for k in sorted(Dk):
    ns = numeral_size(k)
    Nk = ns + math.log2(ns)
    if Dk[k] < Nk - 1e-9:
        wins.append((Nk - Dk[k], k, Nk))
first = min((k for _, k, _ in wins), default=None)
print(f"{len(wins)} numbers have a name that beats their own numeral on `D` "
      f"(the smallest is {big(first) if first is not None else '–'}); every other number "
      "named here is named most cheaply by its numeral. The 20 with the largest saving:\n")
print("| k | numeral cost N(k) | D(k) | saving | best name | size | proof length | K(k) |")
print("|---|---|---|---|---|---|---|---|")
for sav, k, Nk in sorted(wins, reverse=True)[:20]:
    r = Dw[k]
    print(f"| {big(k)} | {Nk:.2f} | {Dk[k]:.2f} | {sav:.2f} | `{r['term']}` = {r['read']} | {r['size']} | "
          f"{r['cost']:,} | {K.get(k,'–')} |")
print()

print("### 5. Largest number per naming cost\n")
dcomplete = (nmax + 1) + math.log2(nmax + 1)
print(f"For each d: the largest k with `D(k) <= d`, and the largest with `K(k) <= d` (proof free). "
      f"A name of size s has `D >= s + log2 s`, so the D column is complete (no larger name could "
      f"enter) for d < {dcomplete:.1f}; beyond that it is a lower bound. The K column is complete "
      f"only for d <= {nmax}.\n")
print("| d | largest k, D(k) <= d | name | size | proof | largest k, K(k) <= d |")
print("|---|---|---|---|---|---|")
for dd in range(2, int(dcomplete) + 1):
    ks = [k for k in Dk if Dk[k] <= dd]
    kk = [k for k in K if K[k] <= dd] if dd <= nmax else []
    if not ks:
        continue
    k = max(ks)
    print(f"| {dd} | {big(k)} | `{Dw[k]['term']}` = {Dw[k]['read']} | {Dw[k]['size']} | {Dw[k]['cost']:,} | "
          f"{big(max(kk)) if kk else '–'} |")
print()

# ---- 6. how good is the evaluation proof? ---------------------------------
cmp_rows = [r for r in rows if "min_cost" in r]
if cmp_rows:
    done = [r for r in cmp_rows if isinstance(r["min_cost"], int)]
    eq = [r for r in done if r["min_cost"] == r["cost"]]
    worst = max(done, key=lambda r: r["cost"] / r["min_cost"])
    print("### 6. Evaluation proof versus shortest proof in any order\n")
    print(f"For the {len(cmp_rows):,} names of size <= {d['exact_n']} with evaluation proof "
          f"<= {d['exact_cap']}: the exhaustive search finished for {len(done):,}; "
          f"the evaluation proof is the shortest for {len(eq):,} of those. "
          f"Largest ratio: `{worst['term']}`, evaluation {worst['cost']} vs shortest "
          f"{worst['min_cost']}.\n")
    # does using shortest proofs change any record?
    changed = []
    for n in range(1, d["exact_n"] + 1):
        for t in budgets:
            if t > d["exact_cap"]:
                continue
            c1 = [r["value"] for r in done if r["size"] <= n and r["cost"] <= t]
            c2 = [r["value"] for r in done if r["size"] <= n and r["min_cost"] <= t]
            if (max(c1) if c1 else -1) != (max(c2) if c2 else -1):
                changed.append((n, t))
    print(f"Record-table cells (n <= {d['exact_n']}, t <= {d['exact_cap']}) that change if shortest "
          f"proofs are used: {changed if changed else 'none'}.\n")
