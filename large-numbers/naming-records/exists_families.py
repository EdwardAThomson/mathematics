"""Property names for two families that have no short term names here:
   (4^j - 1)/3 = 0101...01 (binary), named by  S(x*3) = 4^j
   (3^j - 1)/2,                        named by  S(x*2) = 3^j
Compare D (size + log2 proof) with the numeral and with the best term name
of size <= 11 (from out_B11L.json, if present)."""
import json, math, os
from naming_records import Binary, pretty
from lemmas import Lemmas

S = Binary(10**9)
L = Lemmas(S)


def numeral(k):
    return S.zero if k == 0 else S.mk("D1" if k & 1 else "D0", numeral(k >> 1))


Dt = {}
if os.path.exists("out_B11L.json"):
    for r in json.load(open("out_B11L.json"))["rows"]:
        D = r["size"] + math.log2(r["cost"])
        Dt[r["value"]] = min(D, Dt.get(r["value"], math.inf))


def closure_cost(us):
    seen, tot = set(), 0
    for u in us:
        if S.is_normal(u) or u in seen:
            continue
        seen.add(u)
        st = [u]
        while st:
            v = st.pop()
            own, kids, _ = L.lem(v)
            tot += own
            for w in kids:
                if w not in seen:
                    seen.add(w)
                    st.append(w)
    return tot


print("| family | j | k (bits) | property name size | proof | D | numeral D | best term D, size <= 11 |")
print("|---|---|---|---|---|---|---|---|")
for fam, base, mult in (("(4^j-1)/3", 4, 3), ("(3^j-1)/2", 3, 2)):
    for j in (4, 8, 12, 16, 24, 32, 48, 64):
        k = (base**j - 1) // (base - 1) if base == 4 else (base**j - 1) // 2
        if base == 4:
            k = (4**j - 1) // 3
        c = S.mk("^", numeral(base), numeral(j))
        sk = S.mk("S", S.mk("*", numeral(k), numeral(mult)))
        name_size = (1 + 1 + 1 + S.size[numeral(mult)]) + S.size[c] + 1   # S(x*m) = c
        cost = closure_cost([sk, c]) + S.size[sk] + S.size[c]
        D = name_size + math.log2(cost)
        ns = k.bit_length() + 1
        N = ns + math.log2(ns)
        bt = Dt.get(k)
        print(f"| {fam} | {j} | {k.bit_length()} | {name_size} | {cost:,} | {D:.1f} | {N:.1f} | "
              f"{f'{bt:.1f}' if bt else 'none'} |", flush=True)
