"""Chain proof versus lemma proofs (no reuse / reuse) for a few tower-shaped
binary names that are too big for the exhaustive tables."""
import math
from naming_records import Binary, show, pretty
from lemmas import Lemmas

Binary.VALCAP = 2 ** 40000
S = Binary(10 ** 9)
L = Lemmas(S)
z = S.zero


def num(k):
    if k == 0:
        return z
    return S.mk("D1" if k & 1 else "D0", num(k >> 1))


def pw(a, b):
    return S.mk("^", a, b)


two, three = num(2), num(3)
names = [pw(two, pw(two, two)), pw(three, pw(three, three)), pw(two, pw(two, pw(two, two))),
         pw(two, pw(three, num(7))), pw(two, pw(two, pw(two, three))), pw(three, pw(two, pw(two, three)))]
print("| name | reads as | size | log2 value | chain | lemmas, no reuse | lemmas, reuse | distinct lemmas |")
print("|---|---|---|---|---|---|---|---|")
for t in names:
    v = S.val[t]
    ch = S.li_cost(t)
    tr = L.tree_cost(t, 10 ** 30)
    dg = L.dag_cost(t, 10 ** 30)
    print(f"| `{show(S, t)}` | {pretty(S, t)} | {S.size[t]} | {math.log2(v):.0f} | "
          f"{f'{ch[0]:,}' if ch else '>cap'} | {tr:,} | {dg[0]:,} | {dg[1]:,} |", flush=True)
