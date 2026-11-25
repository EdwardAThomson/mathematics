"""Proof lengths for the families 2^(2^j) and 3^(2^j) in system B, named
by  (2)^(numeral 2^j)  and  (3)^(numeral 2^j)  (name size j + 6).
Shows how log2(value) grows with the proof length t, past the name sizes
the exhaustive tables reach."""
import math
from naming_records import Binary
from lemmas import Lemmas

Binary.VALCAP = 2 ** 9000
S = Binary(10 ** 12)
L = Lemmas(S)


def numeral(k):
    return S.zero if k == 0 else S.mk("D1" if k & 1 else "D0", numeral(k >> 1))


print("| name | size | log2 value | chain t | log2 value / sqrt(t) | lemma t (reuse) | log2 value / sqrt(t) | log2 value / t^(1/3), chain |")
print("|---|---|---|---|---|---|---|---|")
for base in (2, 3):
    for j in range(3, 13 if base == 2 else 11):
        t = S.mk("^", numeral(base), numeral(2 ** j))
        lv = math.log2(base) * 2 ** j
        ch = S.li_cost(t)[0]
        dg = L.dag_cost(t, 10 ** 12)[0]
        print(f"| {base}^(2^{j}) | {S.size[t]} | {lv:.0f} | {ch:,} | {lv / math.sqrt(ch):.3f} | "
              f"{dg:,} | {lv / math.sqrt(dg):.3f} | {lv / ch ** (1/3):.2f} |", flush=True)
