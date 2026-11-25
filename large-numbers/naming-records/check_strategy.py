"""Independent check of naming_records.li_cost: simulate the evaluation
strategy one rewrite step at a time and compare totals.

Strategy, per step: at the root, fire an erasing rule if one applies;
otherwise step inside the leftmost non-normal argument (same rule there);
if all arguments are normal, fire the root rule."""
import random
from naming_records import Unary, Binary


def step(S, t):
    sym, args = S.ops[t]
    for r in S.root_steps(t):
        if S.is_erasing(t, r):
            return r
    for i, a in enumerate(args):
        if not S.is_normal(a):
            new = list(args)
            new[i] = step(S, a)
            return S.mk(sym, *new)
    return S.root_steps(t)[0]


bad = n = 0
for cls, N in ((Unary, 10), (Binary, 8)):
    S = cls(10**6)
    by = S.enumerate(N)
    terms = [t for k in by for t in by[k]]
    random.seed(1)
    for t in random.sample(terms, min(5000, len(terms))):
        r = S.li_cost(t)
        if r is None:
            continue
        u, tot, st = t, 0, 0
        while not S.is_normal(u):
            tot += S.size[u]
            u = step(S, u)
            st += 1
        tot += S.size[u]
        n += 1
        if (tot, st, S.val[u]) != (r[0], r[1], S.val[t]):
            bad += 1
print(n, "names checked,", bad, "mismatches")
