#!/usr/bin/env python3
"""
The cube gadget of CALCNAME2-HARDNESS.md section 2.3, checked on random 3-CNFs.

Positions: a constant c, one constant g_i per variable, literal positions
a[(i,1)] (for y_i) and a[(i,0)] = a[(i,1)] + 2(g_i - c) (for not y_i).
A legit name for an assignment y is  tau_y = z^3  with
    z = K + sum_i 2^(L a[(i, y_i)]),   K = 2^(L c) + sum_i 2^(L g_i).
Blocks are L bits wide (L = 8: every checked block holds at most 6).
Pattern p (every other block is *):
  * block 3c                          -> 1
  * block 2g_i + a[(i,1)] = 2c + a[(i,0)] -> 3  (exactly one literal of y_i chosen)
  * block a[l1]+a[l2]+a[l3] for the three falsifying literals of each clause -> 0
Checks: (1) the positions make each checked block receive exactly the intended
ordered triples; (2) tau_y matches p iff y satisfies phi, for every y;
(3) the "omission cheater"  K^3 + 3 * sum_i 2^(L (2 g_i + a[(i,1)])), which
encodes no assignment at all, also matches p, so any reduction built on this
gadget is unsound; (4) B-term sizes of the legit names and of the cheater.
"""
import itertools, random

L = 8

def bsize(k):
    return 1 if k == 0 else k.bit_length() + 1

def pow2(e):             # size of ^(D0(D1 0), numeral e), the term 2^e
    return 1 + 3 + bsize(e)

def plus(sizes):         # a sum of t terms has t - 1 '+' symbols
    return sum(sizes) + len(sizes) - 1

def build(v, phi, rnd):
    R = 4 * v ** 3
    while True:
        c = rnd.randrange(R, 2 * R)
        g = [c + rnd.randrange(1, R) for _ in range(v)]
        a = {}
        for i in range(v):
            a[(i, 1)] = rnd.randrange(8 * R, 24 * R)
            a[(i, 0)] = a[(i, 1)] + 2 * (g[i] - c)
        sup = {"c": c, **{("g", i): g[i] for i in range(v)}, **a}
        blocks = {}
        for t in itertools.product(sup, repeat=3):
            blocks.setdefault(sum(sup[x] for x in t), set()).add(t)
        want, ok = {3 * c: 1}, blocks[3 * c] == {("c", "c", "c")}
        for i in range(v):
            pos = 2 * g[i] + a[(i, 1)]
            ok &= blocks[pos] == (set(itertools.permutations([("g", i), ("g", i), (i, 1)])) |
                                  set(itertools.permutations(["c", "c", (i, 0)])))
            want[pos] = 3
        for cl in phi:
            bad = [(i, 1 - b) for (i, b) in cl]
            pos = sum(a[l] for l in bad)
            ok &= blocks[pos] == set(itertools.permutations(bad))
            want[pos] = 0
        if ok:
            return c, g, a, want

def trial(v, r, seed):
    rnd = random.Random(seed)
    phi = [[(i, rnd.randint(0, 1)) for i in rnd.sample(range(v), 3)] for _ in range(r)]
    c, g, a, want = build(v, phi, rnd)
    mask = (1 << L) - 1
    matches = lambda X: all((X >> (L * p)) & mask == w for p, w in want.items())
    K = (1 << (L * c)) + sum(1 << (L * gi) for gi in g)
    Ksize = plus([pow2(L * c)] + [pow2(L * gi) for gi in g])
    agree, sizes, nsat = True, [], 0
    for y in itertools.product([0, 1], repeat=v):
        z = K + sum(1 << (L * a[(i, y[i])]) for i in range(v))
        sat = all(any(y[i] == b for (i, b) in cl) for cl in phi)
        nsat += sat
        agree &= matches(z ** 3) == sat
        zsize = plus([Ksize] + [pow2(L * a[(i, y[i])]) for i in range(v)])
        sizes.append(1 + zsize + 3)                       # ^(z, 3), numeral 3 has size 3
    cheat = K ** 3 + 3 * sum(1 << (L * (2 * g[i] + a[(i, 1)])) for i in range(v))
    csize = 1 + (1 + Ksize + 3) + (1 + 3 + plus([pow2(L * (2 * g[i] + a[(i, 1)])) for i in range(v)]))
    return agree, matches(cheat), nsat, min(sizes), max(sizes), csize

if __name__ == "__main__":
    print("v  r  seed | tau_y matches iff y satisfies | cheater matches | #sat | legit size | cheater size")
    for v, r in [(5, 12), (6, 20), (8, 34), (10, 43)]:
        for seed in range(3 if v < 10 else 2):
            ag, ch, ns, lo, hi, cs = trial(v, r, seed)
            print(f"{v:2d} {r:2d} {seed:4d} | {ag} | {ch} | {ns} | {lo}..{hi} | {cs}")
