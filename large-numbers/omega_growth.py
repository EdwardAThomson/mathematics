"""Numerics for OMEGA-FOR-NAMING.md: total weight nu(F) and critical exponent
gamma* = inf{g : sum_F nu(phi)^g < inf} for the two coin processes.

Grammar (16 tokens): V := x | up V ;  T := 0 | 1 | + T T | * T T | V ;
F := top | bot | (= < != !<) T T | (and or) F F | (all ex) F.
"""
import math

def solve(wf, wt, wv, typed):
    """Smallest fixed point (F) of the weighted grammar, or None if divergent."""
    if wv >= 1: return None
    V = wv / (1 - wv)
    # uniform: T = wt(2 + 2T^2) + V ; typed: T = wt(2 + 2T^2 + V)
    c = wt * (2 + V) if typed else 2 * wt + V
    disc = 1 - 8 * wt * c
    if disc < 0: return None
    T = (1 - math.sqrt(disc)) / (4 * wt)
    A, B, C = 2 * wf, 2 * wf - 1, wf * (2 + 4 * T * T)
    d = B * B - 4 * A * C
    if d < 0: return None
    return (-B - math.sqrt(d)) / (2 * A)

def crit(weights, typed):
    lo, hi = 0.05, 1.0
    for _ in range(200):
        m = (lo + hi) / 2
        if solve(*weights(m), typed) is None: lo = m
        else: hi = m
    return hi

U16 = lambda g: (16.0 ** -g,) * 3
TY = lambda g: (10.0 ** -g, 5.0 ** -g, 2.0 ** -g)
print("U16: nu(F) = %.6f  gamma* = %.6f  growth = %.6f" %
      (solve(*U16(1), False), crit(U16, False), 16 ** crit(U16, False)))
print("TY : nu(F) = %.6f  gamma* = %.6f" % (solve(*TY(1), True), crit(TY, True)))

# exact counts for U16 (cross-check of growth rate)
N = 300
V = [0] * (N + 1); T = [0] * (N + 1); F = [0] * (N + 1)
conv = lambda A, B, m: sum(A[i] * B[m - i] for i in range(1, m))
for s in range(1, N + 1):
    V[s] = 1
    T[s] = (2 if s == 1 else 0) + 2 * conv(T, T, s - 1) + V[s]
    F[s] = (2 if s == 1 else 0) + 4 * conv(T, T, s - 1) + 2 * conv(F, F, s - 1) + 2 * F[s - 1]
print("U16 count ratio F[300]/F[299] = %.4f" % (F[N] / F[N - 1]))

# --- Section 3 carriers: unequal-letter-cost rate r with sum_steps 2^{-r cost} = 1
def rate(costs):
    lo, hi = 0.0, 1.0
    for _ in range(200):
        m = (lo + hi) / 2
        if sum(2 ** (-m * c) for c in costs) > 1: lo = m
        else: hi = m
    return lo
for M in (10, 1000):
    u16 = [8, 16] + [4 * (j + 4) for j in range(1, M + 1)]
    c1 = math.log2(1250)
    ty = [math.log2(50), c1] + [c1 + j + 1 for j in range(1, M + 1)]
    print("carrier rate m=%d: U16 %.4f  TY %.4f" % (M, rate(u16), rate(ty)))

# --- distinct values of closed terms over 0,1,+,x with at most k tokens
vals = {1: {0, 1}}
for k in range(2, 16):
    S = set()
    for a in range(1, k - 1):
        b = k - 1 - a
        for x in vals.get(a, ()):
            for y in vals.get(b, ()):
                S.add(x + y); S.add(x * y)
    vals[k] = S
print("distinct closed-term values with <= 15 tokens:", len(set().union(*vals.values())))
