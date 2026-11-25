#!/usr/bin/env python3
"""Proposition 2 of PROOF-BUDGETS-AND-COMPLEXITY.md, written out line by line.

The note's first version of Proposition 2 gave the lower bounds
sqrt(t/C) (unary target) and 2^((t/C)^(1/3)/2) (binary target).  Those
came from proving equations between closed numerals one digit at a time.
This file builds shorter proofs that use universally quantified lemmas,
each proved from the one before it by *doubling*:

  unary   C_n   all a b  (a = b -> S^n(a) = S^n(b))        S(s) = s + 1
          T_n   all z u  (z + S^n(u) = S^n(z + u))
          R_n   all z    (z + nbar = S^n(z))
  binary  B_n   all a b  (a = b -> D^n(a) = D^n(b))        D(s) = (1+1)*s
          A_n   all w z  (D^n(w) * z = D^n(w * z))

for n = 1, 2, 4, ...  The step from n to 2n instantiates the lemma for n
twice (once at D^n(w) or S^n(u)) and chains: a bounded number of lines,
each of size O(n).  So all lemmas up to n = 2^a together cost O(2^a)
symbols, against O(4^a) or more for the digit-by-digit proofs.

With them:

  unary   bin(2^a) = (2^a)bar        in O(2^a) symbols, so the formula
          x = bin(2^a), of size O(a), names 2^a with a proof of length
          O(2^a).  Hence Big^t(n) >= t/C once n >= c log t.

  binary  w_i = bin(2^(2^i)) = D^(2^i)(1), and w_i * w_i = w_(i+1) in
          O(2^i) symbols.  The formula chi_j(x), "x is 2 squared j
          times", of size O(j), names 2^(2^j) with a proof of length
          O(2^j).  Hence Big^t(n) >= 2^(t/C) once n >= c log t.

Proposition 1 gives t/2 and 2^t from above, so in both cases the budget
is reached up to a constant factor (unary) or a constant factor in the
exponent (binary).

The system is H from naming-depth/collision_check.py (same checker,
imported), with two additions, both standard:

  Q2  all v (A -> B) -> (A -> all v B)    v not free in A
  A3  all x y z  (x * y) * z = x * (y * z)   (a PA- axiom, Kaye's A3;
                                              collision_check did not need it)

"exists v A" abbreviates  not all v not A.  Q2 is used only to
eliminate an existential (in the binary case).

Running the file builds the proofs, checks every line, and prints the
lengths.  It checks instances, a = 1..A and j = 1..J; the lemma blocks
have a shape that does not depend on n, so the per-step cost is a fixed
number of lines of size O(n), which the script also reports.

Usage: python3 doubling_check.py [A] [J]      (defaults 16 14)
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'naming-depth'))
import collision_check as cc                                     # noqa: E402
from collision_check import (mk, var, add, mul, eq, neg, imp, conj, forall,   # noqa: E402
                             ZERO, ONE, TWO, binnum, size, length, subst,
                             Builder, A2, A4, A7)

sys.setrecursionlimit(1_000_000)

X_, Y_, Z_ = var('x'), var('y'), var('z')
A3 = forall('x', forall('y', forall('z',
            eq(mul(mul(X_, Y_), Z_), mul(X_, mul(Y_, Z_))))))


# ------------------------------------------------------------ the checker

def free_vars(e, acc=None, bound=frozenset()):
    if acc is None:
        acc = set()
    k = e[0]
    if k == 'v':
        if e[1] not in bound:
            acc.add(e[1])
    elif k in ('0', '1'):
        pass
    elif k == 'all':
        free_vars(e[2], acc, bound | {e[1]})
    else:
        for c in e[1:]:
            free_vars(c, acc, bound)
    return acc


def is_Q2(f):
    """all v (A -> B) -> (A -> all v B), v not free in A."""
    if f[0] != 'imp':
        return False
    l, r = f[1], f[2]
    if l[0] != 'all' or l[2][0] != 'imp' or r[0] != 'imp' or r[2][0] != 'all':
        return False
    v, A, B = l[1], l[2][1], l[2][2]
    return r[1] is A and r[2][1] == v and r[2][2] is B and v not in free_vars(A)


EXTRA = [A3]


def check(lines):
    """Is `lines` a proof in H + Q2 from PA- (with A3)?  (True, None) or
    (False, index of the first bad line)."""
    extra_ids = frozenset(id(cc.canon(e)) for e in EXTRA)
    seen = set()
    by_consequent = {}
    for n, f in enumerate(lines):
        f = cc.canon(f)
        i = id(f)
        ok = (i in seen or i in cc._PA_IDS or i in extra_ids
              or cc.is_logical_axiom(f) or is_Q2(f))
        if not ok and i in by_consequent:
            ok = any(a in seen for a in by_consequent[i])
        if not ok and f[0] == 'all':
            ok = id(f[2]) in seen
        if not ok:
            return (False, n)
        seen.add(i)
        if f[0] == 'imp':
            by_consequent.setdefault(id(f[2]), []).append(id(f[1]))
    return (True, None)


# ---------------------------------------------- propositional and quantifier

def exists(v, a):
    return neg(forall(v, neg(a)))


class B2(Builder):

    def gen(self, v, f):
        return self.emit(forall(v, f))

    def inst_open(self, lemma, terms):
        """Instantiate the leading quantifiers at (possibly open) terms."""
        return self.inst(lemma, terms)

    def identity(self, A):                       # A -> A
        aa = imp(A, A)
        h1 = self.emit(imp(A, imp(aa, A)))
        h2 = self.mp(h1, self.emit(imp(h1, imp(imp(A, aa), aa))))
        return self.mp(self.emit(imp(A, aa)), h2)

    def dne(self, A):                            # not not A -> A
        nA, nnA = neg(A), neg(neg(A))
        nnnnA = neg(neg(nnA))
        s1 = self.emit(imp(nnA, imp(nnnnA, nnA)))                        # P1
        s2 = self.emit(imp(imp(nnnnA, nnA), imp(nA, neg(nnA))))          # P3
        s3 = self.syllogism(s1, s2)                   # nnA -> (nA -> nnnA)
        s4 = self.emit(imp(imp(nA, neg(nnA)), imp(nnA, A)))              # P3
        s5 = self.syllogism(s3, s4)                   # nnA -> (nnA -> A)
        p2 = self.emit(imp(s5, imp(imp(nnA, nnA), imp(nnA, A))))         # P2
        s7 = self.mp(s5, p2)
        return self.mp(self.identity(nnA), s7)

    def dni(self, A):                            # A -> not not A
        d = self.dne(neg(A))                          # nnnA -> nA
        return self.mp(d, self.emit(imp(d, imp(A, neg(neg(A))))))       # P3

    def contra(self, ab):                        # A -> B  |-  not B -> not A
        A, B = ab[1], ab[2]
        s = self.syllogism(self.syllogism(self.dne(A), ab), self.dni(B))  # nnA -> nnB
        return self.mp(s, self.emit(imp(s, imp(neg(B), neg(A)))))         # P3

    # working under a hypothesis H: a formula X is held as the line H -> X
    def lift(self, H, x):                        # X  |-  H -> X
        return self.mp(x, self.emit(imp(x, imp(H, x))))

    def mp_h(self, hx, hxy):                     # H -> X, H -> (X -> Y)  |-  H -> Y
        H, Xf, Yf = hx[1], hx[2], hxy[2][2]
        assert hxy[1] is H and hxy[2][1] is Xf
        p2 = self.emit(imp(hxy, imp(hx, imp(H, Yf))))
        return self.mp(hx, self.mp(hxy, p2))

    def ax_h(self, H, f):                        # an axiom or theorem f, as H -> f
        return self.lift(H, self.emit(f))

    def trans_h(self, h1, h2):                   # H -> s = t, H -> t = r  |-  H -> s = r
        H, e1, e2 = h1[1], h1[2], h2[2]
        e3 = self.ax_h(H, imp(e1, imp(e2, eq(e1[1], e2[2]))))             # E3
        return self.mp_h(h2, self.mp_h(h1, e3))

    def drop_mid(self, a_e_c, e):                # A -> (E -> C), E  |-  A -> C
        A, C = a_e_c[1], a_e_c[2][2]
        ae = self.lift(A, e)
        return self.mp_h(ae, a_e_c)

    def ex_intro(self, v, body, t):              # body[t/v] -> exists v body
        inst = subst(body, v, t)
        q = self.emit(imp(forall(v, neg(body)), neg(inst)))             # Q1
        c = self.contra(q)                            # nn inst -> exists
        return self.syllogism(self.dni(inst), c)

    def ex_elim(self, v, ab):                    # A(v) -> B (v not free in B)  |-  exists v A -> B
        A, B = ab[1], ab[2]
        c = self.contra(ab)                           # not B -> not A
        g = self.gen(v, c)
        q2 = self.emit(imp(g, imp(neg(B), forall(v, neg(A)))))
        h = self.mp(g, q2)                            # not B -> all v not A
        c2 = self.contra(h)                           # exists v A -> nn B
        return self.syllogism(c2, self.dne(B))


# ----------------------------------------------------------------- terms

def S(s, n=1):
    for _ in range(n):
        s = add(s, ONE)
    return s


def D(s, n=1):
    for _ in range(n):
        s = mul(TWO, s)
    return s


def unary(n):
    """0bar = 0, 1bar = 1, (m+1)bar = mbar + 1."""
    return ZERO if n == 0 else S(ONE, n - 1)


# lemma variables avoid x, y, z, which the PA- axioms bind
VA, VB, VZ, VU, VW = var('a'), var('b'), var('p'), var('q'), var('r')
VX = var('u')         # the variable of the binary uniqueness lemmas
# keep these across cc.reset()
cc._base_table.update(cc._table)


# ------------------------------------------------------- unary lemmas

def unary_lemmas(b, top):
    """C_n, T_n, R_n for n = 1, 2, ..., top (powers of two)."""
    C, T, R = {}, {}, {}
    # n = 1
    c1 = b.emit(imp(eq(VA, VB), eq(S(VA), S(VB))))                       # E4
    C[1] = b.gen('a', b.gen('b', c1))
    a1 = b.inst(cc.A1, [VZ, VU, ONE])                 # (z+u)+1 = z+(u+1)
    T[1] = b.gen('p', b.gen('q', b.sym(a1)))
    R[1] = b.gen('p', b.refl(add(VZ, ONE)))
    stats = []
    n = 1
    while 2 * n <= top:
        start = len(b.lines)
        # C_2n
        c_ab = b.inst(C[n], [VA, VB])
        c_sn = b.inst(C[n], [S(VA, n), S(VB, n)])
        C[2 * n] = b.gen('a', b.gen('b', b.syllogism(c_ab, c_sn)))
        # T_2n
        e1 = b.inst(T[n], [VZ, S(VU, n)])
        e2 = b.inst(T[n], [VZ, VU])
        e3 = b.mp(e2, b.inst(C[n], [e2[1], e2[2]]))
        T[2 * n] = b.gen('p', b.gen('q', b.trans(e1, e3)))
        # R_2n
        nb = unary(n)
        e1 = b.inst(T[n], [VZ, nb])
        e2 = b.inst(R[n], [VZ])
        e3 = b.mp(e2, b.inst(C[n], [e2[1], e2[2]]))
        R[2 * n] = b.gen('p', b.trans(e1, e3))
        assert R[2 * n][2][2] is S(VZ, 2 * n) and R[2 * n][2][1][2] is unary(2 * n)
        stats.append((2 * n, len(b.lines) - start,
                      max(size(f) for f in b.lines[start:])))
        n *= 2
    return C, T, R, stats


def unary_name(a):
    """A proof of  all x (x = bin(2^a) <-> x = (2^a)bar)."""
    b = B2()
    top = 2 ** max(a - 1, 0)
    C, T, R, stats = unary_lemmas(b, top)
    lem_len = length(b.lines)
    # bin(2^k) = (2^k)bar
    E = b.refl(ONE)
    for k in range(1, a + 1):
        m = 2 ** (k - 1)
        mb = unary(m)
        e1 = b.congR(E, TWO, '*')                     # (1+1)*bin(m) = (1+1)*mbar
        e2 = b.dbl(mb)                                # (1+1)*mbar = mbar + mbar
        e3 = b.inst(R[m], [mb])                       # mbar + mbar = S^m(mbar)
        E = b.chain(e1, e2, e3)
    K, U = binnum(2 ** a), unary(2 ** a)
    assert E[1] is K and E[2] is U
    phi = eq(X_, K)
    t1 = b.drop_mid(b.emit(imp(phi, imp(E, eq(X_, U)))), E)              # E3
    Es = b.sym(E)
    t2 = b.drop_mid(b.emit(imp(eq(X_, U), imp(Es, phi))), Es)            # E3
    both = b.mp(t2, b.mp(t1, b.emit(imp(t1, imp(t2, conj(t1, t2))))))  # C3
    b.gen('x', both)
    return b.lines, phi, lem_len, stats


# ------------------------------------------------------ binary lemmas

def binary_lemmas(b, top):
    """B_n, A_n for n = 1, 2, ..., top."""
    Bl, Al = {}, {}
    Bl[1] = b.gen('a', b.gen('b', b.emit(imp(eq(VA, VB), eq(D(VA), D(VB))))))   # E7
    Al[1] = b.gen('r', b.gen('p', b.inst(A3, [TWO, VW, VZ])))
    stats = []
    n = 1
    while 2 * n <= top:
        start = len(b.lines)
        c_ab = b.inst(Bl[n], [VA, VB])
        c_dn = b.inst(Bl[n], [D(VA, n), D(VB, n)])
        Bl[2 * n] = b.gen('a', b.gen('b', b.syllogism(c_ab, c_dn)))
        e1 = b.inst(Al[n], [D(VW, n), VZ])            # D^2n(w)*z = D^n(D^n(w)*z)
        e2 = b.inst(Al[n], [VW, VZ])                  # D^n(w)*z = D^n(w*z)
        e3 = b.mp(e2, b.inst(Bl[n], [e2[1], e2[2]]))
        Al[2 * n] = b.gen('r', b.gen('p', b.trans(e1, e3)))
        stats.append((2 * n, len(b.lines) - start,
                      max(size(f) for f in b.lines[start:])))
        n *= 2
    return Bl, Al, stats


def w(i):
    return D(ONE, 2 ** i)


def square(b, Bl, Al, i):
    """w_i * w_i = w_(i+1)."""
    M, wi = 2 ** i, w(i)
    e1 = b.inst(Al[M], [ONE, wi])                     # D^M(1)*wi = D^M(1*wi)
    e2 = b.trans(b.inst(A4, [ONE, wi]), b.inst(A7, [wi]))   # 1*wi = wi
    e3 = b.mp(e2, b.inst(Bl[M], [e2[1], e2[2]]))
    r = b.trans(e1, e3)
    assert r[1] is mul(wi, wi) and r[2] is w(i + 1)
    return r


def chi(i, u):
    """chi_0(u): u = 1+1;  chi_i(u): exists y_(i-1) (u = y*y and chi_(i-1)(y))."""
    if i == 0:
        return eq(u, TWO)
    y = 'y%d' % (i - 1)
    return exists(y, conj(eq(u, mul(var(y), var(y))), chi(i - 1, var(y))))


def binary_name(j):
    """A proof of  all x (chi_j(x) <-> x = bin(2^(2^j)))."""
    b = B2()
    Bl, Al, stats = binary_lemmas(b, 2 ** max(j - 1, 0))
    lem_len = length(b.lines)
    sq = {i: square(b, Bl, Al, i) for i in range(j)}
    # existence: chi_i(w_i)
    X = {0: b.inst(A7, [TWO])}                        # (1+1)*1 = 1+1
    assert X[0] is chi(0, w(0))
    for i in range(1, j):
        y = 'y%d' % (i - 1)
        body = conj(eq(w(i), mul(var(y), var(y))), chi(i - 1, var(y)))
        eqn = b.sym(sq[i - 1])                        # w_i = w'*w'
        c3 = b.emit(imp(eqn, imp(X[i - 1], conj(eqn, X[i - 1]))))   # C3
        both = b.mp(X[i - 1], b.mp(eqn, c3))
        assert both is subst(body, y, w(i - 1))
        X[i] = b.mp(both, b.ex_intro(y, body, w(i - 1)))
        assert X[i] is chi(i, w(i))
    # uniqueness: all u (chi_i(u) -> u = w_i)
    Y = {}
    y0 = b.emit(imp(eq(VX, TWO), imp(eq(TWO, w(0)), eq(VX, w(0)))))       # E3
    Y[0] = b.gen('u', b.drop_mid(y0, b.sym(b.inst(A7, [TWO]))))
    for i in range(1, j + 1):
        y = 'y%d' % (i - 1)
        vy = var(y)
        body = conj(eq(VX, mul(vy, vy)), chi(i - 1, vy))
        H = body
        h_a = b.ax_h(H, imp(H, H[1]))                 # C1
        h_a = b.mp_h(b.identity(H), h_a)              # H -> u = y*y
        h_c = b.mp_h(b.identity(H), b.ax_h(H, imp(H, H[2])))       # H -> chi(y)
        yi = b.inst(Y[i - 1], [vy])                   # chi(y) -> y = w'
        h_y = b.mp_h(h_c, b.lift(H, yi))              # H -> y = w'
        wp = w(i - 1)
        h_1 = b.mp_h(h_y, b.ax_h(H, imp(eq(vy, wp), eq(mul(vy, vy), mul(wp, vy)))))   # E6
        h_2 = b.mp_h(h_y, b.ax_h(H, imp(eq(vy, wp), eq(mul(wp, vy), mul(wp, wp)))))   # E7
        h_s = b.lift(H, sq[i - 1])
        r = b.trans_h(b.trans_h(b.trans_h(h_a, h_1), h_2), h_s)       # H -> u = w_i
        Y[i] = b.gen('u', b.ex_elim(y, r))
        assert Y[i][2][1] is chi(i, VX) and Y[i][2][2] is eq(VX, w(i))
    # the naming sentence
    K = binnum(2 ** (2 ** j))
    assert K is w(j)
    phi = chi(j, X_)
    fwd = b.inst(Y[j], [X_])                          # chi_j(x) -> x = K
    Hx = eq(X_, K)
    yj = 'y%d' % (j - 1)
    body = conj(eq(X_, mul(var(yj), var(yj))), chi(j - 1, var(yj)))
    inst = subst(body, yj, w(j - 1))
    h1 = b.trans_h(b.identity(Hx), b.lift(Hx, b.sym(sq[j - 1])))   # Hx -> x = w'*w'
    h2 = b.lift(Hx, X[j - 1])
    c3 = b.ax_h(Hx, imp(h1[2], imp(h2[2], inst)))
    h3 = b.mp_h(h2, b.mp_h(h1, c3))                   # Hx -> inst
    bwd = b.syllogism(h3, b.ex_intro(yj, body, w(j - 1)))         # Hx -> chi_j(x)
    assert bwd[2] is phi
    both = b.mp(bwd, b.mp(fwd, b.emit(imp(fwd, imp(bwd, conj(fwd, bwd))))))
    b.gen('x', both)
    return b.lines, phi, lem_len, stats


# ------------------------------------------------------------------- run

def report_check(lines, what):
    ok, bad = check(lines)
    if not ok:
        raise SystemExit(f"{what}: line {bad} is not justified: {lines[bad]}")


def mutation_test(trials=40, seed=1):
    """Corrupt one line of a checked proof at random; the checker must
    reject every corrupted proof.  Returns (corruptions tried, accepted)."""
    import random
    rng = random.Random(seed)
    tried = accepted = 0
    for build in (lambda: unary_name(5), lambda: binary_name(4)):
        for _ in range(trials):
            cc.reset()
            lines = list(build()[0])
            i, j = rng.randrange(len(lines)), rng.randrange(len(lines))
            if lines[i] is lines[j]:
                continue
            lines[i] = imp(lines[i], lines[j]) if rng.random() < 0.5 else eq(ONE, TWO)
            tried += 1
            accepted += check(lines)[0]
    return tried, accepted


def main():
    Amax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    Jmax = int(sys.argv[2]) if len(sys.argv) > 2 else 14

    print("Unary target.  phi = (x = bin(2^a)), naming sentence"
          " all x (phi <-> x = (2^a)bar).\n")
    print("| a | k = 2^a | size of phi | proof length | of which lemmas | length / k |")
    print("|---:|---:|---:|---:|---:|---:|")
    last_stats = None
    for a in range(1, Amax + 1):
        cc.reset()
        lines, phi, lem, stats = unary_name(a)
        report_check(lines, f"unary a={a}")
        tot = length(lines)
        k = 2 ** a
        print(f"| {a} | {k:,} | {size(phi)} | {tot:,} | {lem:,} | {tot / k:.1f} |")
        last_stats = stats
    print("\nPer doubling step n -> 2n (unary lemmas C, T, R together):"
          " lines, largest line / n")
    print("  " + ", ".join(f"n={n}: {ln} lines, {mx / n:.1f}" for n, ln, mx in last_stats[-4:]))

    print("\nBinary target.  phi = chi_j(x) ('x is 2 squared j times'),"
          " naming sentence all x (phi <-> x = bin(2^(2^j))).\n")
    print("| j | log2 k = 2^j | size of phi | proof length | of which lemmas | length / log2 k |")
    print("|---:|---:|---:|---:|---:|---:|")
    for j in range(1, Jmax + 1):
        cc.reset()
        lines, phi, lem, stats = binary_name(j)
        report_check(lines, f"binary j={j}")
        tot = length(lines)
        L = 2 ** j
        print(f"| {j} | {L:,} | {size(phi)} | {tot:,} | {lem:,} | {tot / L:.1f} |")
        last_stats = stats
    print("\nPer doubling step n -> 2n (binary lemmas B, A together):"
          " lines, largest line / n")
    print("  " + ", ".join(f"n={n}: {ln} lines, {mx / n:.1f}" for n, ln, mx in last_stats[-4:]))
    print("\nAll proofs checked line by line (H + Q2, PA- with A3).")
    tried, accepted = mutation_test()
    print(f"Checker sanity: {tried} proofs with one corrupted line, {accepted} accepted.")
    assert accepted == 0


if __name__ == '__main__':
    main()
