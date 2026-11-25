#!/usr/bin/env python3
"""Lemma 11 and Lemma 12a of NAMING-DEPTH.md, written out line by line.

This file fixes one Hilbert system (called H below), gives a checker for
it, and gives the functions that build the derivations used in Lemma 11
(collision) and Lemma 12a:

    Z(d)        0 < bin(d)                          d >= 1
    Inc(a)      bin(a) + 1 = bin(a+1)
    AddC(a,b,0) bin(a) + bin(b) = bin(a+b)          ("Add")
    AddC(a,b,1) (bin(a) + bin(b)) + 1 = bin(a+b+1)  ("Add+")
    Lt(k,k2)    bin(k) < bin(k2)                    k < k2
    Hcol(p,p2)  a contradiction, from two naming proofs for one formula
                and two different numbers            (Lemma 11, 12a(i))
    Explode(p,S) the sentence S, from a proof of a contradiction
                                                     (Lemma 12a(ii))

A proof is a list of formulas and nothing else.  A line is correct when
it is an axiom, or follows from two earlier lines by modus ponens, or
from one earlier line by generalisation.  The checker decides this from
the list alone.  The builders below carry no justifications.

Running the file checks every derivation it builds and measures the
lengths against the bounds claimed in the note.  It checks instances.
It is not a proof that the builders are correct for all inputs, but
every block of lines a builder emits has a shape that does not depend
on the terms plugged into it, which is what the induction in Lemma 12a
uses, and the script asserts the two facts that make the length bound
quadratic: a bounded number of lines per digit, each of size linear in
the numerals.

The system H
------------
Language: 0, 1, +, *, =, <, variables.  Connectives: not, imp, and,
all.  (A iff B abbreviates (A imp B) and (B imp A).)

Logical axiom schemes:
    P1  A -> (B -> A)
    P2  (A -> (B -> C)) -> ((A -> B) -> (A -> C))
    P3  (not A -> not B) -> (B -> A)
    C1  A and B -> A        C2  A and B -> B
    C3  A -> (B -> A and B)
    Q1  all x A -> A[t/x]            t free for x in A
Rules: modus ponens; generalisation (from A infer all x A).
Equality schemes, for all terms s, t, r:
    E1  t = t
    E2  s = t -> t = s
    E3  s = t -> (t = r -> s = r)
    E4  s = t -> s + r = t + r       E5  s = t -> r + s = r + t
    E6  s = t -> s * r = t * r       E7  s = t -> r * s = r * t
    E8  s = t -> (s < r -> t < r)    E9  s = t -> (r < s -> r < t)
(E2 and E3 follow from E1 and the others at a fixed cost.  They are
taken as schemes to keep the blocks short.)

Axioms of PA- that are used, as closed sentences:
    A1  all x y z  (x + y) + z = x + (y + z)
    A2  all x y    x + y = y + x
    A4  all x y    x * y = y * x
    A5  all x y z  x * (y + z) = x * y + x * z
    A6  all x      x + 0 = x
    A7  all x      x * 1 = x
    A8  all x y z  x < y -> (y < z -> x < z)
    A9  all x      not x < x
    A11 all x y z  x < y -> x + z < y + z
    A14 0 < 1
(Numbering after Kaye, Models of Peano Arithmetic, ch. 2.  A8 and A11
are written with nested implications where Kaye has a conjunction.)

The size of a formula is its number of nodes.  The length of a proof is
the sum of the sizes of its lines.
"""

import random
import sys

sys.setrecursionlimit(100000)

# ------------------------------------------------------------------ syntax

# Terms and formulas are nested tuples: ('0',), ('1',), ('v', name),
# ('+', s, t), ('*', s, t), ('=', s, t), ('<', s, t), ('not', A),
# ('imp', A, B), ('and', A, B), ('all', name, A).
#
# Every tuple is built by mk, which keeps one copy of each (hash
# consing).  So two expressions are equal exactly when they are the same
# object, and the code below compares with `is`.  This is only for
# speed.  check() first passes its input through canon(), so it accepts
# any list of nested tuples.

_table = {}
_size_cache = {}


def _key(parts):
    return tuple(p if isinstance(p, str) else id(p) for p in parts)


def mk(*parts):
    key = _key(parts)
    node = _table.get(key)
    if node is None:
        node = parts
        _table[key] = node
    return node


def canon(e):
    """The stored copy of an arbitrary nested tuple."""
    if _table.get(_key(e)) is e:
        return e
    return mk(*[p if isinstance(p, str) else canon(p) for p in e])


ZERO = mk('0')
ONE = mk('1')


def var(x):
    return mk('v', x)


def add(s, t):
    return mk('+', s, t)


def mul(s, t):
    return mk('*', s, t)


TWO = add(ONE, ONE)


def eq(s, t):
    return mk('=', s, t)


def lt(s, t):
    return mk('<', s, t)


def neg(a):
    return mk('not', a)


def imp(a, b):
    return mk('imp', a, b)


def conj(a, b):
    return mk('and', a, b)


def iff(a, b):
    return conj(imp(a, b), imp(b, a))


def forall(x, a):
    return mk('all', x, a)


BOT = neg(eq(ZERO, ZERO))          # the fixed contradiction: not 0 = 0


def binnum(n):
    """bin(0)=0, bin(1)=1, bin(2m)=(1+1)*bin(m), bin(2m+1)=(1+1)*bin(m)+1."""
    if n == 0:
        return ZERO
    if n == 1:
        return ONE
    h = mul(TWO, binnum(n // 2))
    return h if n % 2 == 0 else add(h, ONE)


def unbin(t):
    """Inverse of binnum; None if t is not a binary numeral."""
    if t is ZERO:
        return 0
    if t is ONE:
        return 1
    if t[0] == '*' and t[1] is TWO:
        m = unbin(t[2])
        return None if m is None or m < 1 else 2 * m
    if t[0] == '+' and t[2] is ONE and t[1][0] == '*' and t[1][1] is TWO:
        m = unbin(t[1][2])
        return None if m is None or m < 1 else 2 * m + 1
    return None


def size(e):
    """Number of nodes, cached by object identity."""
    key = id(e)
    hit = _size_cache.get(key)
    if hit is not None:
        return hit
    if e[0] in ('0', '1', 'v'):
        n = 1
    elif e[0] in ('+', '*', '=', '<', 'imp', 'and'):
        n = 1 + size(e[1]) + size(e[2])
    elif e[0] == 'not':
        n = 1 + size(e[1])
    elif e[0] == 'all':
        n = 2 + size(e[2])
    else:
        raise ValueError(e[0])
    _size_cache[key] = n
    return n


def length(lines):
    return sum(size(f) for f in lines)


def term_vars(t, acc):
    if t[0] == 'v':
        acc.add(t[1])
    elif t[0] in ('+', '*'):
        term_vars(t[1], acc)
        term_vars(t[2], acc)
    return acc


def subst_term(t, x, r):
    if t[0] == 'v':
        return r if t[1] == x else t
    if t[0] in ('+', '*'):
        a, b = subst_term(t[1], x, r), subst_term(t[2], x, r)
        return t if (a is t[1] and b is t[2]) else mk(t[0], a, b)
    return t


class Capture(Exception):
    pass


def subst(a, x, r, rvars=None, bound=frozenset()):
    """a[r/x].  Raises Capture when r is not free for x in a."""
    if rvars is None:
        rvars = term_vars(r, set())
    k = a[0]
    if k in ('=', '<'):
        s, t = subst_term(a[1], x, r), subst_term(a[2], x, r)
        if (s is not a[1] or t is not a[2]) and (rvars & bound):
            raise Capture()
        return a if (s is a[1] and t is a[2]) else mk(k, s, t)
    if k == 'not':
        b = subst(a[1], x, r, rvars, bound)
        return a if b is a[1] else mk(k, b)
    if k in ('imp', 'and'):
        b, c = subst(a[1], x, r, rvars, bound), subst(a[2], x, r, rvars, bound)
        return a if (b is a[1] and c is a[2]) else mk(k, b, c)
    if k == 'all':
        if a[1] == x:
            return a
        b = subst(a[2], x, r, rvars, bound | {a[1]})
        return a if b is a[2] else mk(k, a[1], b)
    raise ValueError(k)


def find_witness_term(t, t2, x):
    """Walk terms t and t2 together; return the subterm of t2 standing
    where x stands in t, or None."""
    if t[0] == 'v' and t[1] == x:
        return t2
    if t[0] in ('+', '*') and t2[0] == t[0]:
        return find_witness_term(t[1], t2[1], x) or find_witness_term(t[2], t2[2], x)
    return None


def find_witness(a, a2, x):
    if a[0] != a2[0]:
        return None
    k = a[0]
    if k in ('=', '<'):
        return find_witness_term(a[1], a2[1], x) or find_witness_term(a[2], a2[2], x)
    if k == 'not':
        return find_witness(a[1], a2[1], x)
    if k in ('imp', 'and'):
        return find_witness(a[1], a2[1], x) or find_witness(a[2], a2[2], x)
    if k == 'all':
        if a[1] == x:
            return None
        return find_witness(a[2], a2[2], x)
    return None


# ------------------------------------------------------------------ axioms

def _all3(body):
    return forall('x', forall('y', forall('z', body)))


def _all2(body):
    return forall('x', forall('y', body))


X, Y, Zv = var('x'), var('y'), var('z')

A1 = _all3(eq(add(add(X, Y), Zv), add(X, add(Y, Zv))))
A2 = _all2(eq(add(X, Y), add(Y, X)))
A4 = _all2(eq(mul(X, Y), mul(Y, X)))
A5 = _all3(eq(mul(X, add(Y, Zv)), add(mul(X, Y), mul(X, Zv))))
A6 = forall('x', eq(add(X, ZERO), X))
A7 = forall('x', eq(mul(X, ONE), X))
A8 = _all3(imp(lt(X, Y), imp(lt(Y, Zv), lt(X, Zv))))
A9 = forall('x', neg(lt(X, X)))
A11 = _all3(imp(lt(X, Y), lt(add(X, Zv), add(Y, Zv))))
A14 = lt(ZERO, ONE)

PA_MINUS = [A1, A2, A4, A5, A6, A7, A8, A9, A11, A14]
_PA_IDS = frozenset(id(a) for a in PA_MINUS)

_base_table = dict(_table)


def reset():
    """Forget every expression except the constants and axioms above.
    Called between test cases to bound memory.  Expressions built before
    a reset must not be used after it."""
    _table.clear()
    _table.update(_base_table)
    _size_cache.clear()


def is_logical_axiom(f):
    """Is the (stored) formula f an instance of a scheme of H?"""
    k = f[0]
    if k == '=':                                              # E1
        return f[1] is f[2]
    if k != 'imp':
        return False
    a, b = f[1], f[2]
    # P1  A -> (B -> A)
    if b[0] == 'imp' and b[2] is a:
        return True
    # P2  (A -> (B -> C)) -> ((A -> B) -> (A -> C))
    if (a[0] == 'imp' and a[2][0] == 'imp' and b[0] == 'imp'
            and b[1][0] == 'imp' and b[2][0] == 'imp'):
        A, B, C = a[1], a[2][1], a[2][2]
        if b[1][1] is A and b[1][2] is B and b[2][1] is A and b[2][2] is C:
            return True
    # P3  (not A -> not B) -> (B -> A)
    if (a[0] == 'imp' and a[1][0] == 'not' and a[2][0] == 'not'
            and b[0] == 'imp' and b[1] is a[2][1] and b[2] is a[1][1]):
        return True
    # C1, C2
    if a[0] == 'and' and (b is a[1] or b is a[2]):
        return True
    # C3  A -> (B -> A and B)
    if b[0] == 'imp' and b[2][0] == 'and' and b[2][1] is a and b[2][2] is b[1]:
        return True
    # Q1  all x A -> A[t/x]
    if a[0] == 'all':
        x, body = a[1], a[2]
        t = find_witness(body, b, x)
        try:
            if t is None:
                if b is body:
                    return True
            elif subst(body, x, t) is b:
                return True
        except Capture:
            pass
    # equality schemes with antecedent s = t
    if a[0] == '=':
        s, t = a[1], a[2]
        if b[0] == '=':
            if b[1] is t and b[2] is s:                       # E2
                return True
            l, r = b[1], b[2]
            if l[0] in ('+', '*') and r[0] == l[0]:
                if l[1] is s and r[1] is t and l[2] is r[2]:  # E4, E6
                    return True
                if l[2] is s and r[2] is t and l[1] is r[1]:  # E5, E7
                    return True
        if b[0] == 'imp':
            c, d = b[1], b[2]
            if (c[0] == '=' and d[0] == '=' and c[1] is t
                    and d[1] is s and d[2] is c[2]):          # E3
                return True
            if c[0] == '<' and d[0] == '<':
                if c[1] is s and d[1] is t and c[2] is d[2]:  # E8
                    return True
                if c[2] is s and d[2] is t and c[1] is d[1]:  # E9
                    return True
    return False


def check(lines, extra=()):
    """Is `lines` a proof in H from PA- and the sentences in `extra`?
    Returns (True, None) or (False, index of the first bad line)."""
    extra_ids = frozenset(id(canon(e)) for e in extra)
    seen = set()
    by_consequent = {}
    for n, f in enumerate(lines):
        f = canon(f)
        i = id(f)
        ok = i in seen or i in _PA_IDS or i in extra_ids or is_logical_axiom(f)
        if not ok and i in by_consequent:
            ok = any(a in seen for a in by_consequent[i])     # modus ponens
        if not ok and f[0] == 'all':
            ok = id(f[2]) in seen                             # generalisation
        if not ok:
            return (False, n)
        seen.add(i)
        if f[0] == 'imp':
            by_consequent.setdefault(id(f[2]), []).append(id(f[1]))
    return (True, None)


# ---------------------------------------------------------------- builders

class Builder:
    """Collects lines.  Every method emits a fixed pattern of lines."""

    def __init__(self, lines=()):
        self.lines = list(lines)

    def emit(self, f):
        self.lines.append(f)
        return f

    def mp(self, a, ab):
        assert ab[0] == 'imp' and ab[1] is a
        return self.emit(ab[2])

    def inst(self, axiom, terms):
        """Instantiate the leading quantifiers of a sentence at closed terms."""
        cur = self.emit(axiom)
        for t in terms:
            nxt = subst(cur[2], cur[1], t)
            self.emit(imp(cur, nxt))
            cur = self.emit(nxt)
        return cur

    # equations
    def refl(self, t):
        return self.emit(eq(t, t))

    def sym(self, e):
        return self.mp(e, self.emit(imp(e, eq(e[2], e[1]))))

    def trans(self, e1, e2):
        assert e1[2] is e2[1]
        s, t, r = e1[1], e1[2], e2[2]
        h = self.mp(e1, self.emit(imp(e1, imp(e2, eq(s, r)))))
        return self.mp(e2, h)

    def chain(self, *es):
        cur = es[0]
        for e in es[1:]:
            cur = self.trans(cur, e)
        return cur

    def congL(self, e, r, op):          # s = t  |-  s op r = t op r
        return self.mp(e, self.emit(imp(e, eq(mk(op, e[1], r), mk(op, e[2], r)))))

    def congR(self, e, r, op):          # s = t  |-  r op s = r op t
        return self.mp(e, self.emit(imp(e, eq(mk(op, r, e[1]), mk(op, r, e[2])))))

    # order
    def lt_left(self, e, l):            # s = t, s < r  |-  t < r
        assert l[1] is e[1]
        h = self.mp(e, self.emit(imp(e, imp(l, lt(e[2], l[2])))))
        return self.mp(l, h)

    def lt_right(self, e, l):           # s = t, r < s  |-  r < t
        assert l[2] is e[1]
        h = self.mp(e, self.emit(imp(e, imp(l, lt(l[1], e[2])))))
        return self.mp(l, h)

    def lt_trans(self, l1, l2):
        assert l1[2] is l2[1]
        h = self.inst(A8, [l1[1], l1[2], l2[2]])
        return self.mp(l2, self.mp(l1, h))

    # propositional
    def syllogism(self, ab, bc):        # A -> B, B -> C  |-  A -> C
        A, B, C = ab[1], ab[2], bc[2]
        assert bc[1] is B
        h = self.mp(bc, self.emit(imp(bc, imp(A, bc))))                   # P1
        p2 = self.emit(imp(h, imp(ab, imp(A, C))))                        # P2
        return self.mp(ab, self.mp(h, p2))

    def explode(self, p, notp, target):  # P, not P  |-  target
        assert notp is neg(p)
        h = self.mp(notp, self.emit(imp(notp, imp(neg(target), notp))))   # P1
        g = self.mp(h, self.emit(imp(h, imp(p, target))))                 # P3
        return self.mp(p, g)

    # small arithmetic blocks
    def zero_add(self, t):              # 0 + t = t
        return self.trans(self.inst(A2, [ZERO, t]), self.inst(A6, [t]))

    def dbl(self, s):                   # (1+1) * s = s + s
        e1 = self.inst(A4, [TWO, s])                  # two*s = s*two
        e2 = self.inst(A5, [s, ONE, ONE])             # s*(1+1) = s*1 + s*1
        e3 = self.inst(A7, [s])                       # s*1 = s
        e4 = self.congL(e3, mul(s, ONE), '+')         # s*1 + s*1 = s + s*1
        e5 = self.congR(e3, s, '+')                   # s + s*1 = s + s
        return self.chain(e1, e2, e4, e5)

    def one_one(self):                  # 1 + 1 = (1+1) * 1
        return self.sym(self.inst(A7, [TWO]))

    def factor(self, s, t):             # two*s + two*t = two*(s + t)
        return self.sym(self.inst(A5, [TWO, s, t]))

    # rearranging sums with a bounded number of summands
    @staticmethod
    def _rn(leaves):
        t = leaves[-1]
        for x in reversed(leaves[:-1]):
            t = add(x, t)
        return t

    def _append(self, la, lb):          # rn(la) + rn(lb) = rn(la + lb)
        if len(la) == 1:
            return self.refl(add(la[0], self._rn(lb)))
        x, rest = la[0], la[1:]
        e1 = self.inst(A1, [x, self._rn(rest), self._rn(lb)])
        e2 = self.congR(self._append(rest, lb), x, '+')
        return self.trans(e1, e2)

    def _flat(self, t, leaf):           # t = rn(leaves of t)
        if t[0] != '+' or leaf(t):
            return [t], self.refl(t)
        la, ea = self._flat(t[1], leaf)
        lb, eb = self._flat(t[2], leaf)
        e1 = self.congL(ea, t[2], '+')
        e2 = self.congR(eb, self._rn(la), '+')
        e3 = self._append(la, lb)
        return la + lb, self.chain(e1, e2, e3)

    def _swap(self, l, i):              # rn(l) = rn(l with l[i], l[i+1] exchanged)
        if i > 0:
            return self.congR(self._swap(l[1:], i - 1), l[0], '+')
        if len(l) == 2:
            return self.inst(A2, [l[0], l[1]])
        x, y, rest = l[0], l[1], self._rn(l[2:])
        e1 = self.sym(self.inst(A1, [x, y, rest]))        # x+(y+R) = (x+y)+R
        e2 = self.congL(self.inst(A2, [x, y]), rest, '+')  # = (y+x)+R
        e3 = self.inst(A1, [y, x, rest])                  # = y+(x+R)
        return self.chain(e1, e2, e3)

    def _normal(self, t):
        """t = rn(leaves with every 1 moved to the end)."""
        leaves, e = self._flat(t, lambda u: False)
        changed = True
        while changed:
            changed = False
            for i in range(len(leaves) - 1):
                if leaves[i] is ONE and leaves[i + 1] is not ONE:
                    e = self.trans(e, self._swap(leaves, i))
                    leaves = leaves[:i] + [leaves[i + 1], leaves[i]] + leaves[i + 2:]
                    changed = True
        return leaves, e

    def rearrange(self, lhs, rhs):      # lhs = rhs, both sums of the same summands
        l1, e1 = self._normal(lhs)
        l2, e2 = self._normal(rhs)
        assert len(l1) == len(l2) <= 5 and all(u is v for u, v in zip(l1, l2))
        return self.trans(e1, self.sym(e2))


# per-digit statistics, for the length bound
STATS = {'lines_per_digit': 0, 'size_per_line_over_L': 0.0}


def _note(b, start, numeral_size):
    n = len(b.lines) - start
    STATS['lines_per_digit'] = max(STATS['lines_per_digit'], n)
    worst = max(size(f) for f in b.lines[start:]) if n else 0
    STATS['size_per_line_over_L'] = max(STATS['size_per_line_over_L'],
                                        worst / numeral_size)


def Z(b, d):
    """0 < bin(d), for d >= 1."""
    assert d >= 1
    if d == 1:
        return b.emit(A14)
    m = d // 2
    s = binnum(m)
    h = Z(b, m)                                           # 0 < s
    start = len(b.lines)
    l1 = b.mp(h, b.inst(A11, [ZERO, s, s]))               # 0 + s < s + s
    l2 = b.lt_left(b.zero_add(s), l1)                     # s < s + s
    l3 = b.lt_trans(h, l2)                                # 0 < s + s
    l4 = b.lt_right(b.sym(b.dbl(s)), l3)                  # 0 < two*s
    if d % 2 == 1:
        t = mul(TWO, s)
        l5 = b.mp(b.emit(A14), b.inst(A11, [ZERO, ONE, t]))   # 0 + t < 1 + t
        l6 = b.lt_left(b.zero_add(t), l5)                 # t < 1 + t
        l7 = b.lt_right(b.inst(A2, [ONE, t]), l6)         # t < t + 1
        l4 = b.lt_trans(l4, l7)                           # 0 < t + 1
    _note(b, start, size(binnum(d)))
    return l4


def Inc(b, a):
    """bin(a) + 1 = bin(a+1)."""
    if a == 0:
        return b.zero_add(ONE)
    if a == 1:
        return b.one_one()
    if a % 2 == 0:
        return b.refl(add(binnum(a), ONE))
    m = a // 2
    s = binnum(m)
    e0 = Inc(b, m)                                        # s + 1 = bin(m+1)
    start = len(b.lines)
    S = mul(TWO, s)
    e1 = b.inst(A1, [S, ONE, ONE])                        # (S+1)+1 = S+(1+1)
    e2 = b.congR(b.one_one(), S, '+')                     # = S + two*1
    e3 = b.factor(s, ONE)                                 # = two*(s+1)
    e4 = b.congR(e0, TWO, '*')                            # = two*bin(m+1)
    r = b.chain(e1, e2, e3, e4)
    _note(b, start, size(binnum(a)))
    return r


def AddC(b, x, y, c):
    """c = 0:  bin(x) + bin(y) = bin(x+y).
       c = 1:  (bin(x) + bin(y)) + 1 = bin(x+y+1)."""
    Bx, By = binnum(x), binnum(y)
    if x == 0 or y == 0 or x == 1 or y == 1:
        if x == 0:
            e, other = b.zero_add(By), y                  # 0 + By = By
        elif y == 0:
            e, other = b.inst(A6, [Bx]), x                # Bx + 0 = Bx
        elif x == 1:
            e = b.trans(b.inst(A2, [ONE, By]), Inc(b, y))  # 1 + By = bin(y+1)
            other = y + 1
        else:
            e, other = Inc(b, x), x + 1                   # Bx + 1 = bin(x+1)
        if c == 0:
            return e
        return b.trans(b.congL(e, ONE, '+'), Inc(b, other))
    x2, xb = divmod(x, 2)
    y2, yb = divmod(y, 2)
    s, t = binnum(x2), binnum(y2)
    S, T = mul(TWO, s), mul(TWO, t)
    total = xb + yb + c
    lhs = add(Bx, By) if c == 0 else add(add(Bx, By), ONE)
    sub = AddC(b, x2, y2, 1 if total >= 2 else 0)
    start = len(b.lines)
    if total <= 1:
        # sub: s + t = r.   S + T = two*(s+t) = two*r
        f = b.trans(b.factor(s, t), b.congR(sub, TWO, '*'))
        if total == 0:
            res = f
        else:
            g = b.congL(f, ONE, '+')                      # (S+T)+1 = two*r + 1
            res = b.trans(b.rearrange(lhs, add(add(S, T), ONE)), g)
    else:
        # sub: (s + t) + 1 = r.   (S+T) + (1+1) = two*((s+t)+1) = two*r
        st = add(s, t)
        e1 = b.congR(b.one_one(), add(S, T), '+')         # (S+T)+(1+1) = (S+T)+two*1
        e2 = b.congL(b.factor(s, t), mul(TWO, ONE), '+')  # = two*(s+t) + two*1
        e3 = b.factor(st, ONE)                            # = two*((s+t)+1)
        e4 = b.congR(sub, TWO, '*')                       # = two*r
        f = b.chain(e1, e2, e3, e4)
        mid = add(add(S, T), TWO)
        if total == 2:
            res = b.trans(b.rearrange(lhs, mid), f)
        else:
            g = b.congL(f, ONE, '+')
            res = b.trans(b.rearrange(lhs, add(mid, ONE)), g)
    _note(b, start, size(Bx) + size(By))
    return res


def Lt(b, k, k2):
    """bin(k) < bin(k2), for k < k2."""
    assert k < k2
    d = k2 - k
    K, D = binnum(k), binnum(d)
    h = Z(b, d)                                           # 0 < D
    l1 = b.mp(h, b.inst(A11, [ZERO, D, K]))               # 0 + K < D + K
    l2 = b.lt_left(b.zero_add(K), l1)                     # K < D + K
    return b.lt_right(AddC(b, d, k, 0), l2)               # K < bin(k2)


def naming_sentence(phi, x, k):
    """all x (phi(x) iff x = bin(k))."""
    return forall(x, iff(phi, eq(var(x), binnum(k))))


def parse_naming_sentence(f):
    """Return (x, phi, k), or None."""
    if f[0] != 'all' or f[2][0] != 'and':
        return None
    x, (_, l, r) = f[1], f[2]
    if l[0] != 'imp' or r[0] != 'imp' or l[1] is not r[2] or l[2] is not r[1]:
        return None
    phi, a = l[1], l[2]
    if a[0] != '=' or a[1] is not var(x):
        return None
    k = unbin(a[2])
    return None if k is None else (x, phi, k)


def Hcol(p, p2):
    """Lemma 11.  p and p2 are proofs whose last lines are naming
    sentences for the same formula and two different numbers.  Returns a
    proof whose last line is BOT."""
    N, N2 = p[-1], p2[-1]
    x, phi, k = parse_naming_sentence(N)
    x2, phi2, k2 = parse_naming_sentence(N2)
    assert x == x2 and phi is phi2 and k != k2
    b = Builder(list(p) + list(p2))
    K, K2 = binnum(k), binnum(k2)
    A, B = eq(var(x), K), eq(var(x), K2)
    # step 1: all x (A iff B), without looking inside phi
    body = b.mp(N, b.emit(imp(N, N[2])))                  # Q1 at the variable x
    body2 = b.mp(N2, b.emit(imp(N2, N2[2])))
    phi_a = b.mp(body, b.emit(imp(body, body[1])))        # phi -> A
    a_phi = b.mp(body, b.emit(imp(body, body[2])))        # A -> phi
    phi_b = b.mp(body2, b.emit(imp(body2, body2[1])))     # phi -> B
    b_phi = b.mp(body2, b.emit(imp(body2, body2[2])))     # B -> phi
    ab = b.syllogism(a_phi, phi_b)                        # A -> B
    ba = b.syllogism(b_phi, phi_a)                        # B -> A
    both = b.mp(ba, b.mp(ab, b.emit(imp(ab, imp(ba, conj(ab, ba))))))
    G = b.emit(forall(x, both))                           # generalisation
    # step 2: bin(k) = bin(k2)
    inst = subst(both, x, K)
    b.emit(imp(G, inst))
    b.emit(inst)
    fwd = b.mp(inst, b.emit(imp(inst, inst[1])))          # K = K -> K = K2
    E = b.mp(b.refl(K), fwd)                              # K = K2
    # step 3: bin(k2) < bin(k2)
    if k < k2:
        l = Lt(b, k, k2)                                  # K < K2
        bad = b.lt_left(E, l)                             # K2 < K2   (E8)
    else:
        l = Lt(b, k2, k)                                  # K2 < K
        bad = b.lt_right(E, l)                            # K2 < K2   (E9)
    irr = b.inst(A9, [K2])                                # not K2 < K2
    # step 4
    b.explode(bad, irr, BOT)
    return b.lines


def Explode(p, sentence):
    """Lemma 12a(ii).  p is a proof whose last line is BOT.  Returns a
    proof of `sentence`."""
    assert p[-1] is BOT
    b = Builder(p)
    b.explode(b.refl(ZERO), BOT, sentence)
    return b.lines


def Name(k, x='x'):
    """A PA- proof that the formula x = bin(k) names k."""
    b = Builder()
    A = eq(var(x), binnum(k))
    aa = imp(A, A)
    h1 = b.emit(imp(A, imp(aa, A)))                       # P1
    h2 = b.mp(h1, b.emit(imp(h1, imp(imp(A, aa), aa))))   # P2
    self_imp = b.mp(b.emit(imp(A, aa)), h2)               # A -> A
    both = b.mp(self_imp, b.mp(self_imp,
                               b.emit(imp(self_imp, imp(self_imp, conj(self_imp, self_imp))))))
    b.emit(forall(x, both))
    return b.lines


# ------------------------------------------------------------------- tests

def random_formula(rng, depth, x):
    """A formula with free variable x, of arbitrary shape."""
    def term(d):
        if d == 0 or rng.random() < 0.3:
            return rng.choice([ZERO, ONE, var(x), var('u'), var('w')])
        return mk(rng.choice('+*'), term(d - 1), term(d - 1))

    def form(d):
        if d == 0 or rng.random() < 0.2:
            return mk(rng.choice('=<'), term(2), term(2))
        r = rng.random()
        if r < 0.25:
            return neg(form(d - 1))
        if r < 0.5:
            return imp(form(d - 1), form(d - 1))
        if r < 0.75:
            return conj(form(d - 1), form(d - 1))
        return forall(rng.choice(['u', 'w', 'x']), form(d - 1))
    return form(depth)


def must(ok, what):
    if not ok:
        raise AssertionError(what)


def checker_self_tests():
    """The checker must reject wrong lines."""
    good = Name(5)
    must(check(good)[0], 'Name(5)')
    must(not check(good[1:])[0], 'modus ponens without its premise')
    must(not check([eq(ZERO, ONE)])[0], '0 = 1 is not an axiom')
    must(not check([lt(ONE, ZERO)])[0], '1 < 0 is not an axiom')
    must(not check([forall('x', eq(var('x'), ZERO))])[0], 'generalisation of nothing')
    # Q1 with capture: all x all y (x < y), instantiated at y
    f = forall('x', forall('y', lt(var('x'), var('y'))))
    captured = imp(f, forall('y', lt(var('y'), var('y'))))
    must(not check([captured])[0], 'Q1 must refuse capture')
    fine = imp(f, forall('y', lt(ONE, var('y'))))
    must(check([fine])[0], 'Q1 at a closed term')
    # Q1 with two different witnesses
    g = forall('x', eq(var('x'), var('x')))
    must(not check([imp(g, eq(ZERO, ONE))])[0], 'Q1 needs one witness')
    must(check([imp(g, eq(TWO, TWO))])[0], 'Q1 with one witness')
    # misapplied schemes
    e = eq(ZERO, ONE)
    must(not check([imp(e, eq(add(ZERO, ONE), add(ONE, ZERO)))])[0], 'E4 misapplied')
    must(not check([imp(e, imp(lt(ZERO, ONE), lt(ONE, ZERO)))])[0], 'E8 misapplied')
    must(not check([imp(neg(e), e)])[0], 'not A -> A')
    must(not check([imp(imp(e, neg(e)), imp(neg(e), e))])[0], 'P3 misapplied')
    # the checker accepts tuples it has not seen before
    raw = [('imp', ('=', ('0',), ('1',)), ('imp', ('<', ('1',), ('0',)), ('=', ('0',), ('1',))))]
    must(check(raw)[0], 'P1 from raw tuples')
    # the arithmetic of PA- alone gives no contradiction here
    b = Builder()
    Lt(b, 3, 10)
    must(check(b.lines)[0], 'Lt(3,10)')
    must(all(f is not BOT for f in b.lines), 'no contradiction in PA-')
    # changing one numeral in a correct derivation breaks it
    b = Builder()
    AddC(b, 5, 6, 0)
    wrong = list(b.lines)
    wrong[-1] = eq(add(binnum(5), binnum(6)), binnum(12))
    must(not check(wrong)[0], '5 + 6 = 12 must not check')


def bits(n):
    return max(1, n.bit_length())


def run(quick=False):
    rng = random.Random(20261124)
    checker_self_tests()
    print('checker self-tests: passed')

    # 1. arithmetic blocks: all small pairs, random large ones, carry chains
    count = 0
    worst = {'Z': 0.0, 'Inc': 0.0, 'Add': 0.0, 'Add+': 0.0, 'Lt': 0.0}
    small = 24 if quick else 70
    pairs = [(a, c) for a in range(small) for c in range(small)]
    for _ in range(30 if quick else 150):
        L = rng.choice([8, 16, 32, 64, 96, 128])
        pairs.append((rng.getrandbits(rng.randint(1, L)), rng.getrandbits(rng.randint(1, L))))
    for L in ([8, 33] if quick else [8, 33, 64, 127, 200]):
        pairs += [(2 ** L - 1, 1), (2 ** L - 1, 2 ** L - 1), (2 ** L, 2 ** L - 1), (1, 2 ** L - 1)]
    for a, c in pairs:
        reset()
        L = max(bits(a), bits(c))
        for carry in (0, 1):
            b = Builder()
            last = AddC(b, a, c, carry)
            lhs = add(binnum(a), binnum(c))
            want = eq(lhs if carry == 0 else add(lhs, ONE), binnum(a + c + carry))
            must(last is want and b.lines[-1] is want, ('AddC last line', a, c, carry))
            must(check(b.lines)[0], ('AddC', a, c, carry))
            key = 'Add' if carry == 0 else 'Add+'
            worst[key] = max(worst[key], length(b.lines) / L ** 2)
            count += 1
        if a != c:
            lo, hi = min(a, c), max(a, c)
            b = Builder()
            last = Lt(b, lo, hi)
            must(last is lt(binnum(lo), binnum(hi)) and b.lines[-1] is last, ('Lt last line', lo, hi))
            must(check(b.lines)[0], ('Lt', lo, hi))
            worst['Lt'] = max(worst['Lt'], length(b.lines) / L ** 2)
            count += 1
        if a >= 1:
            b = Builder()
            last = Z(b, a)
            must(last is lt(ZERO, binnum(a)) and b.lines[-1] is last, ('Z last line', a))
            must(check(b.lines)[0], ('Z', a))
            worst['Z'] = max(worst['Z'], length(b.lines) / bits(a) ** 2)
            count += 1
        b = Builder()
        last = Inc(b, a)
        must(last is eq(add(binnum(a), ONE), binnum(a + 1)) and b.lines[-1] is last, ('Inc last line', a))
        must(check(b.lines)[0], ('Inc', a))
        worst['Inc'] = max(worst['Inc'], length(b.lines) / bits(a) ** 2)
        count += 1
    print(f'arithmetic derivations checked: {count}')
    print('  worst length / L^2 (L = number of binary digits):')
    for key, v in worst.items():
        print(f'    {key:5s} {v:8.1f}')
    print(f"  most lines added per digit: {STATS['lines_per_digit']}")
    print(f"  largest line size / size of the numerals: {STATS['size_per_line_over_L']:.2f}")
    must(STATS['lines_per_digit'] <= LINES_PER_DIGIT, 'lines per digit')
    must(STATS['size_per_line_over_L'] <= SIZE_PER_LINE, 'line size')

    # 2. Lemma 11: collisions
    count = 0
    worst_ratio = 0.0          # |H| / ell^2
    worst_c2 = 0.0             # (added - C1 * (|N| + |N2|)) / (L + 1)^2
    cases = []
    lim = 10 if quick else 28
    for k in range(lim):
        for k2 in range(lim):
            if k != k2:
                cases.append((k, k2, False))
    for _ in range(30 if quick else 200):
        L = rng.choice([4, 8, 16, 32, 64, 128])
        k, k2 = rng.getrandbits(L), rng.getrandbits(L)
        if k != k2:
            cases.append((k, k2, True))
    for k, k2, arbitrary in cases:
        reset()
        if not arbitrary:
            # the formula x = bin(k), named honestly by p, and one false axiom
            phi = eq(var('x'), binnum(k))
            p = Name(k)
            must(p[-1] is naming_sentence(phi, 'x', k), 'Name last line')
            must(check(p)[0], 'Name is a PA- proof')
            N2 = naming_sentence(phi, 'x', k2)
            p2, extra = [N2], [N2]
        else:
            # an arbitrary formula; both naming sentences are axioms of U
            phi = random_formula(rng, rng.randint(0, 7), 'x')
            N, N2 = naming_sentence(phi, 'x', k), naming_sentence(phi, 'x', k2)
            p, p2, extra = [N], [N2], [N, N2]
        must(check(p, extra)[0] and check(p2, extra)[0], 'premises')
        h = Hcol(p, p2)
        must(h[-1] is BOT, 'Hcol last line')
        ok, where = check(h, extra)
        must(ok, ('Hcol', k, k2, where))
        must(not check(h)[0], 'Hcol must need the extra axioms')
        ell = max(length(p), length(p2))
        added = length(h) - length(p) - length(p2)
        nn = size(p[-1]) + size(p2[-1])
        L = max(bits(k), bits(k2))
        worst_ratio = max(worst_ratio, length(h) / ell ** 2)
        worst_c2 = max(worst_c2, (added - C1 * nn) / (L + 1) ** 2)
        must(added <= C1 * nn + C2 * (L + 1) ** 2, ('two-term bound', k, k2, nn, L, added))
        must(length(h) <= C * ell ** 2, ('quadratic bound', k, k2))
        count += 1
    print(f'collision derivations (Lemma 11) checked: {count}')
    print(f'  worst |H(p,p2)| / max(|p|,|p2|)^2 : {worst_ratio:.2f}   (asserted <= {C})')
    print(f'  added length <= {C1}*(|N|+|N2|) + {C2}*(L+1)^2 in every case '
          f'(worst second coefficient {worst_c2:.0f})')

    # 3. Lemma 12a(ii): from a contradiction to two naming proofs
    reset()
    phi0 = eq(var('x'), ZERO)
    N, N2 = naming_sentence(phi0, 'x', 3), naming_sentence(phi0, 'x', 4)
    extra = [N, N2]
    h = Hcol([N], [N2])
    s0, s1 = naming_sentence(phi0, 'x', 0), naming_sentence(phi0, 'x', 1)
    q0, q1 = Explode(h, s0), Explode(h, s1)
    must(check(q0, extra)[0] and check(q1, extra)[0], 'Explode')
    must(q0[-1] is s0 and q1[-1] is s1, 'Explode last lines')
    c_ii = max(length(q0), length(q1)) - length(h)
    print(f'Lemma 12a(ii): a contradiction of length m gives two naming proofs of length m + {c_ii}')
    h2 = Hcol(q0, q1)
    must(check(h2, extra)[0] and h2[-1] is BOT, 'round trip')
    print('round trip (contradiction -> two names -> contradiction): checked')
    print('all checks passed')


# Constants asserted by run().  They were read off a first run and then
# fixed.  LINES_PER_DIGIT bounds the lines a builder adds per binary
# digit.  SIZE_PER_LINE bounds the size of a line divided by the size of
# the numerals in play.  C1, C2 and C are the constants of Lemma 11.
LINES_PER_DIGIT = 300
SIZE_PER_LINE = 12
C1 = 40
C2 = 3000
C = 30

if __name__ == '__main__':
    run(quick='--quick' in sys.argv)
