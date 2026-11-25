#!/usr/bin/env python3
"""
Lemma-style proofs for the toy arithmetics of naming_records.py.

A chain proof (naming_records.py) writes the whole term at every step, and a
subterm that occurs twice is computed twice.  Here a proof is a list of
equations, as in an equational-logic (or Hilbert) proof:

  * for every term u that the evaluation meets, one *lemma*  u = numeral;
  * a lemma is proved by
      - a congruence line   f(a1,...,am) = f(n1,...,nm)   from the lemmas
        ai = ni of the arguments (omitted if every argument is a numeral),
      - one rule-instance line   f(n1,...,nm) = r,
      - the lemma for r, and
      - the conclusion  u = numeral  (transitivity; omitted when the
        rule-instance line already is the conclusion);
    if an erasing rule (x+0, x*0, x^0, 0+x, 0*x) applies to u itself it is
    used first, before the arguments are evaluated.

The length of a line  s = t  is |s| + |t|; the length of a proof is the
sum over its lines.  Two measures:

  tree(s): every lemma is proved afresh each time it is used (no reuse);
  dag(s) : each distinct lemma is proved once and then reused.

tree >= dag always.  The gap is the saving from reuse; it is large exactly
when a term repeats a subterm, which the rule  x^(2y) -> x^y * x^y  does at
every level.
"""
import sys

sys.setrecursionlimit(1_000_000)


class Overflow(Exception):
    pass


class Lemmas:
    def __init__(self, S):
        self.S = S
        self.info = {}   # u -> (own line cost, child lemma terms, numeral)
        self.tree = {}
        self.too_big = set()
        self.budget = None   # when set, lem() raises Overflow once the new lemmas' cost exceeds it

    def lem(self, u):
        """(own, kids, nf) for the lemma u = nf, or None if u has no value."""
        got = self.info.get(u)
        if got is not None:
            return got
        S = self.S
        if S.val[u] is None:
            raise ValueError("term too large")
        if self.budget is not None and self.budget < 0:
            raise Overflow
        if S.is_normal(u):
            res = (0, (), u)
            self.info[u] = res
            return res
        sym, args = S.ops[u]
        size = S.size
        for r in S.root_steps(u):
            if S.is_erasing(u, r):
                nf = self.lem(r)[2]
                own = size[u] + size[r]
                kids = ()
                if not S.is_normal(r):
                    kids = (r,)
                    own += size[u] + size[nf]
                res = (own, kids, nf)
                self._store(u, res)
                return res
        kids = []
        nargs = []
        for a in args:
            na = self.lem(a)[2]
            if na != a:
                kids.append(a)
            nargs.append(na)
        u2 = S.mk(sym, *nargs)
        own = 0
        if u2 != u:
            own += size[u] + size[u2]
        rs = S.root_steps(u2)
        if not rs:                      # u2 is the numeral: congruence line is the conclusion
            res = (own, tuple(kids), u2)
            self._store(u, res)
            return res
        r = rs[0]
        own += size[u2] + size[r]
        nf = self.lem(r)[2]
        if not S.is_normal(r):
            kids.append(r)
        if not (u2 == u and S.is_normal(r)):
            own += size[u] + size[nf]
        res = (own, tuple(kids), nf)
        self._store(u, res)
        return res

    def _store(self, u, res):
        self.info[u] = res
        if self.budget is not None:
            self.budget -= res[0]

    def tree_cost(self, u, cap):
        """Proof length without reuse, or None if above cap."""
        c = self.tree.get(u)
        if c is not None:
            return c if c <= cap else None
        own, kids, _ = self.lem(u)
        tot = own
        for k in kids:
            ck = self.tree_cost(k, cap)
            if ck is None:
                return None
            tot += ck
            if tot > cap:
                return None
        self.tree[u] = tot
        return tot if tot <= cap else None

    def dag_cost(self, u, cap):
        """Proof length with each distinct lemma proved once, or None if above
        cap.  Returns (length, number of lemmas).

        Every lemma that lem() creates while doing this lies in u's closure, so
        if their costs already exceed cap, so does the answer: lem() is stopped
        early (Overflow) instead of computing a huge numeral in full."""
        if u in self.too_big:
            return None
        self.budget = cap
        try:
            self.lem(u)
        except Overflow:
            self.too_big.add(u)
            return None
        finally:
            self.budget = None
        seen = {u}
        stack = [u]
        tot = 0
        while stack:
            v = stack.pop()
            own, kids, _ = self.lem(v)
            tot += own
            if tot > cap:
                return None
            for k in kids:
                if k not in seen:
                    seen.add(k)
                    stack.append(k)
        if self.S.is_normal(u):
            tot = self.S.size[u]   # a numeral names itself: the one line  k = k  (counted once)
        return tot, len(seen)
