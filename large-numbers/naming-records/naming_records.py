#!/usr/bin/env python3
"""
Naming records in two tiny equational arithmetics.

A *name* for k is a closed term s whose value is k.  A *proof* that s names k
is a rewriting chain  s = t0 -> t1 -> ... -> tm = numeral(k), each step one
application of a defining equation (left to right) inside a context.  The
proof's length is the number of symbols in the chain, sum |t_i|, the analogue
of |pi| in PROOF-BUDGETS-AND-COMPLEXITY.md (the last line holds the numeral,
so that note's Proposition 1 cap applies).

Main measure: the *evaluation proof*, the chain produced by call-by-value
(leftmost-innermost) rewriting, except that a root rule which throws an
argument away (x+0, x*0, x^0, 0+x, 0*x) fires before that argument is
evaluated.  This is a fixed, exactly computable proof for every name.
For small names the script also runs an exhaustive A* search for the
shortest chain in any rewriting order, to measure how much the fixed
strategy loses (astar_cost; chain_cost is a slower full search used only to
validate A*).

  record(n, t) = largest k named by a term of size <= n with proof <= t
  K(k)         = least size of a term with value k (no proof charge)
  D(k)         = least  size(s) + log2(proof length of s)  over names s of k

System U (unary):  0, S, +, *, ^  with
    x+0 -> x      x+Sy -> S(x+y)
    x*0 -> 0      x*Sy -> x*y + x
    x^0 -> S0     x^Sy -> x^y * x
  numerals S^k 0, size k+1.

System B (binary): constructors 0, D0, D1 (D0 x = 2x, D1 x = 2x+1),
operations S, +, *, ^ with
    D0 0 -> 0
    S0 -> D1 0            S(D0 x) -> D1 x          S(D1 x) -> D0(S x)
    x+0 -> x   0+x -> x   D0x+D0y -> D0(x+y)       D0x+D1y -> D1(x+y)
                          D1x+D0y -> D1(x+y)       D1x+D1y -> D0(S(x+y))
    x*0 -> 0   0*x -> 0   D0x*y -> D0(x*y)         D1x*y -> D0(x*y)+y
    x^0 -> D1 0           x^(D0 y) -> x^y * x^y    x^(D1 y) -> (x^y * x^y)*x
  numerals = binary digits, least significant outermost, no leading zero;
  size = bits + 1.

Usage:  python3 naming_records.py SYSTEM NMAX CAP [EXACT_N EXACT_CAP]
  e.g.  python3 naming_records.py U 12 10000000 8 500
        python3 naming_records.py B 10 10000000 6 200
Writes out_<SYSTEM>.json: one row per name of size <= NMAX whose evaluation
proof is <= CAP (size, value, proof length, steps, term), plus min_cost (the
any-order shortest proof) for names of size <= EXACT_N with evaluation proof
<= EXACT_CAP.  Values above 2^256 are dropped (their proofs exceed any CAP
used here).  Then run analyse.py SYSTEM for the Markdown tables.
"""
import json
import math
import sys

sys.setrecursionlimit(1_000_000)

INF = float("inf")
NODE_LIMIT = 50_000


class System:
    """Hash-consed terms: a term is an int id; ops[id] = (symbol, child ids)."""

    def __init__(self, name, cap):
        self.name = name
        self.cap = cap
        self.ops = []          # id -> (sym, args)
        self.table = {}        # (sym, args) -> id
        self.size = []         # id -> number of nodes
        self.val = []          # id -> value, or None if > VALCAP
        self.cost = {}         # id -> exact shortest chain length (<= cap) or INF
        self.steps = {}        # id -> steps of that shortest chain
        self.early_erase = True
        self.li = {}           # id -> leftmost-innermost (cost, steps, nf) or None
        self.zero = self.mk("0")

    def mk(self, sym, *args):
        key = (sym, args)
        i = self.table.get(key)
        if i is not None:
            return i
        i = len(self.ops)
        self.ops.append(key)
        self.table[key] = i
        self.size.append(1 + sum(self.size[a] for a in args))
        self.val.append(self.evaluate(sym, [self.val[a] for a in args]))
        return i

    # values above VALCAP are stored as None ("too big to matter")
    VALCAP = 2 ** 256

    def evaluate(self, sym, vs):
        if any(v is None for v in vs):
            # x*0, 0*x, x^0, 0+... can still be small, handled conservatively
            if sym in "*" and 0 in vs:
                return 0
            if sym == "^" and vs[1] == 0:
                return 1
            return None
        r = self.apply(sym, vs)
        return r if r is not None and r <= self.VALCAP else None

    def apply(self, sym, vs):
        if sym == "0":
            return 0
        if sym == "S":
            return vs[0] + 1
        if sym == "D0":
            return 2 * vs[0]
        if sym == "D1":
            return 2 * vs[0] + 1
        if sym == "+":
            return vs[0] + vs[1]
        if sym == "*":
            return vs[0] * vs[1]
        if sym == "^":
            a, b = vs
            if a > 1 and b * math.log2(a) > self.VALCAP.bit_length():
                return None
            return a ** b
        raise ValueError(sym)

    # --- rewriting -------------------------------------------------------
    def root_steps(self, t):
        """All one-step root rewrites of t."""
        raise NotImplementedError

    def successors(self, t):
        out = list(self.root_steps(t))
        sym, args = self.ops[t]
        for i, a in enumerate(args):
            for a2 in self.successors_cached(a):
                new = list(args)
                new[i] = a2
                out.append(self.mk(sym, *new))
        return out

    def successors_cached(self, t):
        c = self._succ.get(t)
        if c is None:
            c = self.successors(t)
            self._succ[t] = c
        return c

    _succ = None

    def numeral_size(self, k):
        raise NotImplementedError

    def lower_bound(self, t):
        v = self.val[t]
        if v is None:
            return INF
        return self.size[t] + (0 if self.is_normal(t) else self.numeral_size(v))

    def is_normal(self, t):
        raise NotImplementedError

    def chain_cost(self, t):
        """Exact min sum of sizes over rewriting chains t ->* numeral, if <= cap."""
        c = self.cost.get(t)
        if c is not None:
            return c
        if self.lower_bound(t) > self.cap:
            self.cost[t] = INF
            self.steps[t] = INF
            return INF
        if self.is_normal(t):
            self.cost[t] = self.size[t]
            self.steps[t] = 0
            return self.size[t]
        best, best_steps = INF, INF
        st = self.size[t]
        for u in self.successors_cached(t):
            if st + self.lower_bound(u) > self.cap:
                continue
            cu = self.chain_cost(u)
            if st + cu < best or (st + cu == best and self.steps[u] + 1 < best_steps):
                best, best_steps = st + cu, self.steps[u] + 1
        if best > self.cap:
            best, best_steps = INF, INF
        self.cost[t] = best
        self.steps[t] = best_steps
        return best

    def li_cost(self, t):
        """Cost of the leftmost-innermost (call-by-value) chain t ->* numeral.

        Returns (sum of sizes, number of steps, numeral id), or None if the
        sum exceeds cap.  Compositional: reduce the arguments left to right
        inside their context, then fire the (unique) root rule and recurse.
        """
        r = self.li.get(t)
        if r is not None or t in self.li:
            return r
        res = self._li(t)
        self.li[t] = res
        return res

    def _li(self, t):
        if self.lower_bound(t) > self.cap:
            return None
        sym, args = self.ops[t]
        cur = list(args)
        total = 0
        steps = 0
        for i in range(len(args) + 1):
            # Fire an erasing root rule (x+0, x*0, x^0, 0+x, 0*x) as
            # soon as one applies, before evaluating arguments it would throw
            # away.  An erasing rule can only become enabled when an argument
            # has just reached 0, so checking before each argument suffices.
            if self.early_erase:
                here = self.mk(sym, *cur)
                for r in self.root_steps(here):
                    if self.is_erasing(here, r):
                        rr = self.li_cost(r)
                        if rr is None:
                            return None
                        total += self.size[here] + rr[0]
                        if total > self.cap:
                            return None
                        return (total, steps + 1 + rr[1], rr[2])
            if i == len(args):
                break
            a = cur[i]
            ra = self.li_cost(a)
            if ra is None:
                return None
            ca, sa, na = ra
            if sa:
                other = 1 + sum(self.size[cur[j]] for j in range(len(cur)) if j != i)
                total += (ca - self.size[na]) + sa * other
                steps += sa
                cur[i] = na
                if total > self.cap:
                    return None
        t2 = self.mk(sym, *cur)
        total += self.size[t2]
        rs = self.root_steps(t2)
        if not rs:
            return (total, steps, t2) if total <= self.cap else None
        rr = self.li_cost(rs[0])
        if rr is None or total + rr[0] > self.cap:
            return None
        return (total + rr[0], steps + 1 + rr[1], rr[2])

    def astar_cost(self, t, node_limit=200_000):
        """Exact min over all rewriting chains t ->* numeral of the sum of
        sizes (A* with the admissible bound size + numeral size).  Returns
        (cost, steps) or None if the minimum exceeds cap.  Raises
        OverflowError if more than node_limit states are expanded."""
        import heapq
        if self.lower_bound(t) > self.cap:
            return None
        ub = self.li_cost(t)
        best = ub[0] if ub else self.cap
        best_steps = ub[1] if ub else None
        # g = sum of sizes of terms strictly before the current one
        g0 = {t: 0}
        heap = [(self.lower_bound(t), 0, 0, t)]
        expanded = 0
        while heap:
            f, g, k, u = heapq.heappop(heap)
            if f > best or (f == best and best_steps is not None):
                break
            if g0.get(u, INF) < g:
                continue
            if self.is_normal(u):
                best, best_steps = g + self.size[u], k
                break
            expanded += 1
            if expanded > node_limit:
                raise OverflowError
            g2 = g + self.size[u]
            for v in self.successors_nocache(u):
                h = self.lower_bound(v)
                if g2 + h > best:
                    continue
                if g0.get(v, INF) <= g2:
                    continue
                g0[v] = g2
                heapq.heappush(heap, (g2 + h, g2, k + 1, v))
        if best_steps is None:
            return None
        return (best, best_steps)

    def successors_nocache(self, t):
        out = list(self.root_steps(t))
        sym, args = self.ops[t]
        for i, a in enumerate(args):
            for a2 in self.successors_nocache(a):
                new = list(args)
                new[i] = a2
                out.append(self.mk(sym, *new))
        return out

    def is_erasing(self, t, r):
        """A root step t -> r is erasing if it drops an argument: the result
        is one of t's arguments (x+0 -> x, 0+x -> x) or a constant
        (x*0 -> 0, 0*x -> 0, x^0 -> 1).  Each needs an argument that is
        literally 0, which is a normal form."""
        sym, args = self.ops[t]
        return sym in "+*^" and (r in args or self.size[r] <= 2)

    # --- enumeration -----------------------------------------------------
    def enumerate(self, nmax):
        by_size = {1: [self.mk(c) for c in self.nullary]}
        for n in range(2, nmax + 1):
            cur = []
            for u in self.unary:
                for a in by_size[n - 1]:
                    cur.append(self.mk(u, a))
            for b in self.binary:
                for i in range(1, n - 1):
                    for x in by_size[i]:
                        for y in by_size[n - 1 - i]:
                            cur.append(self.mk(b, x, y))
            by_size[n] = cur
        return by_size


class Unary(System):
    nullary = ["0"]
    unary = ["S"]
    binary = ["+", "*", "^"]

    def __init__(self, cap):
        super().__init__("U", cap)
        self._succ = {}

    def numeral_size(self, k):
        return k + 1

    def is_normal(self, t):
        sym, args = self.ops[t]
        while sym == "S":
            sym, args = self.ops[args[0]]
        return sym == "0"

    def root_steps(self, t):
        sym, args = self.ops[t]
        if sym not in "+*^":
            return []
        x, y = args
        ys, yargs = self.ops[y]
        if ys == "0":
            if sym == "+":
                return [x]
            if sym == "*":
                return [self.zero]
            return [self.mk("S", self.zero)]
        if ys == "S":
            (y1,) = yargs
            if sym == "+":
                return [self.mk("S", self.mk("+", x, y1))]
            if sym == "*":
                return [self.mk("+", self.mk("*", x, y1), x)]
            return [self.mk("*", self.mk("^", x, y1), x)]
        return []


class Binary(System):
    nullary = ["0"]
    unary = ["D0", "D1", "S"]
    binary = ["+", "*", "^"]

    def __init__(self, cap):
        super().__init__("B", cap)
        self._succ = {}

    def numeral_size(self, k):
        return k.bit_length() + 1

    def is_normal(self, t):
        sym, args = self.ops[t]
        while sym in ("D0", "D1"):
            if sym == "D0" and self.ops[args[0]][0] == "0":
                return False
            sym, args = self.ops[args[0]]
        return sym == "0"

    def root_steps(self, t):
        sym, args = self.ops[t]
        z = self.zero
        mk = self.mk
        out = []
        if sym == "D0":
            if self.ops[args[0]][0] == "0":
                out.append(z)
            return out
        if sym == "S":
            (x,) = args
            xs, xa = self.ops[x]
            if xs == "0":
                out.append(mk("D1", z))
            elif xs == "D0":
                out.append(mk("D1", xa[0]))
            elif xs == "D1":
                out.append(mk("D0", mk("S", xa[0])))
            return out
        if sym not in "+*^":
            return out
        x, y = args
        xs, xa = self.ops[x]
        ys, ya = self.ops[y]
        if sym == "+":
            if ys == "0":
                out.append(x)
            if xs == "0":
                out.append(y)
            if xs in ("D0", "D1") and ys in ("D0", "D1"):
                s = mk("+", xa[0], ya[0])
                if xs == "D0" and ys == "D0":
                    out.append(mk("D0", s))
                elif xs == "D1" and ys == "D1":
                    out.append(mk("D0", mk("S", s)))
                else:
                    out.append(mk("D1", s))
        elif sym == "*":
            if ys == "0" or xs == "0":
                out.append(z)
            if xs == "D0":
                out.append(mk("D0", mk("*", xa[0], y)))
            elif xs == "D1":
                out.append(mk("+", mk("D0", mk("*", xa[0], y)), y))
        else:  # ^
            if ys == "0":
                out.append(mk("D1", z))
            elif ys in ("D0", "D1"):
                p = mk("^", x, ya[0])
                sq = mk("*", p, p)
                out.append(sq if ys == "D0" else mk("*", sq, x))
        return out


def show(sysm, t):
    sym, args = sysm.ops[t]
    if not args:
        return sym
    if len(args) == 1:
        return f"{sym}({show(sysm, args[0])})" if sym != "S" else "S" + show(sysm, args[0])
    a, b = (show(sysm, x) for x in args)
    return f"({a}{sym}{b})"


def pretty(sysm, t):
    """Human reading: numeral subterms shown as decimals, e.g. (D0(D1(D1(0)))^D1(D1(0))) -> 6^3."""
    if sysm.is_normal(t):
        return str(sysm.val[t])
    sym, args = sysm.ops[t]
    if len(args) == 1:
        inner = pretty(sysm, args[0])
        return f"{sym}({inner})"
    a, b = (pretty(sysm, x) for x in args)
    wrap = lambda s, x: s if sysm.is_normal(x) or len(sysm.ops[x][1]) == 1 else f"({s})"
    return f"{wrap(a, args[0])}{sym}{wrap(b, args[1])}"


def main():
    which, nmax, cap = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    exact_n = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    exact_cap = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    S = Unary(cap) if which == "U" else Binary(cap)
    by_size = S.enumerate(nmax)
    rows = []
    for n in range(1, nmax + 1):
        for t in by_size[n]:
            r = S.li_cost(t)
            if r is None:
                continue
            row = {"size": n, "value": S.val[t], "cost": r[0], "steps": r[1],
                   "term": show(S, t), "read": pretty(S, t)}
            if n <= exact_n and r[0] <= exact_cap:
                # shortest chain in any rewriting order (A*), for comparison
                S.cap = exact_cap
                try:
                    a = S.astar_cost(t, NODE_LIMIT)
                    row["min_cost"] = a[0] if a else None
                except OverflowError:
                    row["min_cost"] = "limit"
                S.cap = cap
            rows.append(row)
        print(f"size {n}: {len(by_size[n])} terms, {len(S.ops)} interned",
              file=sys.stderr, flush=True)
    with open(f"out_{which}.json", "w") as f:
        json.dump({"system": which, "nmax": nmax, "cap": cap, "exact_n": exact_n,
                   "exact_cap": exact_cap, "rows": rows}, f)


if __name__ == "__main__":
    main()
