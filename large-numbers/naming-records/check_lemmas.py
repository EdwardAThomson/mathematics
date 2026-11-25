"""Independent check of lemmas.py: build the lemma proof of a name as an
explicit list of equations, check every line is justified, and compare its
total length with dag_cost.

Line kinds:  rule   f(n..) = r   (one root rewrite rule instance)
             cong   f(a..) = f(b..)   (each ai = bi is an earlier line, or ai is bi)
             trans  s = u   from earlier lines s = v and v = u (chains of them)
"""
import random
from naming_records import Unary, Binary
from lemmas import Lemmas


def build(S, L, s):
    lines = []          # (lhs, rhs, kind)
    proved = {}         # lhs -> nf  for lemma conclusions
    have = set()        # all proved equations (lhs, rhs)

    def add(l, r, kind):
        lines.append((l, r, kind))
        have.add((l, r))

    def prove(u):
        if u in proved or S.is_normal(u):
            return
        own, kids, nf = L.lem(u)
        sym, args = S.ops[u]
        for r in S.root_steps(u):
            if S.is_erasing(u, r):
                add(u, r, "rule")
                if not S.is_normal(r):
                    prove(r)
                    add(u, nf, "trans")
                proved[u] = nf
                return
        for a in args:
            prove(a)
        nargs = [a if S.is_normal(a) else proved[a] for a in args]
        u2 = S.mk(sym, *nargs)
        if u2 != u:
            add(u, u2, "cong")
        rs = S.root_steps(u2)
        if not rs:
            proved[u] = u2
            return
        r = rs[0]
        add(u2, r, "rule")
        if not S.is_normal(r):
            prove(r)
        if not (u2 == u and S.is_normal(r)):
            add(u, nf, "trans")
        proved[u] = nf

    prove(s)
    return lines, proved


def check(S, lines):
    have = set()
    for l, r, kind in lines:
        if S.val[l] != S.val[r]:
            return f"unsound line {l}={r}"
        if kind == "rule":
            if r not in S.root_steps(l):
                return "bad rule line"
        elif kind == "cong":
            (fs, la), (gs, ra) = S.ops[l], S.ops[r]
            if fs != gs or any(a != b and (a, b) not in have for a, b in zip(la, ra)):
                return "bad congruence line"
        elif kind == "trans":
            # l = r must follow from earlier lines by a chain of equations
            frontier, seen = [l], {l}
            ok = False
            while frontier:
                x = frontier.pop()
                for (a, b) in have:
                    if a == x and b not in seen:
                        if b == r:
                            ok = True
                        seen.add(b)
                        frontier.append(b)
            if not ok:
                return "bad transitivity line"
        have.add((l, r))
    return None


bad = n = 0
for cls, N in ((Unary, 9), (Binary, 7)):
    S = cls(10**7)
    L = Lemmas(S)
    by = S.enumerate(N)
    terms = [t for k in by for t in by[k] if S.val[t] is not None and not S.is_normal(t)]
    random.seed(2)
    for t in random.sample(terms, min(1500, len(terms))):
        lines, proved = build(S, L, t)
        err = check(S, lines)
        total = sum(S.size[l] + S.size[r] for l, r, _ in lines)
        dag = L.dag_cost(t, 10**12)[0]
        n += 1
        if err or total != dag or S.val[proved[t]] != S.val[t] or not S.is_normal(proved[t]):
            bad += 1
            print(cls.__name__, err, total, dag)
print(n, "names checked,", bad, "problems")
