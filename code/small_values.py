#!/usr/bin/env python3
"""
small_values.py -- exact values of f(n) and F(n) for small n.

f(n): largest m such that every 2-colouring of the subsets of [n] has a
      monochromatic family of >= m sets closed under union and intersection.
F(n): the same with closure under union only.

Method: counterexample-guided SAT.  Variables x_S (S a subset, as a bitmask).
To test whether f(n) >= M we ask for a colouring with no monochromatic closed
family of size >= M.  A candidate colouring from the solver is checked by a
branch-and-bound search for a monochromatic closed family of size >= M in
either colour class; if one is found, the clause forbidding that family from
being monochromatic (both polarities) is added and the solver is re-run.
UNSAT means every colouring has such a family, i.e. f(n) >= M.

Usage: python3 small_values.py NMAX
"""
import sys
from pysat.solvers import Cadical153


def closed_family_of_size(G, M, both):
    """Search for a family H subset of G (a set of bitmasks) with |H| >= M,
    closed under union (and intersection if both=True).  Returns H or None."""
    G = sorted(G)
    Gset = set(G)
    n = len(G)
    best = [None]

    def closure_add(H, s):
        """Add s to closed family H (a set); return new closed family or
        None if the closure leaves G."""
        H2 = set(H)
        frontier = [s]
        while frontier:
            t = frontier.pop()
            if t in H2:
                continue
            if t not in Gset:
                return None
            for u in list(H2):
                v = t | u
                if v not in H2:
                    frontier.append(v)
                if both:
                    w = t & u
                    if w not in H2:
                        frontier.append(w)
            H2.add(t)
        return H2

    def rec(i, H, excluded):
        if best[0] is not None:
            return
        if len(H) >= M:
            best[0] = set(H)
            return
        # remaining candidates
        if len(H) + (n - i) < M:
            return
        for j in range(i, n):
            s = G[j]
            if s in H or s in excluded:
                continue
            H2 = closure_add(H, s)
            if H2 is not None and not (H2 & excluded):
                rec(j + 1, H2, excluded)
                if best[0] is not None:
                    return
            excluded = excluded | {s}
            if len(H) + (n - j - 1) < M:
                return

    rec(0, set(), set())
    return best[0]


def value(n, both):
    N = 1 << n
    sets = list(range(N))
    # variable for set S is S+1
    M = 1
    known_lower = 1
    while True:
        # test whether some colouring avoids monochromatic closed families of size >= M+1
        target = M + 1
        solver = Cadical153()
        solver.add_clause([1])  # symmetry: empty set has colour 1
        found_colouring = None
        clauses = 0
        while True:
            if not solver.solve():
                break
            model = solver.get_model()
            pos = set(v for v in model if v > 0)
            col = {S: ((S + 1) in pos) for S in sets}
            bad = None
            for c in (True, False):
                G = {S for S in sets if col[S] == c}
                H = closed_family_of_size(G, target, both)
                if H is not None:
                    bad = H
                    break
            if bad is None:
                found_colouring = col
                break
            solver.add_clause([S + 1 for S in bad])
            solver.add_clause([-(S + 1) for S in bad])
            clauses += 2
        if found_colouring is None:
            # every colouring has a monochromatic closed family of size >= M+1
            M += 1
            continue
        return M, clauses


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for n in range(1, NMAX + 1):
        f, c1 = value(n, True)
        F, c2 = value(n, False)
        print(f"n={n}: f(n)={f}  F(n)={F}   (clauses {c1}, {c2})", flush=True)
