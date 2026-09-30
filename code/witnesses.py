#!/usr/bin/env python3
"""
witnesses.py -- produce and independently verify extremal colourings.

For each (n, both) given on the command line, the script finds a
2-colouring of the subsets of [n] with no monochromatic closed family of
size >= v+1, where v is the value f(n) (both=1) or F(n) (both=0) reported by
small_values.py, using the same counterexample-guided loop, and then
verifies the colouring with an INDEPENDENT checker: a SAT encoding of
"there is a closed subfamily of size >= v+1 inside this colour class"
(pysat, CaDiCaL), which must report UNSAT for both colour classes.

The colouring is written to witness_{f|F}_{n}.txt as a 0/1 string indexed
by the bitmask of the subset.

Usage: python3 witnesses.py n both v
"""
import sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from small_values import closed_family_of_size


def independent_check(G, target, both):
    """Return True iff G (set of bitmasks) contains NO closed subfamily of
    size >= target.  Uses a SAT encoding, independent of the DFS."""
    G = sorted(G)
    if len(G) < target:
        return True
    idx = {S: i + 1 for i, S in enumerate(G)}
    Gset = set(G)
    s = Cadical153()
    for i, A in enumerate(G):
        for B in G[i + 1:]:
            for C in ((A | B,) if not both else (A | B, A & B)):
                if C in Gset:
                    if C != A and C != B:
                        s.add_clause([-idx[A], -idx[B], idx[C]])
                else:
                    s.add_clause([-idx[A], -idx[B]])
    card = CardEnc.atleast(lits=list(range(1, len(G) + 1)), bound=target,
                           top_id=len(G), encoding=EncType.seqcounter)
    for cl in card.clauses:
        s.add_clause(cl)
    return not s.solve()


def find_witness(n, both, target):
    N = 1 << n
    sets = list(range(N))
    solver = Cadical153()
    solver.add_clause([1])
    while True:
        if not solver.solve():
            return None
        pos = set(v for v in solver.get_model() if v > 0)
        col = {S: ((S + 1) in pos) for S in sets}
        bad = None
        for c in (True, False):
            G = {S for S in sets if col[S] == c}
            H = closed_family_of_size(G, target, both)
            if H is not None:
                bad = H
                break
        if bad is None:
            return col
        solver.add_clause([S + 1 for S in bad])
        solver.add_clause([-(S + 1) for S in bad])


if __name__ == "__main__":
    n, both, v = int(sys.argv[1]), bool(int(sys.argv[2])), int(sys.argv[3])
    col = find_witness(n, both, v + 1)
    assert col is not None, "no witness: value is larger than claimed"
    N = 1 << n
    ok = all(independent_check({S for S in range(N) if col[S] == c}, v + 1, both)
             for c in (True, False))
    name = f"witness_{'f' if both else 'F'}_{n}.txt"
    with open(name, "w") as fh:
        fh.write("".join("1" if col[S] else "0" for S in range(N)) + "\n")
    print(f"{name}: independent verification {'PASSED' if ok else 'FAILED'}")
