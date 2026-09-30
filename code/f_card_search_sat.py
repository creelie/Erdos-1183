#!/usr/bin/env python3
"""
f_card_search.py -- find a cardinality colouring g of {0,...,n} with no
monochromatic sublattice of more than ceil((n+1)/2) members; such a g
proves f(n) = ceil((n+1)/2), the lower bound being the trivial chain bound.

Candidates g (with g(0) = 1 and balanced colour counts, as chains force)
are filtered by the necessary condition of Proposition 6.1 of the paper
(no monochromatic arithmetic progression of k+1 terms with 2^k > m0,
m0 = ceil((n+1)/2)), then checked by the SAT encoding of witnesses.py (variant: SAT check only).

Usage: python3 f_card_search.py n
"""
import sys, math, itertools, time
from small_values import closed_family_of_size
from witnesses import independent_check

n = int(sys.argv[1])
N = 1 << n
m0 = math.ceil((n + 1) / 2)
target = m0 + 1
kmax = 1
while 2 ** kmax <= m0:
    kmax += 1          # forbid monochromatic APs of kmax+1 terms (cube of 2^kmax > m0)


def has_long_ap(g):
    L = len(g)
    for s in range(1, L):
        for a in range(0, L - kmax * s):
            c = g[a]
            if all(g[a + i * s] == c for i in range(1, kmax + 1)):
                return True
    return False


sizes = [bin(S).count('1') for S in range(N)]
t0 = time.time()
cands = []
for bits in itertools.product([0, 1], repeat=n):
    g = (1,) + bits
    if abs(sum(g) - (n + 1) / 2) > 1:
        continue
    if has_long_ap(g):
        continue
    cands.append(g)
print(f"n={n}: {len(cands)} candidate g after filtering", flush=True)
tried = 0
for g in cands:
    tried += 1
    classes = [{S for S in range(N) if g[sizes[S]] == c} for c in (0, 1)]
    ok = all(independent_check(G, target, True) for G in classes)
    if not ok:
        continue
    print(f"n={n}: g={g} has no monochromatic sublattice of size >= {target}; "
          f"independent check {'PASSED' if ok else 'FAILED'}; tried {tried}, "
          f"{time.time()-t0:.0f}s", flush=True)
    if ok:
        break
else:
    print(f"n={n}: no cardinality colouring achieves {m0}; tried {tried}, "
          f"{time.time()-t0:.0f}s", flush=True)
