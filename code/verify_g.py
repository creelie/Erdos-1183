#!/usr/bin/env python3
"""verify_g.py -- independent SAT check that the cardinality colourings g_n listed in the
paper have no monochromatic sublattice with more than ceil((n+1)/2) members."""
import math
from witnesses import independent_check
G = {3:[1,1,0,0], 4:[1,1,0,1,0], 5:[1,1,0,1,0,0], 6:[1,0,0,1,0,1,1], 7:[1,0,0,1,1,0,0,1],
     8:[1,0,1,0,0,1,1,0,1], 9:[1,0,1,0,0,1,1,0,1,0],
     10:[1,0,0,1,1,0,0,1,0,1,1]}
for n,g in G.items():
    N=1<<n; target=math.ceil((n+1)/2)+1
    ok=all(independent_check({S for S in range(N) if g[bin(S).count('1')]==c}, target, True) for c in (0,1))
    print(f"n={n}: g_n has no monochromatic sublattice of size >= {target}: {ok}", flush=True)
