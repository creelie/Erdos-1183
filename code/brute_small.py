#!/usr/bin/env python3
"""brute_small.py -- exhaustive check of f(n), F(n) for n <= 4 over all 2^(2^n) colourings,
using an independent maximal-closed-family enumeration (no SAT)."""
import itertools, sys
def closed_families(n, both):
    N=1<<n; sets=range(N); fams=[]
    # enumerate all families closed under the operations by brute force over subsets of 2^[n] (n<=4: 2^16 families)
    for mask in range(1, 1<<N):
        fam=[S for S in sets if mask>>S&1]
        ok=True
        for A in fam:
            for B in fam:
                if not (mask>>(A|B)&1) or (both and not (mask>>(A&B)&1)): ok=False; break
            if not ok: break
        if ok: fams.append((len(fam), mask))
    return fams
for n in range(1,5):
    N=1<<n
    for both in (True, False):
        fams=closed_families(n,both)
        best=None
        for col in range(1<<N):
            m=0
            for size,mask in fams:
                if size<=m: continue
                # monochromatic?
                c=col&mask
                if c==0 or c==mask: m=size
            best=m if best is None else min(best,m)
        print(f"n={n} {'f' if both else 'F'}(n)={best}", flush=True)
