import sys, time, math
sys.argv=['x']
from small_values import closed_family_of_size
from pysat.solvers import Cadical153
def size_based_ok(n, target):
    """Return a size-based colouring g with no monochromatic sublattice of size >= target, or None."""
    N=1<<n; sets=list(range(N))
    solver=Cadical153(); solver.add_clause([1])
    # equality of colours within a size class: link S to representative
    rep={}
    for S in sets:
        k=bin(S).count('1')
        if k in rep:
            R=rep[k]; solver.add_clause([-(S+1),R+1]); solver.add_clause([S+1,-(R+1)])
        else: rep[k]=S
    it=0
    while True:
        if not solver.solve(): return None
        model=solver.get_model(); pos=set(v for v in model if v>0)
        col={S:((S+1) in pos) for S in sets}
        bad=None
        for c in (True,False):
            G={S for S in sets if col[S]==c}
            H=closed_family_of_size(G,target,True)
            if H is not None: bad=H; break
        if bad is None:
            return [int(col[rep[k]]) for k in range(n+1)]
        solver.add_clause([S+1 for S in bad]); solver.add_clause([-(S+1) for S in bad]); it+=1
for n in range(3, 10):
    t=time.time()
    g=size_based_ok(n, math.ceil((n+1)/2)+1)
    print(n, g, f"{time.time()-t:.0f}s", flush=True)
