# Certificate generator for P(m) >= K: every 2-colouring of 2^[m] has red and blue
# sublattices with at least K members in total, for a window whose mixed levels must lie
# in the band (pivot model).  Runs the split CEGAR with an explicit-witness search and
# writes every structure it used as an explicit sublattice of 2^[m].
# Output lines:  k  m1 m2 ...   (k = -1 for a structure used by size or with one
# member at a mixed level; k >= 0 for a pivot structure on the chain C_i = {0..i-1}).
import sys, time
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from structs import find_struct, realise, closed, NOPIV

def pc(x): return bin(x).count('1')

CERTS = {}
def record(k, sets):
    assert closed(sets)
    CERTS[(k, tuple(sets))] = 1

def levels_of(sets): return sorted(set(pc(x) for x in sets))

def card_split(m, x, y):
    solver = Cadical195(); v = lambda i: i + 1; top = m + 1
    for lits, bound in (([v(i) for i in range(m + 1)], x), ([-v(i) for i in range(m + 1)], y)):
        enc = CardEnc.atmost(lits, bound=bound, top_id=top, encoding=EncType.seqcounter)
        top = max(top, enc.nv)
        for c in enc.clauses: solver.add_clause(c)
    rounds = 0
    while solver.solve():
        rounds += 1
        mdl = solver.get_model(); g = [1 if mdl[i] > 0 else 0 for i in range(m + 1)]
        bad = None
        for col, s in ((1, x), (0, y)):
            C = {i for i in range(m + 1) if g[i] == col}
            st = find_struct(C, set(), set(), NOPIV, m, s)
            if st:
                sets = realise(st, C, NOPIV); bad = (col, s, sets); break
        if bad is None:
            return ''.join('R' if c else 'b' for c in g), rounds
        col, s, sets = bad
        record(-1, sets)
        T = [l - min(levels_of(sets)) for l in levels_of(sets)]
        other = y if col == 1 else x
        for b in range(0, m - max(T) + 1):
            lv = [v(b + t) for t in T]
            solver.add_clause([-l for l in lv] if col == 1 else lv)
            if other <= len(sets) - 1: solver.add_clause(lv if col == 1 else [-l for l in lv])
    return None, rounds

def band_split(n, band, x, y):
    solver = Cadical195(); top = [0]
    def new():
        top[0] += 1; return top[0]
    r = {l: new() for l in range(n + 1)}
    mx = {l: new() for l in band}
    e = {(k, j): new() for k in band for j in band if j != k}
    pure = {}
    for l in range(n + 1):
        if l in mx:
            pr, pb = new(), new()
            solver.add_clause([-pr, -mx[l]]); solver.add_clause([-pr, r[l]]); solver.add_clause([pr, mx[l], -r[l]])
            solver.add_clause([-pb, -mx[l]]); solver.add_clause([-pb, -r[l]]); solver.add_clause([pb, mx[l], r[l]])
            pure[(l, 1)], pure[(l, 0)] = pr, pb
        else:
            pure[(l, 1)], pure[(l, 0)] = r[l], -r[l]
    cube = {}
    for (k, j), vv in e.items():
        for c in (1, 0):
            a = new(); lit = vv if c == 1 else -vv
            solver.add_clause([-a, mx[j]]); solver.add_clause([-a, lit]); solver.add_clause([a, -mx[j], -lit])
            cube[(k, j, c)] = a
    anyM = new()
    solver.add_clause([-anyM] + [mx[l] for l in band]); [solver.add_clause([anyM, -mx[l]]) for l in band]
    solver.add_clause([anyM])
    for c, bound in ((1, x), (0, y)):
        lits = [pure[(l, c)] for l in range(n + 1)] + [anyM]
        enc = CardEnc.atmost(lits, bound=bound, top_id=top[0], encoding=EncType.seqcounter)
        top[0] = max(top[0], enc.nv)
        for cl in enc.clauses: solver.add_clause(cl)
    rounds = 0
    while solver.solve():
        rounds += 1
        mdl = set(l for l in solver.get_model() if l > 0)
        M = {l for l in band if mx[l] in mdl}
        col = {l: (1 if r[l] in mdl else 0) for l in range(n + 1)}
        added = False
        for c, s in ((1, x), (0, y)):
            P = {l for l in range(n + 1) if l not in M and col[l] == c}
            for mu in [NOPIV] + sorted(M):
                st = find_struct(P, set(), set(), mu, n, s)
                if st:
                    sets = realise(st, P, mu); record(-1, sets)
                    cl = [(-mx[lev]) if lev in M else -pure[(lev, c)] for lev in levels_of(sets)]
                    solver.add_clause(cl); added = True; break
            if added: break
        if added: continue
        for k in sorted(M):
            for c, s in ((1, x), (0, y)):
                P = {l for l in range(n + 1) if l not in M and col[l] == c}
                Lc = {j for j in M if j < k and ((e[(k, j)] in mdl) == (c == 1))}
                Hc = {j for j in M if j > k and ((e[(k, j)] in mdl) == (c == 1))}
                st = find_struct(P, Lc, Hc, k, n, s)
                if st:
                    sets = realise(st, P, k); record(k, sets)
                    cl = [-mx[k]]
                    for lev in levels_of(sets):
                        if lev in P: cl.append(-pure[(lev, c)])
                        elif lev == k: continue
                        else: cl.append(-cube[(k, lev, c)])
                    solver.add_clause(cl); added = True; break
            if added: break
        if not added:
            return ''.join('M' if l in M else ('R' if col[l] else 'b') for l in range(n + 1)), rounds
    return None, rounds

if __name__ == '__main__':
    m, K = int(sys.argv[1]), int(sys.argv[2])
    band = [int(t) for t in sys.argv[3].split(',')]
    out = sys.argv[4]
    t0 = time.time(); ok = True
    for x in range(K - 1, -1, -1):
        y = K - 1 - x
        if y > x: break
        w, rc = card_split(m, x, y)
        print(f"  size split {x}+{y}: {w or 'none'} ({rc} rounds, {len(CERTS)} certificates, {time.time()-t0:.1f} s)", flush=True)
        if w: ok = False
    for x in range(K - 1, -1, -1):
        y = K - 1 - x
        if y > x: break
        w, rb = band_split(m, band, x, y)
        print(f"  band split {x}+{y}: {w or 'none'} ({rb} rounds, {len(CERTS)} certificates, {time.time()-t0:.1f} s)", flush=True)
        if w: ok = False
    with open(out, 'w') as f:
        f.write(f"# m={m} K={K} band={','.join(map(str, band))}\n")
        for (k, sets) in sorted(CERTS):
            f.write(f"{k} " + ' '.join(map(str, sets)) + "\n")
    print(f"m={m} K={K}: {'PROVED' if ok else 'NOT PROVED'}, {len(CERTS)} certificates written to {out}", flush=True)
