# Explicit witnesses for the structures of the window argument.
import ctypes, os
_lib = ctypes.CDLL(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'libfindstruct.so'))
_lib.find_struct.restype = ctypes.c_int
_lib.find_struct.argtypes = [ctypes.c_uint64] * 3 + [ctypes.c_int] * 3 + [ctypes.POINTER(ctypes.c_longlong)]
_out = (ctypes.c_longlong * 4096)()
NOPIV = 63

def lmask(levels):
    return sum(1 << l for l in levels)

def find_struct(P, L, H, k, n, s):
    """A sublattice with at least s+1 members whose members sit at levels of P, or (pivot k)
    low levels L inside U, high levels H containing W, and at most one member at level k.
    Returns (base, weights, strict down-sets, member down-sets) or None."""
    cnt = _lib.find_struct(lmask(P), lmask(L), lmask(H), k, n, s, _out)
    if cnt == 0: return None
    b, E = _out[0], _out[1]
    wts = [_out[2 + 2 * i] for i in range(E)]
    dns = [_out[3 + 2 * i] for i in range(E)]
    mem = [_out[2 + 2 * E + j] for j in range(cnt)]
    return b, wts, dns, mem

def realise(st, P, k):
    """Members as subsets of {0..n-1} along the chain C_i = {0..i-1}: the join of the members
    below level k at non-P levels, the member at level k and the meet of those above k come first."""
    b, wts, dns, mem = st
    E = len(wts)
    wof = lambda D: sum(wts[i] for i in range(E) if (D >> i) & 1)
    JL, MH, DK = 0, (1 << E) - 1, None
    for D in mem:
        lev = b + wof(D)
        if lev in P: continue
        if lev == k: DK = D
        elif lev < k: JL |= D
        else: MH &= D
    segs = [JL, DK if DK is not None else JL, MH, (1 << E) - 1]
    order, seen = [], 0
    for seg in segs:
        for i in range(E):
            if (seg >> i) & 1 and not (seen >> i) & 1:
                order.append(i); seen |= 1 << i
    pos, block = b, {}
    for i in order:
        block[i] = sum(1 << t for t in range(pos, pos + wts[i])); pos += wts[i]
    base = (1 << b) - 1
    sets = []
    for D in mem:
        x = base
        for i in range(E):
            if (D >> i) & 1: x |= block[i]
        sets.append(x)
    return sorted(sets)

def closed(sets):
    S = set(sets)
    return len(S) == len(sets) and all((a | c) in S and (a & c) in S for a in sets for c in sets)
