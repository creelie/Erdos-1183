# Build a prefix decision tree for the size colourings of 2^[19] (words of length 20).
import numpy as np, pickle, sys, collections
sys.setrecursionlimit(10000)
M = 20
best = pickle.load(open('gadgets.pkl', 'rb'))
lib = [(t, lv, len(Y)) for (t, lv), Y in best.items()]
# tables with argmax: T[t][x] = (cnt, gadget index) best over gadgets with levels subset of x
T = {}; A = {}
for gi, (t, lv, cnt) in enumerate(lib):
    if t not in T:
        T[t] = np.zeros(1 << (t + 1), dtype=np.int16); A[t] = -np.ones(1 << (t + 1), dtype=np.int32)
    key = sum(1 << l for l in lv)
    if cnt > T[t][key]: T[t][key] = cnt; A[t][key] = gi
for t in T:
    n = t + 1; idx = np.arange(1 << n)
    for i in range(n):
        sel = np.nonzero((idx >> i) & 1)[0]
        src = sel ^ (1 << i)
        better = T[t][src] > T[t][sel]
        T[t][sel[better]] = T[t][src[better]]; A[t][sel[better]] = A[t][src[better]]
pcs = [bin(x).count('1') for x in range(1 << M)]
Tl = {t: T[t].tolist() for t in T}; Al = {t: A[t].tolist() for t in T}
ts = sorted(T)
def best_in_prefix(w, L, col):
    # w: int bits 0..L-1 (bit 1 = red); col 1 = red, 0 = blue
    x = w if col else (~w) & ((1 << L) - 1)
    bestv = 0; bestp = None
    for t in ts:
        if t + 1 > L: break
        msk = (1 << (t + 1)) - 1
        Tt = Tl[t]
        for d in range(0, L - t):
            c = (x >> d) & msk
            v = Tt[c] - pcs[c]
            if v > bestv: bestv = v; bestp = (Al[t][c], d)
    return bestv, bestp
leaves = []; used = collections.Counter()
def build(w, L):
    gr, pr = best_in_prefix(w, L, 1); gb, pb = best_in_prefix(w, L, 0)
    if gr + gb >= 2:
        leaves.append((w, L, pr, pb)); 
        if pr: used[pr[0]] += 1
        if pb: used[pb[0]] += 1
        return
    if L == M: raise Exception('unresolved %s' % bin(w))
    build(w, L + 1); build(w | (1 << L), L + 1)
build(0, 1)   # bit 0 = 0: the empty set is blue
print('leaves', len(leaves), 'distinct gadgets', len(used))
print(collections.Counter(L for w, L, a, b in leaves))
pickle.dump((leaves, used), open('tree.pkl', 'wb'))
