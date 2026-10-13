# Choose a small gadget library that resolves every leaf of the prefix tree.
import numpy as np, pickle, collections, time
best = pickle.load(open('gadgets.pkl', 'rb'))
keys = list(best.keys())
leaves, used = pickle.load(open('tree.pkl', 'rb'))
NL = len(leaves)
LW = np.array([w for w, L, a, b in leaves], dtype=np.int64)
LL = np.array([L for w, L, a, b in leaves], dtype=np.int64)
LB = (~LW) & ((1 << LL) - 1)          # blue levels
def pcnt(a):
    c = np.zeros_like(a)
    for i in range(20): c += (a >> i) & 1
    return c
# options[g] = (exR, exB): arrays of best excess of gadget g over offsets, per leaf
t0 = time.time()
exR = np.zeros((len(keys), NL), dtype=np.int8); exB = np.zeros((len(keys), NL), dtype=np.int8)
for gi, (t, lv) in enumerate(keys):
    cnt = len(best[(t, lv)]); lm = sum(1 << l for l in lv); wm = (1 << (t + 1)) - 1
    for d in range(0, 20 - t):
        ok = LL >= d + t + 1
        if not ok.any(): break
        for col, X, E in ((1, LW, exR), (0, LB, exB)):
            x = (X >> d) & wm
            v = np.where(ok & ((x & lm) == lm), cnt - pcnt(x), 0)
            np.maximum(E[gi], v.astype(np.int8), out=E[gi])
    if gi % 5000 == 0: print(gi, time.time() - t0, flush=True)
np.save('exR.npy', exR); np.save('exB.npy', exB)
print('done', time.time() - t0)
