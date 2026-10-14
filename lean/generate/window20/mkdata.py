# Data for the Lean check of the size colourings of 2^[19]: gadgets and a preorder tree.
import pickle, sys
sys.setrecursionlimit(10000)
best = pickle.load(open('gadgets.pkl', 'rb')); keys = list(best.keys())
leaves, used = pickle.load(open('tree.pkl', 'rb'))
chosen = pickle.load(open('chosen.pkl', 'rb'))
pc = lambda x: bin(x).count('1')
G = []   # gadget j (1-based in Lean): (t, masks, lm, cnt)
for gi in chosen:
    t, lv = keys[gi]; Y = sorted(best[(t, lv)])
    lmv = 0
    for y in Y: lmv |= 1 << pc(y)
    G.append((t, Y, lmv, len(Y)))
def gain(g, d, w, L, col):
    t, Y, lm, cnt = g
    cm = w if col else (~w) & ((1 << L) - 1)
    if d + t + 1 > L: return 0
    if ((lm << d) & cm) != (lm << d): return 0
    p = pc((cm >> d) & ((1 << (t + 1)) - 1))
    return max(0, cnt - p)
def resolve(w, L):
    opts = {1: [(0, 0, 0)], 0: [(0, 0, 0)]}
    for col in (1, 0):
        for j, g in enumerate(G):
            for d in range(0, L - g[0]):
                e = gain(g, d, w, L, col)
                if e > 0: opts[col].append((e, j + 1, d))
    bestc = None
    for er, jr, dr in opts[1]:
        for eb, jb, db in opts[0]:
            if er + eb >= 2:
                c = (er + eb, -(jr + jb))
                if bestc is None or c < bestc[0]: bestc = (c, (jr, dr, jb, db))
    return bestc[1] if bestc else None
leafset = {(w, L) for w, L, a, b in leaves}
out = []
def build(w, L):
    if (w, L) in leafset:
        r = resolve(w, L); assert r is not None, (w, L)
        jr, dr, jb, db = r
        out.append(1 + (jr | dr << 10 | jb << 15 | db << 25)); return
    out.append(0)
    build(w, L + 1); build(w | 1 << L, L + 1)
build(0, 1)
print(len(out), 'items', len(G), 'gadgets', max(out).bit_length(), 'bits')
pickle.dump((G, out), open('leandata.pkl', 'wb'))
