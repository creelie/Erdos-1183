# Extract window gadgets from the k=-1 certificates of certs_19_22.txt.
import sys, collections
pc = lambda x: bin(x).count('1')
def gadget(X, m):
    top = 0; bot = (1 << m) - 1
    for a in X: top |= a; bot &= a
    el = [i for i in range(m) if (top & ~bot) >> i & 1]
    def comp(a):
        z = 0
        for q, e in enumerate(el):
            if a >> e & 1: z |= 1 << q
        return z
    Y = sorted(comp(a) for a in X)
    return len(el), Y
best = {}
n = 0
for line in open(sys.argv[1]):
    if line.startswith('#'): continue
    p = line.split()
    if p[0] != '-1': continue
    X = [int(x) for x in p[1:]]
    t, Y = gadget(X, 19)
    lv = tuple(sorted(set(pc(y) for y in Y)))
    key = (t, lv)
    if key not in best or len(best[key]) < len(Y): best[key] = Y
    n += 1
print(n, 'certs', len(best), 'distinct (t, levels)')
import pickle; pickle.dump(best, open('gadgets.pkl', 'wb'))
