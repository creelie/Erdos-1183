import numpy as np, pickle, time, heapq
best = pickle.load(open('gadgets.pkl', 'rb')); keys = list(best.keys())
exR = np.load('exR.npy'); exB = np.load('exB.npy')
G, NL = exR.shape
size = np.array([len(best[k]) for k in keys])
gR = np.zeros(NL, dtype=np.int16); gB = np.zeros(NL, dtype=np.int16)
def score(gi):
    return int((np.minimum(2, np.maximum(exR[gi], gR) + np.maximum(exB[gi], gB)) - np.minimum(2, gR + gB)).sum())
t0 = time.time()
heap = []
for gi in range(G):
    s = score(gi)
    if s > 0: heap.append((-(s * 1000 - size[gi]), gi))
heapq.heapify(heap); print('init', len(heap), time.time() - t0, flush=True)
chosen = []; cur = 0
while cur < 2 * NL:
    while True:
        negb, gi = heapq.heappop(heap)
        s = score(gi); val = s * 1000 - size[gi]
        if not heap or val >= -heap[0][0]:
            break
        if s > 0: heapq.heappush(heap, (-val, gi))
    chosen.append(gi); gR = np.maximum(gR, exR[gi]); gB = np.maximum(gB, exB[gi])
    cur = int(np.minimum(2, gR + gB).sum())
    if len(chosen) % 20 == 0: print(len(chosen), s, cur, 2 * NL, time.time() - t0, flush=True)
print('chosen', len(chosen), 'members', size[chosen].sum())
pickle.dump(chosen, open('chosen.pkl', 'wb'))
