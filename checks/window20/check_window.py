#!/usr/bin/env python3
"""Independent check of a window certificate (Python).

The certificate file starts with a line "# m=<m> K=<K> band=<j1>,<j2>,..." and then has one
line per sublattice of 2^[m]: an integer k followed by the members as bit masks.  The claim is
that every 2-colouring of the subsets of an m-element set has a red sublattice and a blue
sublattice with at least K members in total.

The check follows the reduction of the paper.
 (1) A level outside the band with sets of both colours gives the bound by Lemma (adjacent
     sets) and the lower bounds for smaller windows.
 (2) At a mixed band level k with an adjacent pair S, T, the cubes 2^(S&T) and [S|T, top]
     are coloured by size, or the bound holds.
 (3) Every remaining pattern (each level outside the band of one colour, each band level of
     one colour or mixed) is settled by the listed sublattices: k = -1 lines are moved to any
     position, and a line with k >= 0 has [k] = {0, ..., k-1} as its only member of size k and
     is mapped onto the pair at level k; its members inside [k-1] and its members containing
     [k+1] then take the colours of the two cubes beside the pair.
Usage: check_window.py certfile
"""
import sys
import numpy as np


def popcount(x):
    return bin(x).count("1")


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def subset_max(table, nbits):
    """table[x] = max over y subset of x of table[y], in place."""
    a = table.reshape(-1)
    for i in range(nbits):
        v = a.reshape(-1, 2, 1 << i)
        np.maximum(v[:, 1, :], v[:, 0, :], out=v[:, 1, :])
    return table


def main():
    if len(sys.argv) != 2:
        print("usage: check_window.py certfile")
        return 2
    with open(sys.argv[1]) as fh:
        header = fh.readline().split()
        params = dict(item.split("=") for item in header[1:])
        m, K = int(params["m"]), int(params["K"])
        band = [int(x) for x in params["band"].split(",") if x]
        lines = [ln.split() for ln in fh if ln.strip() and not ln.startswith("#")]
    L = m + 1
    NM = 1 << L

    # (1) lower bounds for smaller cubes: P(j) >= j + 1, and j + 2 for j >= 11
    def P(j):
        if j < 0:
            return 0
        return j + 2 if j >= 11 else j + 1

    for k in range(1, m):
        if k not in band and P(k - 1) + P(m - k - 1) + 2 < K:
            fail("level %d outside the band is not settled" % k)
    # (2) a cube not coloured by size beside a band pivot
    for k in band:
        if (k + 1) + (m - k) + 2 < K:
            fail("cube reduction at level %d" % k)

    NB = len(band)
    bidx = {j: i for i, j in enumerate(band)}
    res = [np.zeros(NM, dtype=np.int16) for _ in range(NB + 1)]
    piv = {}
    full = (1 << m) - 1
    for parts in lines:
        k = int(parts[0])
        X = [int(x) for x in parts[1:]]
        S = set(X)
        if len(S) != len(X):
            fail("repeated member")
        if any(a < 0 or a > full for a in X):
            fail("member out of range")
        for a in X:
            for b in X:
                if (a | b) not in S or (a & b) not in S:
                    fail("not a sublattice")
        cnt = len(X)
        if k < 0:
            top = 0
            bot = full
            for a in X:
                top |= a
                bot &= a
            t = popcount(top & ~bot)
            base = popcount(bot)
            rel = {}
            for a in X:
                r = popcount(a) - base
                rel[r] = rel.get(r, 0) + 1
            relmask = sum(1 << r for r in rel)
            # translates: the member a goes to level (|a| - |bot|) + d, for d = 0..m-t
            for d in range(0, m - t + 1):
                lm = relmask << d
                if res[0][lm] < cnt:
                    res[0][lm] = cnt
                for j, i in bidx.items():
                    if rel.get(j - d, 0) == 1:
                        key = lm & ~(1 << j)
                        if res[1 + i][key] < cnt:
                            res[1 + i][key] = cnt
        else:
            if k not in bidx:
                fail("pivot outside the band")
            Sk, below, above = (1 << k) - 1, (1 << (k - 1)) - 1, (1 << (k + 1)) - 1
            lv = {}
            good = True
            for a in X:
                j = popcount(a)
                if j == k:
                    if a != Sk:
                        good = False
                    continue
                inside = (a & ~below) == 0 if j < k else (a & above) == above
                lv[j] = lv.get(j, True) and inside
            if not good:
                continue
            strict = 0
            flex = 0
            for j, inside in lv.items():
                if inside and j in bidx:
                    flex |= 1 << j
                else:
                    strict |= 1 << j
            ki = bidx[k]
            for Mb in range(1 << NB):
                if not (Mb >> ki) & 1:
                    continue
                Mmask = sum(1 << band[i] for i in range(NB) if (Mb >> i) & 1)
                if strict & Mmask:
                    continue
                T = piv.get((ki, Mb))
                if T is None:
                    T = piv[(ki, Mb)] = np.zeros(NM, dtype=np.int16)
                key = strict | flex
                if T[key] < cnt:
                    T[key] = cnt
    for T in res:
        subset_max(T, L)
    for T in piv.values():
        subset_max(T, L)

    # (3) every pattern
    bandmask = sum(1 << j for j in band)
    rest = [l for l in range(L) if not (bandmask >> l) & 1]
    nr = len(rest)
    r = np.arange(1 << nr, dtype=np.int64)
    Rrest = np.zeros(1 << nr, dtype=np.int64)
    for i, l in enumerate(rest):
        Rrest |= ((r >> i) & 1) << l
    Brest = ((1 << L) - 1) & ~bandmask & ~Rrest
    pc = np.zeros(NM, dtype=np.int16)
    for i in range(L):
        pc += ((np.arange(NM) >> i) & 1).astype(np.int16)
    configs = via = words = 0
    least = 10 ** 9
    for st in range(3 ** NB):
        z = st
        Radd = Badd = 0
        Mi = []
        for i in range(NB):
            s = z % 3
            z //= 3
            if s == 0:
                Radd |= 1 << band[i]
            elif s == 1:
                Badd |= 1 << band[i]
            else:
                Mi.append(i)
        Rp = Rrest | Radd
        Bp = Brest | Badd
        configs += len(r)
        anyM = 1 if Mi else 0
        bR = np.maximum(pc[Rp] + anyM, res[0][Rp])
        bB = np.maximum(pc[Bp] + anyM, res[0][Bp])
        for i in Mi:
            bR = np.maximum(bR, res[1 + i][Rp])
            bB = np.maximum(bB, res[1 + i][Bp])
        tot = bR + bB
        okl = tot >= K
        if okl.any():
            least = min(least, int(tot[okl].min()))
        bad = np.nonzero(~okl)[0]
        if len(bad) == 0:
            continue
        if not Mi:
            fail("size colouring with pair %d" % int(tot[bad[0]]))
        via += len(bad)
        Rb, Bb, bRb, bBb = Rp[bad], Bp[bad], bR[bad], bB[bad]
        Mb = sum(1 << i for i in Mi)
        choices = []
        for i in Mi:
            T = piv.get((i, Mb))
            others = [band[j] for j in Mi if j != i]
            opts = []
            for eps in range(1 << len(others)):
                er = sum(1 << others[q] for q in range(len(others)) if (eps >> q) & 1)
                eb = sum(1 << others[q] for q in range(len(others)) if not (eps >> q) & 1)
                if T is None:
                    zero = np.zeros(len(bad), dtype=np.int16)
                    opts.append((zero, zero))
                else:
                    opts.append((T[Rb | er], T[Bb | eb]))
            choices.append(opts)
        # every combination of words, one per pivot
        combos = [()]
        for opts in choices:
            combos = [c + (o,) for c in combos for o in range(len(opts))]
        for c in combos:
            R = bRb.copy()
            B = bBb.copy()
            for a, o in enumerate(c):
                np.maximum(R, choices[a][o][0], out=R)
                np.maximum(B, choices[a][o][1], out=B)
            s = R + B
            words += len(bad)
            if (s < K).any():
                fail("pattern with pair %d" % int(s.min()))
            least = min(least, int(s.min()))
    print("m=%d K=%d band=%s: %d certificates, %d patterns, %d settled by pivots, "
          "%d word choices, least pair %d" % (m, K, ",".join(map(str, band)), len(lines),
                                               configs, via, words, least))
    print("PASS: every 2-colouring of 2^[%d] has a red and a blue sublattice with at least "
          "%d members in total" % (m, K))
    return 0


if __name__ == "__main__":
    sys.exit(main())
