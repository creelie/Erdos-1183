/* Independent check of a window certificate (C).

   The certificate file starts with "# m=<m> K=<K> band=<j1>,<j2>,..." and has one line per
   sublattice of 2^[m]: an integer k and the members as bit masks.  It certifies that every
   2-colouring of the subsets of an m-element set has a red and a blue sublattice with at least
   K members in total.  Same reduction as the paper: a mixed level outside the band settles the
   bound by the adjacent-set lemma; at a mixed band level k with an adjacent pair the two cubes
   beside the pair are coloured by size; every remaining pattern is settled by a listed
   sublattice (k = -1: moved to any position; k >= 0: placed around the pair at level k).
   Usage: check_window certfile */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
static int m, K, NB, band[64], bandIndex[64];
static unsigned char *res[65];           /* res[0]: no mixed member; res[1+i]: one at band[i] */
static unsigned char *piv[64 * 4096];    /* piv[i * 2^NB + Mb] */
static u64 NM;

static int pc(u64 x) { return __builtin_popcountll(x); }
static void die(const char *s) { printf("FAIL: %s\n", s); exit(1); }
static int cmpu(const void *a, const void *b) {
    u64 x = *(const u64 *)a, y = *(const u64 *)b; return x < y ? -1 : x > y;
}
static int has(const u64 *s, int n, u64 v) {
    int lo = 0, hi = n - 1;
    while (lo <= hi) { int mid = (lo + hi) / 2; if (s[mid] == v) return 1; if (s[mid] < v) lo = mid + 1; else hi = mid - 1; }
    return 0;
}
static int P(int j) { return j < 0 ? 0 : (j >= 11 ? j + 2 : j + 1); }
static void upd(unsigned char *T, u64 key, int v) { if (T[key] < v) T[key] = (unsigned char)v; }
static void zeta(unsigned char *T, int bits) {
    for (int i = 0; i < bits; ++i)
        for (u64 x = 0; x < ((u64)1 << bits); ++x)
            if (x >> i & 1) { unsigned char v = T[x ^ ((u64)1 << i)]; if (T[x] < v) T[x] = v; }
}

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: %s certfile\n", argv[0]); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    static char line[1 << 20];
    if (!fgets(line, sizeof line, f)) die("empty file");
    if (sscanf(line, "# m=%d K=%d", &m, &K) != 2) die("bad header");
    char *bp = strstr(line, "band="); NB = 0;
    for (int i = 0; i < 64; ++i) bandIndex[i] = -1;
    if (bp) { bp += 5; while (*bp && *bp != '\n') { if (*bp >= '0' && *bp <= '9') { int v = strtol(bp, &bp, 10); bandIndex[v] = NB; band[NB++] = v; } else ++bp; } }
    int L = m + 1; NM = (u64)1 << L;
    for (int k = 1; k < m; ++k)
        if (bandIndex[k] < 0 && P(k - 1) + P(m - k - 1) + 2 < K) die("level outside the band not settled");
    for (int i = 0; i < NB; ++i) if ((band[i] + 1) + (m - band[i]) + 2 < K) die("cube reduction");
    for (int i = 0; i <= NB; ++i) res[i] = calloc(NM, 1);
    u64 full = ((u64)1 << m) - 1;
    long ncert = 0;
    static u64 X[1 << 16];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        char *p = line; long k = strtol(p, &p, 10); int n = 0;
        for (;;) { while (*p == ' ') ++p; if (*p < '0' || *p > '9') break; X[n++] = strtoull(p, &p, 10); }
        ++ncert;
        qsort(X, n, sizeof(u64), cmpu);
        for (int i = 0; i + 1 < n; ++i) if (X[i] == X[i + 1]) die("repeated member");
        for (int i = 0; i < n; ++i) if (X[i] > full) die("member out of range");
        for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j)
            if (!has(X, n, X[i] | X[j]) || !has(X, n, X[i] & X[j])) die("not a sublattice");
        if (k < 0) {
            u64 top = 0, bot = full; for (int i = 0; i < n; ++i) { top |= X[i]; bot &= X[i]; }
            int t = pc(top & ~bot), base = pc(bot);
            int relcnt[64] = {0}; u64 rel = 0;
            for (int i = 0; i < n; ++i) { int r = pc(X[i]) - base; relcnt[r]++; rel |= (u64)1 << r; }
            for (int d = 0; d + t <= m; ++d) {
                u64 lm = rel << d; upd(res[0], lm, n);
                for (int i = 0; i < NB; ++i) { int r = band[i] - d; if (r >= 0 && relcnt[r] == 1) upd(res[1 + i], lm & ~((u64)1 << band[i]), n); }
            }
        } else {
            if (k >= 64 || bandIndex[k] < 0) die("pivot outside the band");
            int ki = bandIndex[k]; u64 Sk = ((u64)1 << k) - 1, lo = ((u64)1 << (k - 1)) - 1, hi = ((u64)1 << (k + 1)) - 1;
            int seen[64] = {0}, inside[64]; int good = 1;
            for (int j = 0; j < 64; ++j) inside[j] = 1;
            for (int i = 0; i < n; ++i) {
                int j = pc(X[i]);
                if (j == k) { if (X[i] != Sk) good = 0; continue; }
                seen[j] = 1;
                if (j < k ? (X[i] & ~lo) != 0 : (X[i] & hi) != hi) inside[j] = 0;
            }
            if (!good) continue;
            u64 strict = 0, flex = 0;
            for (int j = 0; j <= m; ++j) if (seen[j]) { if (inside[j] && bandIndex[j] >= 0) flex |= (u64)1 << j; else strict |= (u64)1 << j; }
            for (int Mb = 0; Mb < (1 << NB); ++Mb) {
                if (!(Mb >> ki & 1)) continue;
                u64 Mm = 0; for (int i = 0; i < NB; ++i) if (Mb >> i & 1) Mm |= (u64)1 << band[i];
                if (strict & Mm) continue;
                unsigned char **T = &piv[ki * (1 << NB) + Mb]; if (!*T) *T = calloc(NM, 1);
                upd(*T, strict | flex, n);
            }
        }
    }
    for (int i = 0; i <= NB; ++i) zeta(res[i], L);
    for (int i = 0; i < NB * (1 << NB); ++i) if (piv[i]) zeta(piv[i], L);
    u64 bandMask = 0; for (int i = 0; i < NB; ++i) bandMask |= (u64)1 << band[i];
    int rest[64], nr = 0; for (int l = 0; l < L; ++l) if (!(bandMask >> l & 1)) rest[nr++] = l;
    int NS = 1; for (int i = 0; i < NB; ++i) NS *= 3;
    long long configs = 0, via = 0, words = 0; int least = 1 << 30;
    for (int st = 0; st < NS; ++st) {
        u64 Radd = 0, Badd = 0; int Mi[64], nm = 0, Mb = 0, z = st;
        for (int i = 0; i < NB; ++i) { int s = z % 3; z /= 3; if (s == 0) Radd |= (u64)1 << band[i]; else if (s == 1) Badd |= (u64)1 << band[i]; else { Mi[nm++] = i; Mb |= 1 << i; } }
        for (u64 r = 0; r < ((u64)1 << nr); ++r) {
            u64 Rp = Radd, Bp = Badd;
            for (int i = 0; i < nr; ++i) { if (r >> i & 1) Rp |= (u64)1 << rest[i]; else Bp |= (u64)1 << rest[i]; }
            ++configs;
            int bR = pc(Rp) + (nm > 0), bB = pc(Bp) + (nm > 0);
            if (res[0][Rp] > bR) bR = res[0][Rp];
            if (res[0][Bp] > bB) bB = res[0][Bp];
            for (int a = 0; a < nm; ++a) { int i = Mi[a]; if (res[1 + i][Rp] > bR) bR = res[1 + i][Rp]; if (res[1 + i][Bp] > bB) bB = res[1 + i][Bp]; }
            if (bR + bB >= K) { if (bR + bB < least) least = bR + bB; continue; }
            if (nm == 0) die("size colouring below the bound");
            ++via;
            /* per pivot, values over the words of the other mixed levels inside its cubes */
            int vr[16][64], vb[16][64], nw[16];
            for (int a = 0; a < nm; ++a) {
                int i = Mi[a], oth[16], no = 0;
                for (int b = 0; b < nm; ++b) if (b != a) oth[no++] = band[Mi[b]];
                nw[a] = 1 << no;
                unsigned char *T = piv[i * (1 << NB) + Mb];
                for (int e = 0; e < nw[a]; ++e) {
                    u64 er = 0, eb = 0; for (int q = 0; q < no; ++q) { if (e >> q & 1) er |= (u64)1 << oth[q]; else eb |= (u64)1 << oth[q]; }
                    vr[a][e] = T ? T[Rp | er] : 0; vb[a][e] = T ? T[Bp | eb] : 0;
                }
            }
            int idx[16] = {0};
            for (;;) {
                int R = bR, B = bB;
                for (int a = 0; a < nm; ++a) { if (vr[a][idx[a]] > R) R = vr[a][idx[a]]; if (vb[a][idx[a]] > B) B = vb[a][idx[a]]; }
                ++words;
                if (R + B < K) die("pattern below the bound");
                if (R + B < least) least = R + B;
                int a = 0; while (a < nm && ++idx[a] == nw[a]) { idx[a] = 0; ++a; }
                if (a == nm) break;
            }
        }
    }
    printf("m=%d K=%d band=", m, K); for (int i = 0; i < NB; ++i) printf(i ? ",%d" : "%d", band[i]);
    printf(": %ld certificates, %lld patterns, %lld settled by pivots, %lld word choices, least pair %d\n", ncert, configs, via, words, least);
    printf("PASS: every 2-colouring of 2^[%d] has a red and a blue sublattice with at least %d members in total\n", m, K);
    return 0;
}
