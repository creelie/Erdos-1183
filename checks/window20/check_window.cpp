// Independent check of a window certificate: every 2-colouring of the subsets of an
// m-element set has a red and a blue sublattice with at least K members in total.
// Reads explicit sublattices, checks them, and runs through every colouring pattern of
// the reduction (levels outside the band pure; band levels pure or mixed; for a mixed
// pivot level k, the size words of the cubes below and above the pivot pair).
// Usage: check_window certfile
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <set>
#include <string>
#include <sstream>
#include <fstream>
#include <algorithm>
using namespace std;
typedef unsigned long long u64;
static int m, K; static vector<int> band;
static int popc(u64 x) { return __builtin_popcountll(x); }
static bool inBand(int j) { return find(band.begin(), band.end(), j) != band.end(); }

int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s certfile\n", argv[0]); return 2; }
    ifstream in(argv[1]); string line;
    getline(in, line);
    if (sscanf(line.c_str(), "# m=%d K=%d", &m, &K) != 2) { fprintf(stderr, "bad header\n"); return 2; }
    { size_t p = line.find("band="); string b = line.substr(p + 5); stringstream ss(b); string t;
      while (getline(ss, t, ',')) band.push_back(atoi(t.c_str())); }
    int L = m + 1, NB = band.size(); u64 NM = 1ULL << L;
    // Band reduction: a mixed level k outside the band gives pair >= P(k-1) + P(m-k-1) + 2,
    // with P(j) >= j + 1, and P(j) >= j + 2 for j >= 11 (the 12-level window and stacking).
    auto Plow = [](int j) { return j < 0 ? 0 : j + 1 + (j >= 11 ? 1 : 0); };
    for (int k = 1; k < m; ++k)
        if (!inBand(k) && Plow(k - 1) + Plow(m - k - 1) + 2 < K) { printf("FAIL band: level %d\n", k); return 1; }
    // At a band pivot, a cube 2^U or [W, top] not coloured by size has pair at least its
    // dimension + 2, so pair >= (k + 1) + (m - k) + 2.
    for (int k : band) if ((k + 1) + (m - k) + 2 < K) { printf("FAIL: cube reduction at %d\n", k); return 1; }
    // Tables: residual (index 0 = no mixed member, 1 + i = one member at band level band[i]),
    // pivot (k index i, mixed set M as a bit mask over the band).
    vector<vector<unsigned char>> res(NB + 1, vector<unsigned char>(NM, 0));
    vector<vector<unsigned char>> piv((size_t)NB << NB);
    long ncert = 0, ntrans = 0;
    while (getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;
        stringstream ss(line); long long kk; ss >> kk; vector<u64> X; long long t;
        while (ss >> t) X.push_back((u64)t);
        ++ncert;
        set<u64> S(X.begin(), X.end());
        if (S.size() != X.size()) { printf("FAIL: repeated member\n"); return 1; }
        for (u64 a : X) {
            if (a >= (1ULL << m)) { printf("FAIL: member out of range\n"); return 1; }
            for (u64 b : X) if (!S.count(a | b) || !S.count(a & b)) { printf("FAIL: not a sublattice\n"); return 1; }
        }
        int cnt = X.size();
        if (kk < 0) {
            // Move the sublattice to any position: drop the elements common to all members,
            // renumber the rest of the top member as 0..t-1, shift by d and add {0..d-1}.
            // The map is injective and commutes with union and intersection.
            u64 top = 0, bot = ~0ULL; for (u64 a : X) { top |= a; bot &= a; }
            vector<int> el; for (int i = 0; i < m; ++i) if (((top & ~bot) >> i) & 1) el.push_back(i);
            int tt = el.size();
            auto comp = [&](u64 a) { u64 z = 0; for (int q = 0; q < tt; ++q) if ((a >> el[q]) & 1) z |= 1ULL << q; return z; };
            for (int d = 0; tt + d <= m; ++d) {
                vector<u64> Y; for (u64 a : X) Y.push_back((comp(a) << d) | ((1ULL << d) - 1));
                ++ntrans;
                u64 lm = 0; for (u64 a : Y) lm |= 1ULL << popc(a);
                res[0][lm] = max<int>(res[0][lm], cnt);
                for (int i = 0; i < NB; ++i) {
                    int j = band[i], c = 0; for (u64 a : Y) if (popc(a) == j) ++c;
                    if (c == 1) { u64 lj = lm & ~(1ULL << j); res[1 + i][lj] = max<int>(res[1 + i][lj], cnt); }
                }
            }
        } else {
            int k = kk, ki = -1; for (int i = 0; i < NB; ++i) if (band[i] == k) ki = i;
            if (ki < 0) { printf("FAIL: pivot outside band\n"); return 1; }
            u64 Ck = (1ULL << k) - 1, Cl = (1ULL << (k - 1)) - 1, Ch = (1ULL << (k + 1)) - 1;
            u64 strict = 0, flex = 0; bool ok = true;
            for (int j = 0; j <= m; ++j) {
                bool any = false, allIn = true;
                for (u64 a : X) if (popc(a) == j) {
                    any = true;
                    if (j == k) { if (a != Ck) ok = false; }
                    else if (j < k) { if (a & ~Cl) allIn = false; }
                    else { if ((a & Ch) != Ch) allIn = false; }
                }
                if (!any || j == k) continue;
                if (allIn && inBand(j)) flex |= 1ULL << j; else strict |= 1ULL << j;
            }
            if (!ok) continue;
            for (int Mb = 0; Mb < (1 << NB); ++Mb) {
                if (!((Mb >> ki) & 1)) continue;
                u64 Mmask = 0; for (int i = 0; i < NB; ++i) if ((Mb >> i) & 1) Mmask |= 1ULL << band[i];
                if (strict & Mmask) continue;
                auto& T = piv[((size_t)ki << NB) | Mb]; if (T.empty()) T.assign(NM, 0);
                u64 key = strict | flex; T[key] = max<int>(T[key], cnt);
            }
        }
    }
    auto zeta = [&](vector<unsigned char>& T) {
        for (int i = 0; i < L; ++i) for (u64 x = 0; x < NM; ++x) if ((x >> i) & 1) T[x] = max(T[x], T[x ^ (1ULL << i)]);
    };
    for (auto& T : res) zeta(T);
    for (auto& T : piv) if (!T.empty()) zeta(T);
    u64 bandMask = 0; for (int j : band) bandMask |= 1ULL << j;
    vector<int> rest; for (int l = 0; l <= m; ++l) if (!((bandMask >> l) & 1)) rest.push_back(l);
    long long configs = 0, viaPivot = 0, epsChecked = 0; int worst = 1000;
    int NS = 1; for (int i = 0; i < NB; ++i) NS *= 3;
    for (u64 r = 0; r < (1ULL << rest.size()); ++r) {
        u64 Rb = 0; for (size_t i = 0; i < rest.size(); ++i) if ((r >> i) & 1) Rb |= 1ULL << rest[i];
        u64 Bb = ((1ULL << L) - 1) & ~bandMask & ~Rb;
        for (int st = 0; st < NS; ++st) {
            u64 Rp = Rb, Bp = Bb; int Mb = 0; int z = st; vector<int> Mi;
            for (int i = 0; i < NB; ++i) { int s = z % 3; z /= 3;
                if (s == 0) Rp |= 1ULL << band[i]; else if (s == 1) Bp |= 1ULL << band[i]; else { Mb |= 1 << i; Mi.push_back(i); } }
            ++configs;
            int anyM = Mb ? 1 : 0;
            int bR = popc(Rp) + anyM, bB = popc(Bp) + anyM;
            bR = max<int>(bR, res[0][Rp]); bB = max<int>(bB, res[0][Bp]);
            for (int i : Mi) { bR = max<int>(bR, res[1 + i][Rp]); bB = max<int>(bB, res[1 + i][Bp]); }
            if (bR + bB >= K) { worst = min(worst, bR + bB); continue; }
            if (!Mb) { printf("FAIL: size colouring R=%llx B=%llx pair %d\n", Rp, Bp, bR + bB); return 1; }
            ++viaPivot;
            // For each pivot, the best red and blue values over the words of its two cubes.
            int nm = Mi.size();
            vector<vector<int>> vr(nm), vb(nm); vector<int> others(nm);
            for (int a = 0; a < nm; ++a) {
                int i = Mi[a]; auto& T = piv[((size_t)i << NB) | Mb];
                vector<int> oth; for (int b2 : Mi) if (b2 != i) oth.push_back(band[b2]);
                int no = oth.size(); others[a] = no;
                for (int eps = 0; eps < (1 << no); ++eps) {
                    u64 er = 0, eb = 0; for (int q = 0; q < no; ++q) { if ((eps >> q) & 1) er |= 1ULL << oth[q]; else eb |= 1ULL << oth[q]; }
                    vr[a].push_back(T.empty() ? 0 : T[Rp | er]); vb[a].push_back(T.empty() ? 0 : T[Bp | eb]);
                }
            }
            // every combination of words
            vector<int> idx(nm, 0);
            while (true) {
                int R = bR, B = bB;
                for (int a = 0; a < nm; ++a) { R = max(R, vr[a][idx[a]]); B = max(B, vb[a][idx[a]]); }
                ++epsChecked;
                if (R + B < K) { printf("FAIL: pattern R=%llx B=%llx M=%x pair %d\n", Rp, Bp, Mb, R + B); return 1; }
                worst = min(worst, R + B);
                int a = 0; while (a < nm && ++idx[a] == (1 << others[a])) { idx[a] = 0; ++a; }
                if (a == nm) break;
            }
        }
    }
    printf("m=%d K=%d band=", m, K); for (int j : band) printf("%d ", j);
    printf(": %ld certificates (%ld translates), %lld patterns, %lld settled by pivots (%lld word choices), least pair %d\n",
           ncert, ntrans, configs, viaPivot, epsChecked, worst);
    printf("PASS: every 2-colouring of 2^[%d] has a red and a blue sublattice with at least %d members in total\n", m, K);
    return 0;
}
