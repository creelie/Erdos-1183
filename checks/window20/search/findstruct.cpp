// Pivot model.  An adjacent pair S (red), T (blue) at the mixed level k, U = S & T,
// W = S | T; the cubes 2^U and [W, top] are coloured by size (words given).
// A sublattice may use: members at pure levels of its colour (no constraint);
// members at mixed levels j < k whose lower-cube colour is c ("low"), all inside U;
// at most one member at level k (S for red, T for blue); members at mixed levels
// j > k whose upper-cube colour is c ("high"), all containing W.  Realisable iff
// level(join of lows) <= k-1, level(meet of highs) >= k+1, join(lows) <= D_k <= meet(highs)
// and join(lows) <= meet(highs).
#include <cstdint>
#include <vector>
using u64 = uint64_t;
extern "C" int find_bad_pivot(u64 P, u64 L, u64 H, int kpiv, int n, int s, int* lev_out);
static u64 gP, gL, gH; static int gk, gn, gs, gb;
static int resN; static int resLev[512];
static u64 dn[64]; static int resK; static int resB; static u64 resMM[512];
static int wt[64];
struct D { u64 mm; int w; };
static int weightOf(u64 mask) { int s = 0; while (mask) { int i = __builtin_ctzll(mask); s += wt[i]; mask &= mask - 1; } return s; }
struct St { u64 JL; bool anyL; u64 MH; bool anyH; bool hasK; u64 DK; };
static bool addMember(St& st, u64 mm, int lev) {
    if ((gP >> lev) & 1) return true;
    if (lev == gk) { if (st.hasK) return false; st.hasK = true; st.DK = mm; }
    else if (lev < gk && ((gL >> lev) & 1)) { st.JL |= mm; st.anyL = true; }
    else if (lev > gk && ((gH >> lev) & 1)) { st.MH &= mm; st.anyH = true; }
    else return false;
    if (st.anyL && gb + weightOf(st.JL) > gk - 1) return false;
    if (st.anyH && gb + weightOf(st.MH) < gk + 1) return false;
    if ((st.JL & ~st.MH) != 0) return false;
    if (st.hasK && ((st.JL & ~st.DK) != 0 || (st.DK & ~st.MH) != 0)) return false;
    return true;
}
static bool dfs(std::vector<D>& downs, int k, int total, St st, int lastp, int lastw, u64 lastbit) {
    int nd = downs.size();
    if (nd >= gs + 1) {
        resN = nd; resK = k; resB = gb; for (int j = 0; j < nd; ++j) { resLev[j] = gb + downs[j].w; resMM[j] = downs[j].mm; } return true;
    }
    for (int qi = 0; qi < nd; ++qi) {
        u64 qm = downs[qi].mm;
        int nu = 0;
        for (int j = 0; j < nd; ++j) if ((downs[j].mm & qm) == qm) ++nu;
        if (nd + nu > 2 * gs + 1) continue;
        int psize = __builtin_popcountll(qm) + 1;
        for (int wp = 1; wp <= gn - gb - total; ++wp) {
            if (k > 0 && !(qm & lastbit) && (psize < lastp || (psize == lastp && wp < lastw))) continue;
            u64 nb = (u64)1 << k;
            wt[k] = wp; dn[k] = qm;
            St s2 = st; bool ok = true;
            for (int j = 0; j < nd && ok; ++j) {
                if ((downs[j].mm & qm) != qm) continue;
                ok = addMember(s2, downs[j].mm | nb, gb + downs[j].w + wp);
            }
            if (!ok) continue;
            size_t old = downs.size();
            for (int j = 0; j < nd; ++j)
                if ((downs[j].mm & qm) == qm) downs.push_back({downs[j].mm | nb, downs[j].w + wp});
            if (dfs(downs, k + 1, total + wp, s2, psize, wp, nb)) return true;
            downs.resize(old);
        }
    }
    return false;
}
// Output: out[0] = base b, out[1] = number of poset elements E, then E pairs (weight, strict-down mask
// as two 32-bit halves), then the member downset masks (two halves each).  Returns the member count.
extern "C" int find_struct(u64 P, u64 L, u64 H, int kpiv, int n, int s, long long* out) {
    int lev[512];
    int cnt = find_bad_pivot(P, L, H, kpiv, n, s, lev);
    if (!cnt) return 0;
    int t = 0; out[t++] = resB; out[t++] = resK;
    for (int i = 0; i < resK; ++i) { out[t++] = wt[i]; out[t++] = (long long)dn[i]; }
    for (int j = 0; j < resN; ++j) out[t++] = (long long)resMM[j];
    return cnt;
}
extern "C" int find_bad_pivot(u64 P, u64 L, u64 H, int kpiv, int n, int s, int* lev_out) {
    gP = P; gL = L; gH = H; gk = kpiv; gn = n; gs = s;
    for (int b = 0; b <= n; ++b) {
        gb = b;
        St st{0, false, ~(u64)0, false, false, 0};
        if (!addMember(st, 0, b)) continue;
        std::vector<D> downs; downs.reserve(512); downs.push_back({0, 0});
        if (dfs(downs, 0, 0, st, 0, 0, 0)) {
            for (int j = 0; j < resN; ++j) lev_out[j] = resLev[j];
            return resN;
        }
    }
    return 0;
}
