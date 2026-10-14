# Write lean/Erdos1183/Window20Data.lean from leandata.pkl.
import pickle, sys
G, items = pickle.load(open('leandata.pkl', 'rb'))
def tree(idx, shift):
    # idx: list of 1-based gadget indices whose low bits (below `shift`) agree
    if len(idx) == 1:
        t, Y, lm, cnt = G[idx[0] - 1]
        return "(.leaf ⟨%d, %d, %d, [%s]⟩)" % (t, lm, cnt, ", ".join(map(str, Y)))
    l = [i for i in idx if not (i >> shift) & 1]; r = [i for i in idx if (i >> shift) & 1]
    sl = tree(l, shift + 1) if l else ".nil"; sr = tree(r, shift + 1) if r else ".nil"
    return "(.node %s %s)" % (sl, sr)
out = []
out.append("""import Erdos1183.Window20Defs

/-!
# Data for the size colourings of `2^{[19]}`

`gadgets` holds %d sublattices of cubes `2^{[t]}`, `t ≤ 19`, as lists of bit masks, in a binary
tree indexed by the bits of the index (lowest bit first). `tree20` is a preorder description of a
binary tree of prefixes of words `g 0, g 1, …, g 19` with `g 0 = false`: an entry `0` is an inner
node (the next level is `false`, then `true`), and an entry `x + 1` is a leaf settled by the code
`x` (see `leafOK`). Both are produced by `generate/window20/make_data.sh`.
-/

namespace Erdos1183.W20

set_option maxRecDepth 100000
""" % len(G))
D = 5
def top(idx, shift):
    # the tree above depth D, with the subtrees at depth D named gsub_b (b = the low D bits)
    if shift == D:
        return "gsub_%d" % (idx[0] & ((1 << D) - 1))
    l = [i for i in idx if not (i >> shift) & 1]; r = [i for i in idx if (i >> shift) & 1]
    assert l and r
    return "(.node %s %s)" % (top(l, shift + 1), top(r, shift + 1))
allidx = list(range(1, len(G) + 1))
for b in range(1 << D):
    idx = [i for i in allidx if i & ((1 << D) - 1) == b]
    out.append("/-- The sublattices whose index is %d modulo %d. -/" % (b, 1 << D))
    out.append("def gsub_%d : GTree :=" % b)
    out.append("  " + tree(idx, D))
    out.append("")
out.append("/-- The sublattices used by the leaves, indexed by the bits of the index, lowest first. -/")
out.append("def gadgets : GTree :=")
out.append("  " + top(allidx, 0))
out.append("")
CH = 1000
chunks = [items[i:i + CH] for i in range(0, len(items), CH)]
for k, c in enumerate(chunks):
    out.append("/-- Part %d of the preorder list. -/" % (k + 1))
    out.append("def tree20_%d : List ℕ := [%s]" % (k + 1, ", ".join(map(str, c))))
    out.append("")
out.append("/-- The preorder description of the prefix tree. -/")
out.append("def tree20 : List ℕ := " + " ++ ".join("tree20_%d" % (k + 1) for k in range(len(chunks))))
out.append("")
out.append("end Erdos1183.W20")
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
print(len(chunks), 'chunks')
