#!/bin/sh
# Rebuilds lean/Erdos1183/Window20Data.lean from checks/window20/certs_19_22.txt.
#   gadgets.py  the sublattices of the list used without mixed levels, one per pair
#               (dimension t, set of member sizes), moved into a cube 2^[t]
#   tree.py     the binary tree of beginnings of words g(0) ... g(L-1), g(0) blue, cut at the
#               first L at which the red and the blue gains add up to 2
#   cover.py    the gain of each sublattice at each leaf, for both colours
#   greedy.py   a small set of sublattices that settles every leaf
#   mkdata.py   the leaf codes in preorder
#   emit_lean.py  the Lean file
# Usage: sh lean/generate/window20/make_data.sh [output]   (needs python3 with numpy)
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=${1:-$root/lean/Erdos1183/Window20Data.lean}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM
cd "$work"
python3 "$here/gadgets.py" "$root/checks/window20/certs_19_22.txt"
python3 "$here/tree.py"
python3 "$here/cover.py"
python3 "$here/greedy.py"
python3 "$here/mkdata.py"
python3 "$here/emit_lean.py" "$out"
