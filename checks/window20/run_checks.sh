#!/bin/sh
# Checks of the windows of the lattice function (Lemmas "Windows" and "Twenty levels").
#
# 1. The four independent programs (C, C++, Python with numpy, Julia) read the lists of
#    sublattices certs_11.txt (every 2-colouring of 2^[11] has a red-blue pair of size 13)
#    and certs_19_22.txt (every 2-colouring of 2^[19] has a red-blue pair of size 22) and
#    run through every case of the reduction in the proof of the twenty-level lemma.
# 2. Three corrupted lists must be rejected by all four programs: a target of 23 instead of
#    22, the pivot sublattices removed, and a member removed from a sublattice.
# 3. The Lean development is built and its axioms are printed; it contains the check of the
#    colourings by size of 2^[19] (Erdos1183.W20.splits_card19).
#
# Usage: sh checks/window20/run_checks.sh [--no-lean]
# Needs cc, c++, python3 with numpy, julia and, for step 3, lake (elan).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT INT TERM

for tool in "${CC:-cc}" "${CXX:-c++}" python3 julia; do
  command -v "$tool" >/dev/null 2>&1 || { echo "missing tool: $tool"; exit 2; }
done
python3 -c 'import numpy' 2>/dev/null || { echo "missing python module: numpy"; exit 2; }

"${CC:-cc}" -O2 -o "$work/check_c" "$here/check_window.c"
"${CXX:-c++}" -O2 -std=c++17 -o "$work/check_cpp" "$here/check_window.cpp"

run_one() {
  # run_one prog certfile: prints the report of one program; succeeds if it passes
  case $1 in
    c) out=$("$work/check_c" "$2") || true ;;
    cpp) out=$("$work/check_cpp" "$2") || true ;;
    py) out=$(python3 "$here/check_window.py" "$2") || true ;;
    jl) out=$(julia "$here/check_window.jl" "$2") || true ;;
  esac
  printf '[%s] %s\n' "$1" "$out"
  printf '%s\n' "$out" | grep -q '^PASS'
}

echo "== certificates"
for cert in certs_11.txt certs_19_22.txt; do
  echo "-- $cert"
  for prog in c cpp py jl; do
    run_one $prog "$here/$cert" || { echo "FAILED: $prog on $cert"; exit 1; }
  done
done

echo "== corrupted lists (each must be rejected)"
sed '1s/K=22/K=23/' "$here/certs_19_22.txt" > "$work/mut_target.txt"
grep -v '^[0-9]' "$here/certs_19_22.txt" > "$work/mut_pivots.txt"
awk 'NR == 3 { $NF = ""; sub(/ +$/, "") } { print }' "$here/certs_19_22.txt" > "$work/mut_member.txt"
for mut in mut_target mut_pivots mut_member; do
  echo "-- $mut"
  for prog in c cpp py jl; do
    if run_one $prog "$work/$mut.txt"; then echo "NOT REJECTED: $prog on $mut"; exit 1; fi
  done
done

if [ "${1:-}" = "--no-lean" ]; then
  echo "== Lean skipped"
else
  echo "== Lean"
  cd "$root/lean"
  lake build
  lake env lean Check.lean > "$work/axioms.txt"
  grep 'W20' "$work/axioms.txt"
  if grep -q sorryAx "$work/axioms.txt"; then echo "sorryAx found"; exit 1; fi
fi
echo "ALL CHECKS PASSED"
