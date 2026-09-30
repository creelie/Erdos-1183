Code accompanying
  "Monochromatic Union-Closed Families in the Boolean Lattice"
  Deep Bhattacharjee, EGSPL, Bhubaneswar, 2026

REQUIREMENTS
  Python 3.8 or later, python-sat (pip install python-sat).  All SAT calls
  use CaDiCaL 1.5.3 through PySAT.

FILES
  small_values.py   exact values of f(n) and F(n) by counterexample-guided
                    SAT (outer solver) with a branch-and-bound search for
                    monochromatic closed families (inner check).
                    Usage: python3 small_values.py NMAX
                    Times (one core): f(8) 35 s, f(9) 20 min, F(6) 1 s,
                    F(7) 18 min.
  witnesses.py      produces the extremal colouring (witness) for a given
                    (n, both, value) and verifies it with an INDEPENDENT
                    SAT encoding (cardinality constraint), independent of
                    the branch-and-bound search.
                    Usage: python3 witnesses.py n both value
                    (both = 1 for f, 0 for F).  Output: witness_{f|F}_n.txt,
                    a 0/1 string indexed by the bitmask of the subset.
  verify_g.py       independent SAT verification that the cardinality
                    colourings g_3,...,g_9 listed in the paper have no
                    monochromatic sublattice with more than ceil((n+1)/2)
                    members.
  brute_small.py    exhaustive check of f(n), F(n) for n <= 4 over all
                    2^(2^n) colourings and all closed families, no SAT.
  sizebased.py      search for cardinality colourings attaining f(n),
                    n = 3..9 (adds the clauses x_S <-> x_S' for |S| = |S'|).
  f_card_search_sat.py
                    enumerates the cardinality colourings g passing the
                    necessary conditions of Proposition 6.1 and checks each
                    with the independent SAT encoding; used for n = 9, 10.
                    Usage: python3 f_card_search_sat.py n
  witness_*.txt     witnesses produced by witnesses.py.
  *.log             outputs of the runs reported in the paper.

RESULTS
  n     : 1 2 3 4 5 6 7 8 9 10
  f(n)  : 1 2 2 3 3 4 4 5 5 6
  F(n)  : 1 2 2 3 4 5 7
