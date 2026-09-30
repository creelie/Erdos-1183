# Draft note for erdosproblems.com, Problem 1183

*To be posted by the authors as a comment on the problem page or sent to Thomas
Bloom. Fill in the DOI once the Zenodo record is published.*

---

**Progress on the second question (upper bound for F(n)).**

In D. Bhattacharjee, P. Mandal and U. Bhattacharya, *Monochromatic
union-closed families in the Boolean lattice* (2026), DOI: 10.5281/zenodo.XXXXXXX,
we show that for every n ≥ 1 and every integer d with 2^d > nd + 2,

  F(n) ≤ Σ_{j<d} C(n, j).

Proof sketch: colour 2^[n] uniformly at random. Call a d-tuple (A_1, …, A_d) bad
if each A_i has a private element (an element in A_i and in no other A_j) and all
2^d − 1 nonempty unions have the same colour. Private elements make these unions
distinct, so a fixed tuple is bad with probability 2^{2−2^d}. There are at most
2^{nd} tuples, so some colouring has no bad tuple. In that colouring a
monochromatic union-closed family cannot shatter a d-set (the witnesses for
the singletons of a shattered set form an independent system whose unions stay
in the family), so its VC-dimension is < d and Sauer–Shelah gives the bound.

Taking d ≈ log₂ n + log₂ log₂ n + O(1) gives F(n) ≤ n^{(1+o(1)) log₂ n}, so
F(n) < (1 + o(1))^n. This answers the second part of the question in the
affirmative.

The bound F(n) ≤ Σ_{j<d} C(n, j) (under 2^d > nd + 2), the statement
"for every ε > 0, F(n) < (1+ε)^n for all large n", and the trivial bound
⌈(n+1)/2⌉ ≤ f(n) ≤ F(n) are formalized in Lean 4 / Mathlib, with no `sorry`
and only the standard axioms: https://github.com/creelie/erdos-1183 (directory
`lean/`).

**What remains open.** The first question, whether F(n) ≥ n^{ω(n)} with
ω(n) → ∞, is not resolved; we know of no lower bound for general colourings
better than ⌈(n+1)/2⌉. A random colouring has, in expectation, monochromatic
union-closed families of size n^{(1+o(1)) log₂ log₂ n}, so random colourings
cannot give a polynomial upper bound. The order of magnitude of f(n) is also open;
we show f(n) < 12 n (log₂(n+2))² and compute f(n) = ⌈(n+1)/2⌉ for n ≤ 10
(SAT computation, not formalized).
