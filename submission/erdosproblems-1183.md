# Draft note for erdosproblems.com, Problem 1183

*To be posted by the authors as a comment on the problem page or sent to Thomas
Bloom.*

---

**Partial result: the two specific questions about F(n) are answered in the
affirmative, for any number of colours, with a complete Lean formalisation. The
estimates of f(n) and F(n) are improved, but their exact orders remain open.**

D. Bhattacharjee, P. Mandal and U. Bhattacharya, *Resolving Erdős–Ulam
Monochromatic Union-Closed Family Conjectures* (2026),
DOI: [10.5281/zenodo.23094057](https://doi.org/10.5281/zenodo.23094057).

**First question.** For all k ≥ 2 and t ≥ 1, with M = t² k^(2^t), every
k-colouring of the subsets of [n] has a monochromatic union-closed family with at
least n^(t+1) / (k^(2^t+1) t^t (4M²)^(t+1)) members. For two colours this gives
F(n) ≥ n^t once log₂ n ≥ (t+2)² 2^t, and hence F(n) ≥ n^(ω(n)) for every n ≥ 2
with ω(n) = ℓ − 2 log₂(ℓ+2) − 1, ℓ = log₂ log₂ n.

Sketch. Take disjoint nonempty blocks Y_1, …, Y_m and C_j = Y_1 ∪ … ∪ Y_j. For
j > s and A ⊆ {1, …, s} the sets C_j \ Y_B (B ⊆ A) form a cube Q(j, A). If
j ≤ j′ and B, B′ ⊆ {1, …, s}, then (C_j \ Y_B) ∪ (C_j′ \ Y_B′) = C_j′ \ Y_(B∩B′),
so the cubes Q(j, A) of one colour together form a union-closed family, with at
least as many members as there are cubes. It remains to make a fixed proportion
of the roughly m^(t+1) cubes with |A| = t monochromatic. Permute the ground set
by a random σ and choose each block size at random in {1, …, M}; after the
permutation, the chance that a cube is monochromatic depends only on its shape.
A Cauchy–Schwarz inequality for products over the 2^t vertices of a box, applied
to t disjoint chains of length L = t k^(2^t), shows that for every r some shape
with base size between r and r + M is monochromatic with probability at least
k^(−2^t). The shape of Q(j, A) is controlled by the t+1 sizes of Y_j and Y_a
(a ∈ A), which can be tuned independently of the others, and averaging gives one
chain in which a proportion k^(−2^t) M^(−t−1) of the cubes is monochromatic.

**Second question.** For every n ≥ 1 and every d with 2^d > nd + 2,
F(n) ≤ Σ_(j<d) C(n, j). With d = ⌊log₂ n⌋ + ⌊log₂ ⌊log₂ n⌋⌋ + 3 this gives
F(n) ≤ n^((1+o(1)) log₂ n), so F(n) < (1 + o(1))^n.

Sketch. Colour 2^[n] at random. Call a d-tuple bad if each set has a private
element and all 2^d − 1 nonempty unions have one colour; the unions are
distinct, so a tuple is bad with probability 2^(2−2^d), and there are at most
2^(nd) tuples. In a colouring with no bad tuple, a monochromatic union-closed
family cannot shatter a d-set, and the Sauer–Shelah lemma gives the bound.

**Formal verification.** Both statements, in the form on the problem page
(∃ ω → ∞ with n^(ω(n)) ≤ F(n) for all n; ∃ ε → 0 with F(n) < (1 + ε(n))^n
for all n ≥ 1), their conjunction, the k-colour versions and every other result
of the paper are proved in Lean 4 with Mathlib, with no `sorry` and only the
standard axioms. The formalisation is included in the Zenodo record.

**Also in the paper.** ⌈(n+1)/2⌉ ≤ f(n) ≤ min(n² + n + 1, nL(3L+2) + 2n + 3L + 3)
with L = ⌊log₂ n⌋ + 1, so f(n) = O(n (log n)²) while F(n) grows faster than
every power of n. For colourings by cardinality the argument becomes a statement
about monochromatic Hilbert cubes hanging from the partial sums of one bounded
sequence, and Howorka's result follows from van der Waerden's theorem with the
explicit bound C(⌊n/(2W)⌋ + p − 1, p − 1), where W = W_k(p). The exact order of
log F(n) / log n, between (1 − o(1)) log₂ log₂ n and (1 + o(1)) log₂ n, remains
open; the paper reduces the matching upper bound to counting union-closed
families.
