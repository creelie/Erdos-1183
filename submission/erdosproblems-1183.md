# Draft note for erdosproblems.com, Problem 1183

*To be posted by the authors as a comment on the problem page or sent to Thomas
Bloom. Fill in the DOI once the Zenodo record is published.*

---

**Both questions are answered in the affirmative.**

D. Bhattacharjee, P. Mandal and U. Bhattacharya, *On the Erdős–Ulam problem for
monochromatic union-closed families* (2026), DOI: 10.5281/zenodo.XXXXXXX.

**First question.** For every t ≥ 1 there is c_t > 0 with F(n) ≥ c_t n^{t+1}
for all n. Hence F(n) ≥ n^{ω(n)} for some ω(n) → ∞.

Sketch. Take disjoint nonempty blocks Y_1, …, Y_m and C_j = Y_1 ∪ … ∪ Y_j. For
j > s and A ⊆ {1, …, s} the sets C_j \ Y_B (B ⊆ A) form a cube Q(j, A). If
j ≤ j′ and B, B′ ⊆ {1, …, s}, then (C_j \ Y_B) ∪ (C_j′ \ Y_B′) = C_j′ \ Y_{B∩B′},
so the union of any set of cubes Q(j, A) that are monochromatic in one colour is
union-closed, and it has at least as many members as there are cubes. It
remains to make a fixed proportion of the roughly m^{t+1} cubes with |A| = t
monochromatic. Permute the ground set by a random σ and choose each block size
at random in {1, …, M}. After a random permutation, the chance that a cube is
monochromatic depends only on its shape (base size; generator sizes). The
two-letter multidimensional Hales–Jewett theorem, applied once per permutation,
together with pigeonhole over the at most (t+2)^M patterns, shows that for every
base size r some shape with base in [r, r+M] is monochromatic with probability
at least (t+2)^{-M}. The shape of Q(j, A) is controlled by the t+1 sizes of Y_j
and Y_a (a ∈ A), which can be tuned independently of the others, so each cube
gets a good shape for at least a fraction M^{-t-1} of the size vectors. Averaging
gives one chain in which a fraction (t+2)^{-M} M^{-t-1} of the cubes is
monochromatic.

**Second question.** For every n ≥ 1 and every d with 2^d > nd + 2,
F(n) ≤ Σ_{j<d} C(n, j); hence F(n) ≤ n^{(1+o(1)) log₂ n} and
F(n) < (1 + o(1))^n.

Sketch. Colour 2^[n] at random. Call a d-tuple bad if each set has a private
element and all 2^d − 1 nonempty unions have one colour; the unions are
distinct, so a tuple is bad with probability 2^{2−2^d}, and there are at most
2^{nd} tuples. In a colouring with no bad tuple, a monochromatic union-closed
family cannot shatter a d-set, and Sauer–Shelah gives the bound.

**Formal verification.** Both statements, in the form on the problem page
(∃ ω → ∞ with n^{ω(n)} ≤ F(n) for all n; ∃ ε → 0 with F(n) < (1 + ε(n))^n
for all n ≥ 1), and their conjunction are proved in Lean 4 with Mathlib, with
no `sorry` and only the standard axioms. The formalisation is included in the
Zenodo record.

**Also in the paper.** ⌈(n+1)/2⌉ ≤ f(n) < 12 n (log₂(n+2))², so f(n) = n^{1+o(1)}
and the two functions have very different orders. For colourings by
cardinality, the argument becomes a statement about monochromatic Hilbert cubes
hanging from the partial sums of one bounded sequence, and Howorka's result
also follows directly from van der Waerden's theorem. Exact values: f(n) =
⌈(n+1)/2⌉ for n ≤ 10, and F(1), …, F(7) = 1, 2, 2, 3, 4, 5, 7 (SAT computation,
not formalised).
