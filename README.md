# Erdős Problem 1183: monochromatic union-closed families

Paper, code and Lean 4 formalization for
[Erdős Problem 1183](https://www.erdosproblems.com/1183) (Erdős–Ulam).

**Authors:** Deep Bhattacharjee (ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)),
Priyabrata Mandal (ORCID [0000-0001-6472-6239](https://orcid.org/0000-0001-6472-6239)),
Ushashi Bhattacharya (ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914)).

Let `f(n)` (resp. `F(n)`) be the largest `m` such that every 2-colouring of the
subsets of `{1,…,n}` contains a monochromatic family of `m` sets closed under
union and intersection (resp. under union only).

## Status of the two questions

| Question on erdosproblems.com | Status here | Lean |
|---|---|---|
| `F(n) < (1+o(1))^n` | **Proved**: `F(n) ≤ Σ_{j<d} C(n,j)` whenever `2^d > nd+2`, so `F(n) ≤ n^{(1+o(1)) log₂ n}` | `second_conjecture`, `bigF_le_sum_choose` |
| `F(n) ≥ n^{ω(n)}` with `ω(n) → ∞` | **Open**; stated but not proved | `FirstConjecture` (a definition only) |
| Estimate `f(n)` | Open; `⌈(n+1)/2⌉ ≤ f(n) < 12 n (log₂(n+2))²`, and `f(n) = ⌈(n+1)/2⌉` for `n ≤ 10` (SAT) | lower bound only: `half_le_smallF` |

## Layout

- `paper/` — LaTeX source and PDF.
- `lean/` — Lake project (Lean 4.34.1, Mathlib v4.34.1).
  - `Erdos1183/Basic.lean`: definitions of `f(n)`, `F(n)`; the counting argument;
    `bigF_le_sum_choose`; the trivial lower bound.
  - `Erdos1183/Asymptotic.lean`: `bigF_le_explicit`, `second_conjecture`,
    and the statement `FirstConjecture`.
  - `Check.lean`: `#print axioms` for the main theorems.
- `code/` — Python/PySAT programs and logs for the small values of `f(n)`, `F(n)`.
- `submission/` — draft note for erdosproblems.com.
- `.zenodo.json`, `CITATION.cff` — archival metadata.

## Building the Lean proof

```sh
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean Check.lean   # prints axioms: propext, Classical.choice, Quot.sound
```

## License

Paper and data: CC BY 4.0.
