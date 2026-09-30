# Erdős Problem 1183: monochromatic union-closed families

Paper, code and Lean 4 formalisation for
[Erdős Problem 1183](https://www.erdosproblems.com/1183) (Erdős–Ulam).

**Zenodo:** [10.5281/zenodo.23050880](https://doi.org/10.5281/zenodo.23050880)
(v1.0.0; [10.5281/zenodo.23050879](https://doi.org/10.5281/zenodo.23050879)
covers all versions).

**Authors:** Deep Bhattacharjee (ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)),
Priyabrata Mandal (ORCID [0000-0001-6472-6239](https://orcid.org/0000-0001-6472-6239)),
Ushashi Bhattacharya (ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914)).

Let `f(n)` (resp. `F(n)`) be the largest `m` such that every 2-colouring of the
subsets of `{1,…,n}` contains a monochromatic family of `m` sets closed under
union and intersection (resp. under union only).

## Status of the two questions

| Question on erdosproblems.com | Status here | Lean |
|---|---|---|
| `F(n) ≥ n^{ω(n)}` for some `ω(n) → ∞` | **Proved**: `F(n) ≥ c_t n^{t+1}` for every `t ≥ 1` | `first_conjecture`, `pow_le_mul_bigF`, `bigF_superpolynomial` |
| `F(n) < (1+o(1))^n` | **Proved**: `F(n) ≤ Σ_{j<d} C(n,j)` whenever `2^d > nd+2`, so `F(n) ≤ n^{(1+o(1)) log₂ n}` | `second_conjecture`, `bigF_le_sum_choose` |
| Both together | **Proved** | `erdos_1183 : FirstConjecture ∧ SecondConjecture` |
| Estimate `f(n)` | `⌈(n+1)/2⌉ ≤ f(n) < 12 n (log₂(n+2))²`, so `f(n) = n^{1+o(1)}`; `f(n) = ⌈(n+1)/2⌉` for `n ≤ 10` (SAT) | lower bound only: `half_le_smallF` |

`FirstConjecture` and `SecondConjecture` are stated in `lean/Erdos1183/Main.lean`
exactly as on the problem page:

```lean
def FirstConjecture : Prop :=
  ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧ ∀ n : ℕ, (n : ℝ) ^ ω n ≤ bigF n

def SecondConjecture : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 1 ≤ n → (bigF n : ℝ) < (1 + ε n) ^ n
```

`#print axioms Erdos1183.erdos_1183` reports only `propext`, `Classical.choice`
and `Quot.sound`.

## Layout

- `paper/` — LaTeX source (`Erdos.tex`, class `aomart`) and PDF.
  - `paper/figures/` — TikZ sources of the seven figures, with PDF and PNG
    renderings; `build.sh name` rebuilds one figure (after the paper has been
    compiled, so that its cross-references resolve).
- `lean/` — Lake project (Lean 4.34.1, Mathlib v4.34.1).
  - `Erdos1183/Basic.lean`: definitions of `f(n)` and `F(n)`; the counting argument;
    `bigF_le_sum_choose`; the trivial lower bound.
  - `Erdos1183/Asymptotic.lean`: `bigF_le_explicit`, `bigF_subexponential`.
  - `Erdos1183/Cube.lean`: cubes, the shape-invariance count, and the
    supersaturated Hales–Jewett lemma (`exists_good_pattern`).
  - `Erdos1183/Chain.lean`: block chains laid out in slots and the slice count
    (`card_goodSizes`).
  - `Erdos1183/Lower.lean`: gluing, double counting, and `pow_le_mul_bigF`.
  - `Erdos1183/Main.lean`: `FirstConjecture`, `SecondConjecture`, `erdos_1183`.
  - `Check.lean`: `#print axioms` for the main theorems.
- `code/` — Python/PySAT programs, witnesses and logs for the small values of
  `f(n)` and `F(n)`.
- `submission/` — draft note for erdosproblems.com.
- `.zenodo.json`, `CITATION.cff` — archival metadata.

## Building

```sh
cd lean
lake exe cache get          # download prebuilt Mathlib
lake build
lake env lean Check.lean    # prints axioms: propext, Classical.choice, Quot.sound

cd ../paper
pdflatex Erdos.tex && pdflatex Erdos.tex
```

## Credits

Claude (Anthropic) assisted with the coding.

## License

Paper and data: CC BY 4.0.
