# Resolving Erdős–Ulam Monochromatic Union-Closed Family Conjectures

Paper and Lean 4 formalisation for
[Erdős Problem 1183](https://www.erdosproblems.com/1183).

**Zenodo:** [10.5281/zenodo.23050879](https://doi.org/10.5281/zenodo.23050879)
(all versions).

**Authors:** Deep Bhattacharjee (ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)),
Priyabrata Mandal (ORCID [0000-0001-6472-6239](https://orcid.org/0000-0001-6472-6239)),
Ushashi Bhattacharya (ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914)).

For a `k`-colouring of the subsets of `[n] = {1,…,n}`, let `F_k(n)` be the least,
over all colourings, of the size of the largest monochromatic union-closed family,
and `F = F_2`. Let `f(n)` be the same for 2-colourings and families closed under
union and intersection (sublattices).

## Results

Every statement below is proved in Lean with no `sorry`; `lean/Check.lean` prints
the axioms of 45 theorems, and each uses only `propext`, `Classical.choice` and
`Quot.sound`.

| Statement | Lean |
|---|---|
| First conjecture: `F(n) ≥ n^{ω(n)}` for some `ω(n) → ∞` | `first_conjecture` |
| Second conjecture: `F(n) < (1 + ε(n))^n` for some `ε(n) → 0` | `second_conjecture` |
| Both together, as stated on erdosproblems.com | `erdos_1183 : FirstConjecture ∧ SecondConjecture` |
| `n^{t+1} ≤ k^{2^t+1} t^t (4M²)^{t+1} F_k(n)` with `M = t² k^{2^t}` | `bigFk_lower_explicit` |
| `F(n) ≥ n^t` once `n ≥ 2^{(t+2)² 2^t}` | `pow_le_bigF` |
| `F(n) ≥ n^{ℓ − 2 log₂(ℓ+2) − 1}`, `ℓ = log₂ log₂ n` | `rpow_loglog_le_bigF` |
| `F(n) ≤ Σ_{j<d} C(n,j)` whenever `2^d > nd + 2` | `bigF_le_sum_choose` |
| `F(n) ≤ (log₂n + log₂log₂n + 3) n^{log₂n + log₂log₂n + 2}` | `bigF_le_loglog_real` |
| Both conjectures for any number of colours | `erdos_1183_colours` |
| `⌈(n+1)/2⌉ ≤ f(n) ≤ min(n² + n + 1, nL(3L+2) + 2n + 3L + 3)`, `L = ⌊log₂n⌋ + 1` | `half_le_smallF`, `smallF_le_sq`, `smallF_le_log` |
| Hilbert's lemma with window `t² k^{2^t}`; many Hilbert cubes on one sequence | `hilbert_window`, `hilbert_cubes` |
| Progressions of sizes, van der Waerden, Howorka's theorem | `ap_family`, `ap_lattice`, `exists_vdW`, `howorka` |
| Random colouring and the counting criterion | `sum_maxUC_ge`, `sum_maxUC_ge_pow`, `bigF_lt_of_count` |

The two conjectures are stated in `lean/Erdos1183/Main.lean` in the form of the
problem page:

```lean
def FirstConjecture : Prop :=
  ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧ ∀ n : ℕ, (n : ℝ) ^ ω n ≤ bigF n

def SecondConjecture : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 1 ≤ n → (bigF n : ℝ) < (1 + ε n) ^ n
```

The exact order of `log F(n) / log n`, between `(1 − o(1)) log₂ log₂ n` and
`(1 + o(1)) log₂ n`, remains open (Section 9 of the paper).

## Layout

- `paper/`: LaTeX source (`Erdos.tex`, class `aomart`) and PDF.
  - `paper/figures/`: TikZ sources of the eight figures, with PDF and PNG
    renderings; `build.sh name` rebuilds one figure after the paper has been
    compiled, so that its cross-references resolve.
- `lean/`: Lake project (Lean 4.34.1, Mathlib v4.34.1).
  - `Basic.lean`: definitions of `f`, `F`; the trivial bounds; the Sauer–Shelah upper bound.
  - `Asymptotic.lean`, `Explicit.lean`: explicit and asymptotic forms of both bounds.
  - `Cube.lean`: cubes and the count of orderings that make a cube monochromatic.
  - `Box.lean`: the box inequality and supersaturation.
  - `Chain.lean`: block chains and the slice count.
  - `Lower.lean`: gluing and double counting.
  - `Main.lean`: `FirstConjecture`, `SecondConjecture`, `erdos_1183`.
  - `Colours.lean`: any number of colours.
  - `Hilbert.lean`, `Howorka.lean`: cardinality colourings, Hilbert cubes, progressions.
  - `Lattice.lean`: the lattice function `f`.
  - `Random.lean`: the random colouring and the counting criterion.
  - `Check.lean`: `#print axioms` for the main theorems.
- `submission/`: draft note for erdosproblems.com.
- `.zenodo.json`, `CITATION.cff`: archival metadata.

## Building

```sh
cd lean
lake exe cache get          # download prebuilt Mathlib
lake build
lake env lean Check.lean    # prints axioms: propext, Classical.choice, Quot.sound

cd ../paper
pdflatex Erdos.tex && pdflatex Erdos.tex && pdflatex Erdos.tex
```

## Credits

Claude (Anthropic) assisted with the coding.

## License

Paper: CC BY 4.0.
