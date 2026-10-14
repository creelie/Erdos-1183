# Resolving Erdős–Ulam Monochromatic Union-Closed Family Conjectures

Paper and Lean 4 formalisation for
[Erdős Problem 1183](https://www.erdosproblems.com/1183).

**Zenodo:** [10.5281/zenodo.23288724](https://doi.org/10.5281/zenodo.23288724)
(v2.1.1; v2.1.0 is [10.5281/zenodo.23188241](https://doi.org/10.5281/zenodo.23188241), and
[10.5281/zenodo.23050879](https://doi.org/10.5281/zenodo.23050879) covers all versions).

**Authors:** Deep Bhattacharjee (ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)),
Priyabrata Mandal (ORCID [0000-0001-6472-6239](https://orcid.org/0000-0001-6472-6239)),
Ushashi Bhattacharya (ORCID [0009-0002-2254-3914](https://orcid.org/0009-0002-2254-3914)).

For a `k`-colouring of the subsets of `[n] = {1,…,n}`, let `F_k(n)` be the least,
over all colourings, of the size of the largest monochromatic union-closed family,
and `F = F_2`. Let `f(n)` be the same for 2-colourings and families closed under
union and intersection (sublattices).

## Results

Every statement below is proved in Lean with no `sorry`; `lean/Check.lean` prints
the axioms of 58 theorems, and each uses only `propext`, `Classical.choice` and
`Quot.sound` (four finite checks, `certs_ok`, `cover_ok`, `gadgets_ok` and
`tree20_ok`, use only `propext`). The one result of the paper that is not proved
in full in Lean, the bound `f(n) ≥ 11n/20`, is described after the table.

| Statement | Lean |
|---|---|
| First conjecture: `F(n) ≥ n^{ω(n)}` for some `ω(n) → ∞` | `first_conjecture` |
| Second conjecture: `F(n) < (1 + ε(n))^n` for some `ε(n) → 0` (first proved by P. Chojecki, [18 March 2026](https://www.ulam.ai/research/erdos1183.pdf), as `F(n) ≤ n^{log₂ n + O(log log n)}`) | `second_conjecture` |
| Both together, as stated on erdosproblems.com | `erdos_1183 : FirstConjecture ∧ SecondConjecture` |
| `n^{t+1} ≤ k^{2^t+1} t^t (4M²)^{t+1} F_k(n)` with `M = t² k^{2^t}` | `bigFk_lower_explicit` |
| `F(n) ≥ n^t` once `n ≥ 2^{(t+2)² 2^t}` | `pow_le_bigF` |
| `F(n) ≥ n^{ℓ − 2 log₂(ℓ+2) − 1}`, `ℓ = log₂ log₂ n` | `rpow_loglog_le_bigF` |
| `F(n) ≤ Σ_{j<d} C(n,j)` whenever `2^d > nd + 2` | `bigF_le_sum_choose` |
| `F(n) ≤ (log₂n + log₂log₂n + 3) n^{log₂n + log₂log₂n + 2}` | `bigF_le_loglog_real` |
| Both conjectures for any number of colours | `erdos_1183_colours` |
| At most `(m+1)^{2n}` nonempty sublattices of `2^[n]` with at most `m` members | `card_sublattices_le_pow` |
| Every 2-colouring of `2^[11]` has a red and a blue sublattice with 13 members in total | `splits_window` |
| `⌈(n+1+q)/2⌉ ≤ f(n) ≤ min(n² + n + 1, 2n(L+K+3) + L + K + 4)`, `q = ⌊(n+1)/12⌋`, `L = ⌊log₂n⌋ + 1`, `K = ⌊log₂L⌋ + 1` | `smallF_ge_window`, `smallF_le_sq`, `smallF_le_log` |
| `f(n) > ⌈(n+1)/2⌉` for odd `n ≥ 11` and for `n ≥ 23` | `half_lt_smallF` |
| Every 2-colouring of `2^[19]` in which sets of the same size have the same colour has a red and a blue sublattice with 22 members in total | `W20.splits_card19` |
| Hilbert's lemma with window `t² k^{2^t}`; many Hilbert cubes on one sequence | `hilbert_window`, `hilbert_cubes` |
| Progressions of sizes, van der Waerden, Howorka's theorem | `ap_family`, `ap_lattice`, `exists_vdW`, `howorka` |
| Random colouring and the counting criterion | `sum_maxUC_ge`, `sum_maxUC_ge_pow`, `bigF_lt_of_count` |
| `U(n,N) ≥ 2^{N−1}` for `n ≥ 206` and `1 ≤ N ≤ 2^{n/4}`, so the counting criterion gives no bound on `F(n)` below `2^{n/4}`; the answer to Question 9.2 is negative for every `C` (first shown for `n = 6r` in the [trureturing](https://github.com/the-omega-institute/trureturing) repository, commit `c0bb36b`, 9 October 2026) | `choose_choose_le_ucCount`, `two_pow_le_ucCount`, `two_pow_le_ucCount_of_pow_four`, `count_question_false` |

The two conjectures are stated in `lean/Erdos1183/Main.lean` in the form of the
problem page:

```lean
def FirstConjecture : Prop :=
  ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧ ∀ n : ℕ, (n : ℝ) ^ ω n ≤ bigF n

def SecondConjecture : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 1 ≤ n → (bigF n : ℝ) < (1 + ε n) ^ n
```

### Twenty levels: `f(n) ≥ 11n/20` (computer check, partial Lean)

Theorem 7.6 of the paper: write `n + 1 = 20q + r` with `0 ≤ r ≤ 19` and put
`e = 1` if `r ≥ 12`, else `e = 0`. Every 2-colouring of `2^[n]` has a red and a
blue sublattice with `n + 1 + 2q + e` members in total, so
`f(n) ≥ ⌈(n + 1 + 2q + e)/2⌉ ≥ 11n/20`. This improves `13n/24` and is larger
than the bound of the table for `n = 20`, `n = 22` and every `n ≥ 110`.

The proof stacks windows of twenty levels, and the window (Lemma 7.7: every
2-colouring of `2^[19]` has a red and a blue sublattice with 22 members in
total) is reduced by hand to a finite check over `2^16 · 3^4 = 5,308,416`
patterns. The check is carried out as follows.

- Lean checks only the colourings by size, which are the patterns without mixed
  levels (`W20.splits_card19`, 826 sublattices and a tree of 6,495 leaves,
  evaluated in the kernel).
- The whole lemma, including the patterns with mixed levels, is checked by four
  independent programs in C, C++, Python and Julia (`checks/window20/`), from
  an explicit list of 63,272 sublattices of `2^[19]` (`certs_19_22.txt`). The
  same programs check the twelve-level window from `certs_11.txt`. All four
  report the same counts.
- `sh checks/window20/run_checks.sh` runs the four programs on both lists,
  checks that each program rejects three corrupted lists, and builds the Lean
  development.

The reduction itself (a mixed level outside `{8, …, 11}` or a pivot whose cubes
are not coloured by size gives 22 directly) is proved in the paper and is not
formalised.

### Open

The exact order of `log F(n) / log n`, between `(1 − o(1)) log₂ log₂ n` and
`(1 + o(1)) log₂ n`, remains open, and so does the exact order of `f(n)`,
between `11n/20` and `(2 + o(1)) n log₂ n` (Section 9 of the paper). Counting
all union-closed families cannot settle the first: `U(n,N) ≥ 2^{N−1}` for
every `N ≤ 2^{n/4}` once `n ≥ 206` (Proposition 5.5).

## Layout

- `paper/`: LaTeX source (`Erdos.tex`, class `amsart`) and PDF; it compiles with pdfLaTeX (three runs) or LuaLaTeX.
  - `paper/figures/`: TikZ sources of the nine figures, with PDF and PNG
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
  - `Lattice.lean`: the lattice function `f` and the bound `f(n) ≤ n² + n + 1`.
  - `LatticeCount.lean`: counting sublattices point by point and `f(n) ≤ (2 + o(1)) n log₂ n`.
  - `LatticeCerts.lean`: 294 explicit sublattices of `2^[11]`, checked in the kernel, covering the colourings by size.
  - `LatticeLower.lean`: windows of twelve levels and `f(n) ≥ ⌈(n + 1 + ⌊(n+1)/12⌋)/2⌉`.
  - `Window20Defs.lean`, `Window20Data.lean`, `Window20Gadgets.lean`, `Window20.lean`: the colourings by size of `2^[19]` (`W20.splits_card19`); the data file is written by `lean/generate/window20/make_data.sh` from `checks/window20/certs_19_22.txt`.
  - `Random.lean`: the random colouring and the counting criterion.
  - `CountFails.lean`: `U(n,N) ≥ 2^{N−1}` for `N ≤ 2^{n/4}`; the counting question has a negative answer.
  - `Check.lean`: `#print axioms` for the main theorems.
- `checks/window20/`: the lists of sublattices for the windows of twelve and twenty
  levels, the four checkers (`check_window.c`, `check_window.cpp`,
  `check_window.py`, `check_window.jl`), the runner `run_checks.sh`, and in
  `search/` the SAT-based search that produced the lists (needs PySAT).
- `submission/`: draft note for erdosproblems.com.
- `.zenodo.json`, `CITATION.cff`: archival metadata.

## Building

```sh
cd lean
lake exe cache get          # download prebuilt Mathlib
lake build
lake env lean Check.lean    # prints axioms: propext, Classical.choice, Quot.sound

cd ..
sh checks/window20/run_checks.sh   # four checkers, corrupted lists, Lean build

cd ../paper
pdflatex Erdos.tex && pdflatex Erdos.tex && pdflatex Erdos.tex
```

## Credits

Claude (Anthropic) assisted with the coding.

## License

Paper: CC BY 4.0.
