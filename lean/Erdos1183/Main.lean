import Erdos1183.Lower
import Erdos1183.Asymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem 1183: both conjectures

`F(n)` (`bigF n`) is the largest `k` such that every 2-colouring of the subsets of an `n`-set
has a monochromatic union-closed family of `k` sets. Erdős asked whether
`F(n) ≥ n^{ω(n)}` for some `ω(n) → ∞` (`FirstConjecture`), and whether
`F(n) < (1 + o(1))^n` (`SecondConjecture`). Both hold (`erdos_1183`).
-/

open Filter Topology Finset

namespace Erdos1183

open scoped Classical

/-- `F(n) ≥ 1`. -/
lemma one_le_bigF (n : ℕ) : 1 ≤ bigF n :=
  le_trans (by omega) (half_le_smallF.trans smallF_le_bigF)

/-- `F(n) < 2^n` for `n ≥ 1`: colour the empty set alone. -/
lemma bigF_lt_two_pow {n : ℕ} (hn : 1 ≤ n) : bigF n < 2 ^ n := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hle : bigF n ≤ 2 ^ n - 1 := by
    rw [bigF_le_iff]
    refine ⟨fun S => decide (S = ∅), fun 𝓕 _ hM => ?_⟩
    by_cases h0 : ∅ ∈ 𝓕
    · have hsub : 𝓕 ⊆ {∅} := by
        intro A hA
        have := hM A hA ∅ h0
        simp only [decide_true, decide_eq_true_eq] at this
        simp [this]
      calc #𝓕 ≤ #({∅} : Finset (Finset (Fin n))) := card_le_card hsub
        _ = 1 := card_singleton _
        _ ≤ 2 ^ n - 1 := by omega
    · have hsub : 𝓕 ⊆ univ.erase ∅ := fun A hA =>
        mem_erase.2 ⟨fun h => h0 (h ▸ hA), mem_univ _⟩
      calc #𝓕 ≤ #((univ : Finset (Finset (Fin n))).erase ∅) := card_le_card hsub
        _ = 2 ^ n - 1 := by
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset, Fintype.card_fin]
  omega

/-- **Superpolynomial growth.** For every fixed `c`, `F(n) > n^c` for all large `n`. -/
theorem bigF_superpolynomial (c : ℕ) : ∀ᶠ n : ℕ in atTop, n ^ c < bigF n := by
  obtain ⟨M, hM0, K, hK0, hbound⟩ := pow_le_mul_bigF (c + 1) (by omega)
  set L := 2 * M * (c + 2) with hL
  rw [eventually_atTop]
  refine ⟨2 * M * (K * L ^ c + c + 1) + 1, fun n hn => ?_⟩
  set x := (n - 1) / M with hx
  set s := x / 2 with hs
  set w := s + 1 - (c + 1) with hw
  have hx_ge : 2 * (K * L ^ c + c + 1) ≤ x := by
    rw [hx, Nat.le_div_iff_mul_le hM0]
    have : 2 * M * (K * L ^ c + c + 1) + 1 ≤ n := hn
    have : 2 * (K * L ^ c + c + 1) * M = 2 * M * (K * L ^ c + c + 1) := by ring
    omega
  have hw1 : K * L ^ c + 1 ≤ w := by omega
  have hwpos : 1 ≤ w := by omega
  have hn_le : n ≤ L * w := by
    have h1 : n - 1 < M * (x + 1) := Nat.lt_mul_div_succ _ hM0
    have h2 : x + 1 ≤ 2 * (w + c + 1) := by omega
    have h3 : 2 * (w + c + 1) ≤ 2 * (c + 2) * w := by nlinarith
    have h4 : M * (x + 1) ≤ M * (2 * (c + 2) * w) :=
      Nat.mul_le_mul_left _ (h2.trans h3)
    have h5 : M * (2 * (c + 2) * w) = L * w := by rw [hL]; ring
    omega
  have hwc : 0 < w ^ c := pow_pos hwpos _
  have key : K * n ^ c < K * bigF n := by
    calc K * n ^ c ≤ K * (L * w) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn_le _)
      _ = (K * L ^ c) * w ^ c := by rw [mul_pow, ← mul_assoc]
      _ < w * w ^ c := Nat.mul_lt_mul_of_pos_right (by omega) hwc
      _ = w ^ (c + 1) := by ring
      _ ≤ w ^ (c + 1 + 1) := Nat.pow_le_pow_right hwpos (by omega)
      _ ≤ K * bigF n := hbound n (by omega)
  exact Nat.lt_of_mul_lt_mul_left key

/-- **Erdős's first conjecture** for Problem 1183, as stated on erdosproblems.com:
`F(n) ≥ n^{ω(n)}` for some `ω(n) → ∞`. -/
def FirstConjecture : Prop :=
  ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧ ∀ n : ℕ, (n : ℝ) ^ ω n ≤ bigF n

/-- **Erdős's second conjecture** for Problem 1183, as stated on erdosproblems.com:
`F(n) < (1 + o(1))^n`. -/
def SecondConjecture : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 1 ≤ n → (bigF n : ℝ) < (1 + ε n) ^ n

/-- The first conjecture with an integer-valued `ω`. -/
theorem first_conjecture_nat :
    ∃ ω : ℕ → ℕ, Tendsto ω atTop atTop ∧ ∀ n : ℕ, n ^ ω n ≤ bigF n := by
  refine ⟨fun n => Nat.findGreatest (fun c => n ^ c ≤ bigF n) n, ?_, fun n => ?_⟩
  · rw [tendsto_atTop]
    intro c
    filter_upwards [bigF_superpolynomial c, eventually_ge_atTop c] with n h1 h2
    exact Nat.le_findGreatest h2 h1.le
  · exact Nat.findGreatest_spec (P := fun c => n ^ c ≤ bigF n) (Nat.zero_le n)
      (by simpa using one_le_bigF n)

theorem first_conjecture : FirstConjecture := by
  obtain ⟨ω, hω, hle⟩ := first_conjecture_nat
  refine ⟨fun n => (ω n : ℝ), tendsto_natCast_atTop_atTop.comp hω, fun n => ?_⟩
  rw [Real.rpow_natCast]
  exact_mod_cast hle n

theorem second_conjecture : SecondConjecture := by
  set k : ℕ → ℕ := fun n =>
    Nat.findGreatest (fun k => (bigF n : ℝ) < (1 + 1 / ((k : ℝ) + 1)) ^ n) n with hk
  have hkt : Tendsto k atTop atTop := by
    rw [tendsto_atTop]
    intro c
    have hc : (0 : ℝ) < 1 / ((c : ℝ) + 1) := by positivity
    filter_upwards [bigF_subexponential _ hc, eventually_ge_atTop c] with n h1 h2
    exact Nat.le_findGreatest h2 h1
  refine ⟨fun n => 1 / ((k n : ℝ) + 1),
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hkt, fun n hn => ?_⟩
  refine Nat.findGreatest_spec
    (P := fun k => (bigF n : ℝ) < (1 + 1 / ((k : ℝ) + 1)) ^ n) (Nat.zero_le n) ?_
  have := bigF_lt_two_pow hn
  have h2 : ((bigF n : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast this
  simpa [one_add_one_eq_two] using h2

/-- **Erdős Problem 1183.** Both conjectures hold. -/
theorem erdos_1183 : FirstConjecture ∧ SecondConjecture :=
  ⟨first_conjecture, second_conjecture⟩

end Erdos1183
