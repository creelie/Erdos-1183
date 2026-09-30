import Erdos1183.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős Problem 1183: `F(n) < (1 + ε)^n` for every `ε > 0` and all large `n`

Taking `d = 2 (⌊log₂ n⌋ + 1)` in `bigF_le_sum_choose` gives
`F(n) ≤ d · n^d = exp(O((log n)^2))`, which is `(1 + o(1))^n`.
This gives Erdős's second conjecture for Problem 1183; the statement in the form used on
erdosproblems.com is `SecondConjecture` in `Erdos1183.Main`.
-/

open Filter Finset Real

namespace Erdos1183

/-- The choice `d = 2 (⌊log₂ n⌋ + 1)` satisfies `n d + 2 < 2 ^ d` for `n ≥ 2`. -/
lemma choice_d {n : ℕ} (hn : 2 ≤ n) :
    n * (2 * (Nat.log 2 n + 1)) + 2 < 2 ^ (2 * (Nat.log 2 n + 1)) := by
  set L := Nat.log 2 n with hL
  have hk : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hL1 : 1 ≤ L := Nat.log_pos (by norm_num) hn
  have hLt : L < 2 ^ L := Nat.lt_two_pow_self
  have h4 : 4 ≤ 2 ^ (L + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2k : 2 * (L + 1) ≤ 2 ^ (L + 1) := by rw [pow_succ]; omega
  rw [show 2 * (L + 1) = (L + 1) + (L + 1) by ring, pow_add]
  rw [show (L + 1) + (L + 1) = 2 * (L + 1) by ring]
  generalize 2 ^ (L + 1) = P at hk h4 h2k ⊢
  nlinarith

lemma sum_choose_le (n d : ℕ) (hn : 1 ≤ n) : ∑ k ∈ range d, n.choose k ≤ d * n ^ d := by
  calc ∑ k ∈ range d, n.choose k ≤ ∑ _k ∈ range d, n ^ d :=
        sum_le_sum fun k hk =>
          (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right hn (mem_range.1 hk).le)
    _ = d * n ^ d := by rw [sum_const, card_range, smul_eq_mul]

/-- Explicit form: for `n ≥ 2`, `F(n) ≤ d · n^d` with `d = 2 (⌊log₂ n⌋ + 1)`. -/
theorem bigF_le_explicit {n : ℕ} (hn : 2 ≤ n) :
    bigF n ≤ (2 * (Nat.log 2 n + 1)) * n ^ (2 * (Nat.log 2 n + 1)) :=
  (bigF_le_sum_choose (choice_d hn)).trans (sum_choose_le _ _ (by omega))

/-- **Erdős's second conjecture (Problem 1183).** For every `ε > 0`,
`F(n) < (1 + ε)^n` for all sufficiently large `n`; i.e. `F(n) < (1 + o(1))^n`. -/
theorem bigF_subexponential :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (bigF n : ℝ) < (1 + ε) ^ n := by
  intro ε hε
  set c := Real.log (1 + ε) with hc
  have hc0 : 0 < c := Real.log_pos (by linarith)
  have h1 := (isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < c / 16 by positivity)
  have h2 := (isLittleO_pow_log_id_atTop (n := 1)).bound (show (0 : ℝ) < c / 16 by positivity)
  have h3 : ∀ᶠ x : ℝ in atTop, 16 / c < x := eventually_gt_atTop _
  have h4 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x := eventually_ge_atTop _
  have hnat := tendsto_natCast_atTop_atTop.eventually (h1.and (h2.and (h3.and h4)))
  filter_upwards [hnat] with n ⟨hn1, hn2, hn3, hn4⟩
  have hn : 2 ≤ n := by exact_mod_cast hn4
  set L := Real.log n with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  simp only [id, Real.norm_eq_abs, pow_one, abs_of_nonneg hL0, abs_of_pos hnpos,
    abs_of_nonneg (sq_nonneg L)] at hn1 hn2
  have hcn : 16 < n * c := (div_lt_iff₀ hc0).1 hn3
  -- `⌊log₂ n⌋ ≤ 2 log n`
  set m := Nat.log 2 n with hm
  have hm_le : (m : ℝ) ≤ 2 * L := by
    have hpow : ((2 : ℕ) ^ m : ℕ) ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hpowR : (2 : ℝ) ^ m ≤ n := by exact_mod_cast hpow
    have hlog : (m : ℝ) * Real.log 2 ≤ L := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpowR
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at this ⊢
      linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  set d := 2 * (m + 1) with hd
  have hdR : (d : ℝ) = 2 * ((m : ℝ) + 1) := by rw [hd]; push_cast; ring
  have hdpos : (0 : ℝ) < d := by rw [hdR]; positivity
  have hbound : (bigF n : ℝ) ≤ (d : ℝ) * (n : ℝ) ^ d := by
    exact_mod_cast bigF_le_explicit hn
  refine hbound.trans_lt ?_
  have hlhs : 0 < (d : ℝ) * (n : ℝ) ^ d := by positivity
  have hrhs : 0 < (1 + ε) ^ n := by positivity
  rw [← Real.log_lt_log_iff hlhs hrhs, Real.log_mul hdpos.ne' (by positivity), Real.log_pow,
    Real.log_pow, ← hLdef, ← hc]
  have hlogd : Real.log d ≤ d - 1 := Real.log_le_sub_one_of_pos hdpos
  have hdL : (d : ℝ) ≤ 4 * L + 2 := by rw [hdR]; linarith
  have hprod : (d : ℝ) * (1 + L) ≤ (4 * L + 2) * (1 + L) :=
    mul_le_mul_of_nonneg_right hdL (by linarith)
  nlinarith

end Erdos1183
