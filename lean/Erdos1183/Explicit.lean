import Erdos1183.Main
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Explicit forms of the bounds

* `pow_le_pow_mul_choose`: `s^t ≤ t^t C(s, t)` for `t ≤ s`.
* `bigF_lower_explicit`: `n^{t+1} ≤ 2^{2^t+1} t^t (4 M^2)^{t+1} F(n)` for `n ≥ 1`, where
  `M = boxM t = t^2 2^{2^t}`; this is `F(n) ≥ c_t n^{t+1}`.
* `pow_le_bigF`: `F(n) ≥ n^t` as soon as `n ≥ 2^{(t+2)^2 2^t}`.
* `rpow_loglog_le_bigF`: `F(n) ≥ n^{ℓ - 2 log₂(ℓ + 2) - 1}` with `ℓ = log₂ log₂ n`, for `n ≥ 2`.
* `first_conjecture_explicit`: the first conjecture with this explicit `ω`.
-/

open Finset Filter

namespace Erdos1183

open scoped Classical

/-- `(s/t)^t ≤ C(s, t)`, in the form `s^t ≤ t^t C(s, t)`. -/
theorem pow_le_pow_mul_choose : ∀ t s : ℕ, t ≤ s → s ^ t ≤ t ^ t * s.choose t
  | 0, s, _ => by simp
  | t + 1, s, h => by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hs' : t ≤ s' := by omega
    have ih := pow_le_pow_mul_choose t s' hs'
    have hch : (s' + 1) * s'.choose t = (s' + 1).choose (t + 1) * (t + 1) :=
      Nat.add_one_mul_choose_eq s' t
    have h1 : (s' + 1) ^ t * t ^ t ≤ (t + 1) ^ t * s' ^ t := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith) t
    have htt : 0 < t ^ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp
      · exact pow_pos ht t
    have h2 : (s' + 1) ^ t ≤ (t + 1) ^ t * s'.choose t := by
      have : (s' + 1) ^ t * t ^ t ≤ ((t + 1) ^ t * s'.choose t) * t ^ t := by
        calc (s' + 1) ^ t * t ^ t ≤ (t + 1) ^ t * s' ^ t := h1
          _ ≤ (t + 1) ^ t * (t ^ t * s'.choose t) := Nat.mul_le_mul_left _ ih
          _ = ((t + 1) ^ t * s'.choose t) * t ^ t := by ring
      exact Nat.le_of_mul_le_mul_right this htt
    calc (s' + 1) ^ (t + 1) = (s' + 1) ^ t * (s' + 1) := pow_succ _ _
      _ ≤ (t + 1) ^ t * s'.choose t * (s' + 1) := Nat.mul_le_mul_right _ h2
      _ = (t + 1) ^ t * ((s' + 1) * s'.choose t) := by ring
      _ = (t + 1) ^ t * ((s' + 1).choose (t + 1) * (t + 1)) := by rw [hch]
      _ = (t + 1) ^ (t + 1) * (s' + 1).choose (t + 1) := by ring

lemma two_le_two_pow_two_pow (t : ℕ) : 2 ≤ 2 ^ 2 ^ t := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ 2 ^ t := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

lemma boxM_eq (t : ℕ) : boxM t = t ^ 2 * 2 ^ 2 ^ t := by
  unfold boxM boxL
  ring

lemma succ_le_boxM (t : ℕ) (ht : 1 ≤ t) : t + 1 ≤ boxM t := by
  have h := two_le_two_pow_two_pow t
  rw [boxM_eq]
  nlinarith

/-- **Theorem 1.1, explicit.** For `t ≥ 1` and `n ≥ 1`,
`n^{t+1} ≤ 2^{2^t+1} t^t (4 M^2)^{t+1} F(n)` with `M = t^2 2^{2^t}`. -/
theorem bigF_lower_explicit (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) :
    n ^ (t + 1) ≤ 2 ^ (2 ^ t + 1) * t ^ t * (4 * (t ^ 2 * 2 ^ 2 ^ t) ^ 2) ^ (t + 1) * bigF n := by
  rw [← boxM_eq]
  set M := boxM t with hMdef
  have hMt : t + 1 ≤ M := succ_le_boxM t ht
  have hM0 : 0 < M := by omega
  have hF : 1 ≤ bigF n := one_le_bigF n
  by_cases hsmall : n < 4 * M * (t + 1)
  · have hA : 1 ≤ 2 ^ (2 ^ t + 1) * t ^ t := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc n ^ (t + 1) ≤ (4 * M * (t + 1)) ^ (t + 1) := Nat.pow_le_pow_left hsmall.le _
      _ ≤ (4 * M ^ 2) ^ (t + 1) := Nat.pow_le_pow_left (by nlinarith) _
      _ = 1 * (4 * M ^ 2) ^ (t + 1) * 1 := by ring
      _ ≤ 2 ^ (2 ^ t + 1) * t ^ t * (4 * M ^ 2) ^ (t + 1) * bigF n :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hA) hF
  · push Not at hsmall
    set m := (n - 1) / M with hm
    set s := m / 2 with hs
    have hmn : m * M < n := by
      have : m * M ≤ n - 1 := Nat.div_mul_le_self (n - 1) M
      omega
    have hnm : n ≤ M * (m + 1) := by
      have := Nat.lt_mul_div_succ (n - 1) hM0
      rw [← hm] at this
      omega
    have hms : m ≤ 2 * s + 1 := by omega
    have hs1 : 2 * t + 1 ≤ s := by
      have h1 : M * (4 * (t + 1)) ≤ M * (2 * s + 2) := by
        calc M * (4 * (t + 1)) = 4 * M * (t + 1) := by ring
          _ ≤ n := hsmall
          _ ≤ M * (m + 1) := hnm
          _ ≤ M * (2 * s + 2) := Nat.mul_le_mul_left _ (by omega)
      have := Nat.le_of_mul_le_mul_left h1 hM0
      omega
    have hn4 : n ≤ 4 * M * s := by
      calc n ≤ M * (m + 1) := hnm
        _ ≤ M * (4 * s) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * M * s := by ring
    have hsm : s ≤ m := Nat.div_le_self _ _
    set P : Finset (Fin m × Finset (Fin m)) := (univ.filter fun j : Fin m => s ≤ j.val) ×ˢ
      powersetCard t (univ.filter fun k : Fin m => k.val < s)
    have hP : ∀ x ∈ P, ∀ y ∈ P, ∀ a ∈ y.2, a < x.1 := by
      intro x hx y hy a ha
      simp only [P, mem_product, mem_filter, mem_univ, true_and, mem_powersetCard] at hx hy
      have := hy.2.1 ha
      simp only [mem_filter, mem_univ, true_and] at this
      exact Fin.lt_def.2 (by omega)
    have hPt : ∀ x ∈ P, #x.2 = t := by
      intro x hx
      simp only [P, mem_product, mem_powersetCard] at hx
      exact hx.2.2
    have hbound := card_le_bigF (2 ^ 2 ^ t) ht (fun r χ => exists_good_pattern t ht r χ)
      hmn P hP hPt
    have hcardP : #P = (m - s) * s.choose t := by
      simp only [P, card_product, card_powersetCard, card_filter_le_val,
        card_filter_lt_val m s hsm]
    have hch := pow_le_pow_mul_choose t s (by omega)
    have hsms : s ≤ m - s := by omega
    have h1 : s ^ (t + 1) ≤ t ^ t * (2 * 2 ^ 2 ^ t * M ^ (t + 1) * bigF n) := by
      calc s ^ (t + 1) = s * s ^ t := by ring
        _ ≤ (m - s) * (t ^ t * s.choose t) := Nat.mul_le_mul hsms hch
        _ = t ^ t * #P := by rw [hcardP]; ring
        _ ≤ t ^ t * (2 * 2 ^ 2 ^ t * M ^ (t + 1) * bigF n) := Nat.mul_le_mul_left _ hbound
    calc n ^ (t + 1) ≤ (4 * M * s) ^ (t + 1) := Nat.pow_le_pow_left hn4 _
      _ = (4 * M) ^ (t + 1) * s ^ (t + 1) := by ring
      _ ≤ (4 * M) ^ (t + 1) * (t ^ t * (2 * 2 ^ 2 ^ t * M ^ (t + 1) * bigF n)) :=
          Nat.mul_le_mul_left _ h1
      _ = 2 ^ (2 ^ t + 1) * t ^ t * (4 * M ^ 2) ^ (t + 1) * bigF n := by ring

/-- The constant of `bigF_lower_explicit` is at most `2^{(t+2)^2 2^t}`. -/
theorem lower_const_le (t : ℕ) (ht : 1 ≤ t) :
    2 ^ (2 ^ t + 1) * t ^ t * (4 * (t ^ 2 * 2 ^ 2 ^ t) ^ 2) ^ (t + 1) ≤ 2 ^ ((t + 2) ^ 2 * 2 ^ t) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  set X := 2 ^ (u + 1) with hXdef
  have htu : u + 1 ≤ 2 ^ u := Nat.lt_two_pow_self
  have hX : 2 * u + 2 ≤ X := by rw [hXdef, pow_succ]; omega
  have e1 : (u + 1) ^ (u + 1) ≤ 2 ^ (u * (u + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left htu _
  have e2 : (u + 1) ^ 2 * 2 ^ X ≤ 2 ^ (2 * u + X) := by
    calc (u + 1) ^ 2 * 2 ^ X ≤ (2 ^ u) ^ 2 * 2 ^ X :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left htu 2)
      _ = 2 ^ (2 * u + X) := by ring
  have e3 : 4 * ((u + 1) ^ 2 * 2 ^ X) ^ 2 ≤ 2 ^ (2 + 2 * (2 * u + X)) := by
    calc 4 * ((u + 1) ^ 2 * 2 ^ X) ^ 2 ≤ 4 * (2 ^ (2 * u + X)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e2 2)
      _ = 2 ^ (2 + 2 * (2 * u + X)) := by ring
  have e4 : (4 * ((u + 1) ^ 2 * 2 ^ X) ^ 2) ^ (u + 1 + 1) ≤
      2 ^ ((2 + 2 * (2 * u + X)) * (u + 1 + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left e3 _
  have hexp : X + 1 + u * (u + 1) + (2 + 2 * (2 * u + X)) * (u + 1 + 1) ≤ (u + 1 + 2) ^ 2 * X := by
    have := Nat.mul_le_mul_left ((u + 2) ^ 2) hX
    nlinarith
  calc 2 ^ (X + 1) * (u + 1) ^ (u + 1) * (4 * ((u + 1) ^ 2 * 2 ^ X) ^ 2) ^ (u + 1 + 1)
      ≤ 2 ^ (X + 1) * 2 ^ (u * (u + 1)) * 2 ^ ((2 + 2 * (2 * u + X)) * (u + 1 + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) e4
    _ = 2 ^ (X + 1 + u * (u + 1) + (2 + 2 * (2 * u + X)) * (u + 1 + 1)) := by
        rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ ((u + 1 + 2) ^ 2 * X) := Nat.pow_le_pow_right (by norm_num) hexp

/-- **Explicit rate.** `F(n) ≥ n^t` whenever `n ≥ 2^{(t+2)^2 2^t}`. -/
theorem pow_le_bigF (t : ℕ) (ht : 1 ≤ t) (n : ℕ) (hn : 2 ^ ((t + 2) ^ 2 * 2 ^ t) ≤ n) :
    n ^ t ≤ bigF n := by
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have h := bigF_lower_explicit t ht n hn1
  have hC := lower_const_le t ht
  have key : n * n ^ t ≤ n * bigF n := by
    calc n * n ^ t = n ^ (t + 1) := by ring
      _ ≤ _ := h
      _ ≤ n * bigF n := Nat.mul_le_mul_right _ (hC.trans hn)
  exact Nat.le_of_mul_le_mul_left key hn1

/-- **Corollary 1.3 (i), explicit.** For `n ≥ 2`, with `ℓ = log₂ log₂ n`,
`F(n) ≥ n^{ℓ - 2 log₂(ℓ + 2) - 1}`. -/
theorem rpow_loglog_le_bigF (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (Real.logb 2 (Real.logb 2 n) -
      2 * Real.logb 2 (Real.logb 2 (Real.logb 2 n) + 2) - 1) ≤ bigF n := by
  set ℓ := Real.logb 2 (Real.logb 2 n) with hℓ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hn2
  have hℓ0 : 0 ≤ ℓ := Real.logb_nonneg (by norm_num) hlog1
  have hF1 : (1 : ℝ) ≤ bigF n := by exact_mod_cast one_le_bigF n
  set x := ℓ - 2 * Real.logb 2 (ℓ + 2) with hx
  by_cases hω : x - 1 ≤ 0
  · calc (n : ℝ) ^ (x - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 hω
      _ ≤ bigF n := hF1
  · push Not at hω
    have hx0 : 0 ≤ x := by linarith
    set t := ⌊x⌋₊ with htdef
    have ht1 : 1 ≤ t := Nat.le_floor (by push_cast; linarith)
    have htx : (t : ℝ) ≤ x := Nat.floor_le hx0
    have hxt : x - 1 < t := by have := Nat.lt_floor_add_one x; linarith
    have hL2 : 0 ≤ Real.logb 2 (ℓ + 2) := Real.logb_nonneg (by norm_num) (by linarith)
    have htℓ : (t : ℝ) + 2 ≤ ℓ + 2 := by linarith
    have hlogt : Real.logb 2 ((t : ℝ) + 2) ≤ Real.logb 2 (ℓ + 2) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) htℓ
    set K : ℕ := (t + 2) ^ 2 * 2 ^ t with hK
    have hKpos : (0 : ℝ) < K := by positivity
    have hlogK : Real.logb 2 (K : ℝ) ≤ ℓ := by
      rw [hK]
      push_cast
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      push_cast
      linarith
    have hKlog : (K : ℝ) ≤ Real.logb 2 n := by
      calc (K : ℝ) = 2 ^ Real.logb 2 (K : ℝ) :=
            (Real.rpow_logb (by norm_num) (by norm_num) hKpos).symm
        _ ≤ 2 ^ ℓ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlogK
        _ = Real.logb 2 n := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
    have hNat : 2 ^ K ≤ n := by
      have : (2 : ℝ) ^ (K : ℝ) ≤ n := by
        calc (2 : ℝ) ^ (K : ℝ) ≤ 2 ^ Real.logb 2 n :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hKlog
          _ = n := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
      rw [Real.rpow_natCast] at this
      exact_mod_cast this
    have hpow := pow_le_bigF t ht1 n hNat
    calc (n : ℝ) ^ (x - 1) ≤ (n : ℝ) ^ (t : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hxt.le
      _ = ((n ^ t : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
      _ ≤ bigF n := by exact_mod_cast hpow

/-- The exponent `ω(n) = ℓ - 2 log₂(ℓ + 2) - 1`, `ℓ = log₂ log₂ n`, for `n ≥ 2`. -/
noncomputable def omegaLL (n : ℕ) : ℝ :=
  if 2 ≤ n then
    Real.logb 2 (Real.logb 2 n) - 2 * Real.logb 2 (Real.logb 2 (Real.logb 2 n) + 2) - 1
  else 0

lemma tendsto_sub_two_logb :
    Tendsto (fun x : ℝ => x - 2 * Real.logb 2 (x + 2) - 1) atTop atTop := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_atTop_add_const_right atTop 2 tendsto_id)).bound
    (show (0 : ℝ) < Real.log 2 / 8 by positivity)
  have hlin : Tendsto (fun x : ℝ => x / 2 - 2) atTop atTop := by
    have h2 := (tendsto_id (α := ℝ) (x := atTop)).atTop_div_const (show (0 : ℝ) < 2 by norm_num)
    refine (tendsto_atTop_add_const_right atTop (-2) h2).congr fun x => ?_
    simp [sub_eq_add_neg]
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [h, eventually_ge_atTop 0] with x hx hx0
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hx
  have hx2 : 0 < x + 2 := by linarith
  rw [abs_of_pos hx2] at hx
  have hlog : Real.log (x + 2) ≤ Real.log 2 / 8 * (x + 2) := (le_abs_self _).trans hx
  have hb : 2 * Real.logb 2 (x + 2) ≤ (x + 2) / 4 := by
    rw [Real.logb, mul_div_assoc', div_le_div_iff₀ hlog2 (by norm_num)]
    nlinarith
  linarith

/-- **The first conjecture with an explicit `ω`.** `ω(n) → ∞` and `n^{ω(n)} ≤ F(n)` for all
`n`, where `ω(n) = log₂ log₂ n - 2 log₂(log₂ log₂ n + 2) - 1` for `n ≥ 2`. -/
theorem first_conjecture_explicit :
    Tendsto omegaLL atTop atTop ∧ ∀ n : ℕ, (n : ℝ) ^ omegaLL n ≤ bigF n := by
  constructor
  · have hℓ : Tendsto (fun n : ℕ => Real.logb 2 (Real.logb 2 n)) atTop atTop :=
      (Real.tendsto_logb_atTop (by norm_num)).comp
        ((Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    refine (tendsto_sub_two_logb.comp hℓ).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp [omegaLL, hn]
  · intro n
    by_cases hn : 2 ≤ n
    · simp only [omegaLL, hn, ite_true]
      exact rpow_loglog_le_bigF n hn
    · simp only [omegaLL, hn, ite_false, Real.rpow_zero]
      exact_mod_cast one_le_bigF n

/-! ### The upper bound with `d = log₂ n + log₂ log₂ n + O(1)` -/

/-- `d = ⌊log₂ n⌋ + ⌊log₂ ⌊log₂ n⌋⌋ + 3` satisfies `n d + 2 < 2^d` for `n ≥ 2`. -/
lemma choice_d_loglog {n : ℕ} (hn : 2 ≤ n) :
    n * (Nat.log 2 n + Nat.log 2 (Nat.log 2 n) + 3) + 2 <
      2 ^ (Nat.log 2 n + Nat.log 2 (Nat.log 2 n) + 3) := by
  set a := Nat.log 2 n with ha
  set c := Nat.log 2 a + 1 with hc
  have ha1 : 1 ≤ a := Nat.log_pos (by norm_num) hn
  have hna : n < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hac : a < 2 ^ c := Nat.lt_pow_succ_log_self (by norm_num) a
  have hca : c ≤ a := Nat.log_lt_self 2 (by omega)
  have hsplit : 2 ^ (a + Nat.log 2 a + 3) = 2 ^ (a + 1) * (2 * 2 ^ c) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  rw [hsplit]
  have h1 : (n + 1) * (2 * (a + 1)) ≤ 2 ^ (a + 1) * (2 * 2 ^ c) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : n * (a + Nat.log 2 a + 3) ≤ n * (2 * (a + 1)) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

lemma sum_choose_le_pred (n d : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range d, n.choose k ≤ d * n ^ (d - 1) := by
  calc ∑ k ∈ range d, n.choose k ≤ ∑ _k ∈ range d, n ^ (d - 1) :=
        sum_le_sum fun k hk =>
          (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right hn (by rw [mem_range] at hk; omega))
    _ = d * n ^ (d - 1) := by rw [sum_const, card_range, smul_eq_mul]

/-- **Theorem 1.2, second part.** For `n ≥ 2`, `F(n) ≤ d n^{d-1}` with
`d = ⌊log₂ n⌋ + ⌊log₂ ⌊log₂ n⌋⌋ + 3`. -/
theorem bigF_le_loglog {n : ℕ} (hn : 2 ≤ n) :
    bigF n ≤ (Nat.log 2 n + Nat.log 2 (Nat.log 2 n) + 3) *
      n ^ (Nat.log 2 n + Nat.log 2 (Nat.log 2 n) + 2) :=
  (bigF_le_sum_choose (choice_d_loglog hn)).trans (sum_choose_le_pred n _ (by omega))

/-- The same bound in real form: `F(n) ≤ (L + log₂ L + 3) n^{L + log₂ L + 2}`, `L = log₂ n`. -/
theorem bigF_le_loglog_real {n : ℕ} (hn : 2 ≤ n) :
    (bigF n : ℝ) ≤ (Real.logb 2 n + Real.logb 2 (Real.logb 2 n) + 3) *
      (n : ℝ) ^ (Real.logb 2 n + Real.logb 2 (Real.logb 2 n) + 2) := by
  set a := Nat.log 2 n with ha
  set b := Nat.log 2 a with hb
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have ha1 : 1 ≤ a := Nat.log_pos (by norm_num) hn
  have haR : (a : ℝ) ≤ Real.logb 2 n := by
    have := Real.natLog_le_logb n 2
    simpa using this
  have hbR : (b : ℝ) ≤ Real.logb 2 (Real.logb 2 n) := by
    have h1 : (b : ℝ) ≤ Real.logb 2 a := by
      have := Real.natLog_le_logb a 2
      simpa using this
    have h2 : Real.logb 2 (a : ℝ) ≤ Real.logb 2 (Real.logb 2 n) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast ha1) haR
    linarith
  have hnat := bigF_le_loglog hn
  have hcast : (bigF n : ℝ) ≤ ((a + b + 3 : ℕ) : ℝ) * (n : ℝ) ^ ((a + b + 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hnat
  refine hcast.trans ?_
  push_cast
  have hD : (0 : ℝ) ≤ a + b + 3 := by positivity
  apply mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
    (by positivity) (by linarith)

/-- **Corollary 1.3 (iii).** Any admissible exponent satisfies `ω(n) ≤ (1 + o(1)) log₂ n`. -/
theorem omega_le_of_pow_le (ω : ℕ → ℝ) (hω : ∀ n : ℕ, (n : ℝ) ^ ω n ≤ bigF n) (ε : ℝ)
    (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, ω n ≤ (1 + ε) * Real.logb 2 n := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    linarith
  have hL : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h1 := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < ε * Real.log 2 / 2 by positivity)
  have h2 : ∀ᶠ x : ℝ in atTop, 18 / ε ≤ x ∧ 16 ≤ x :=
    (eventually_ge_atTop _).and (eventually_ge_atTop _)
  filter_upwards [hL.eventually h1, hL.eventually h2, eventually_ge_atTop 2] with n hn1 hn2 hn
  set L := Real.logb 2 n with hLdef
  obtain ⟨hLε, hL16⟩ := hn2
  simp only [id, Real.norm_eq_abs] at hn1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1' : (1 : ℝ) < n := by linarith
  have hpos : (0 : ℝ) < n := by linarith
  have hL0 : 0 < L := by linarith
  rw [abs_of_pos hL0] at hn1
  set l := Real.logb 2 L with hldef
  -- `log₂ L ≤ ε L / 2`, and `log₂ L ≥ 0`
  have hlogL : l ≤ ε * L / 2 := by
    have := (le_abs_self _).trans hn1
    rw [hldef, Real.logb, div_le_iff₀ hlog2]
    nlinarith
  have hl0 : 0 ≤ l := Real.logb_nonneg (by norm_num) (by linarith)
  set D := L + l + 3 with hDdef
  have hD0 : 0 < D := by linarith
  -- `ω(n) ≤ log_n D + D - 1`
  have hE : ω n ≤ Real.logb n D + (D - 1) := by
    have h := (hω n).trans (bigF_le_loglog_real hn)
    rw [← hLdef, ← hldef, show L + l + 2 = D - 1 by rw [hDdef]; ring] at h
    have hrw : (n : ℝ) ^ (Real.logb n D + (D - 1)) = D * (n : ℝ) ^ (D - 1) := by
      rw [Real.rpow_add hpos, Real.rpow_logb hpos (ne_of_gt hn1') hD0]
    rw [← hrw] at h
    exact (Real.rpow_le_rpow_left_iff hn1').1 h
  -- `log_n D ≤ 2 D / L ≤ 3 + ε`
  have hlogn : Real.log n = L * Real.log 2 := by
    rw [hLdef, Real.logb]
    field_simp
  have hlogD : Real.logb n D ≤ 2 * D / L := by
    rw [Real.logb, hlogn, div_le_div_iff₀ (by positivity) hL0]
    have h1 := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hD0) hL0.le
    have h2 : 0 ≤ D * L * (2 * Real.log 2 - 1) :=
      mul_nonneg (mul_pos hD0 hL0).le (by linarith)
    nlinarith
  have h2D : 2 * D / L ≤ 3 + ε := by
    rw [div_le_iff₀ hL0]
    nlinarith
  have hεL : 18 ≤ ε * L := by
    rw [div_le_iff₀ hε] at hLε
    linarith
  have hεL' : 16 * ε ≤ ε * L := by nlinarith
  nlinarith

end Erdos1183
