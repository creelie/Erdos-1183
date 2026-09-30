import Erdos1183.Explicit

/-!
# Any number of colours

For a finite set of colours `κ` with `k = |κ|`, `bigFk κ n` is the least, over all colourings
`Finset (Fin n) → κ`, of the size of the largest monochromatic union-closed family.

* `bigFk_le_bigF`: `F_k(n) ≤ F(n)` for `k ≥ 2`.
* `bigFk_lower_explicit`: `n^{t+1} ≤ k^{2^t+1} t^t (4 M^2)^{t+1} F_k(n)` with `M = t^2 k^{2^t}`.
* `erdos_1183_colours`: both conjectures of Erdős and Ulam hold for `F_k`.
-/

open Finset Filter Topology

namespace Erdos1183

open scoped Classical

/-- `F_κ(n)`: the analogue of `F(n)` for colourings with colour set `κ`. -/
noncomputable def bigFk (κ : Type*) (n : ℕ) : ℕ := ⨅ χ : Finset (Fin n) → κ, maxUC χ

set_option linter.unusedSectionVars false

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}

theorem le_bigFk_iff [Nonempty κ] (m : ℕ) :
    m ≤ bigFk κ n ↔
      ∀ χ : Finset (Fin n) → κ, ∃ 𝓕, UnionClosed 𝓕 ∧ Monochromatic χ 𝓕 ∧ m ≤ #𝓕 := by
  unfold bigFk
  rw [le_ciInf_iff (OrderBot.bddBelow _)]
  simp only [le_maxUC_iff]

theorem bigFk_le_iff [Nonempty κ] (m : ℕ) :
    bigFk κ n ≤ m ↔
      ∃ χ : Finset (Fin n) → κ, ∀ 𝓕, UnionClosed 𝓕 → Monochromatic χ 𝓕 → #𝓕 ≤ m := by
  unfold bigFk
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := ciInf_mem (fun χ : Finset (Fin n) → κ => maxUC χ)
    have hχ' : maxUC χ = ⨅ χ : Finset (Fin n) → κ, maxUC χ := hχ
    refine ⟨χ, (maxUC_le_iff χ m).1 ?_⟩
    rw [hχ']
    exact h
  · rintro ⟨χ, hχ⟩
    exact (ciInf_le (OrderBot.bddBelow _) χ).trans ((maxUC_le_iff χ m).2 hχ)

lemma one_le_bigFk [Nonempty κ] (n : ℕ) : 1 ≤ bigFk κ n := by
  rw [le_bigFk_iff]
  intro χ
  refine ⟨{∅}, ?_, ?_, by simp⟩
  · intro A hA B hB
    simp only [mem_singleton] at hA hB ⊢
    rw [hA, hB, empty_union]
  · intro A hA B hB
    simp only [mem_singleton] at hA hB
    rw [hA, hB]

lemma nonempty_of_two_le (hk : 2 ≤ Fintype.card κ) : Nonempty κ :=
  Fintype.card_pos_iff.1 (by omega)

/-- **More colours cannot help the colouring less.** With `k ≥ 2` colours available, a
`2`-colouring is one of the allowed colourings, so `F_k(n) ≤ F(n)`. -/
theorem bigFk_le_bigF (hk : 2 ≤ Fintype.card κ) (n : ℕ) : bigFk κ n ≤ bigF n := by
  have := nonempty_of_two_le hk
  obtain ⟨e⟩ : Nonempty (Bool ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_bool]; exact hk)
  obtain ⟨χ, hχ⟩ := (bigF_le_iff (n := n) (bigF n)).1 le_rfl
  refine (bigFk_le_iff _).2 ⟨e ∘ χ, fun 𝓕 hU hM => hχ 𝓕 hU fun A hA B hB => ?_⟩
  exact e.injective (hM A hA B hB)

lemma boxM_eq_k (k t : ℕ) : boxM k t = t ^ 2 * k ^ 2 ^ t := by
  unfold boxM boxL
  ring

lemma succ_le_boxM_k (k t : ℕ) (hk : 2 ≤ k) (ht : 1 ≤ t) : t + 1 ≤ boxM k t := by
  have h : 2 ≤ k ^ 2 ^ t :=
    calc 2 ≤ k := hk
      _ = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ 2 ^ t := Nat.pow_le_pow_right (by omega) Nat.one_le_two_pow
  rw [boxM_eq_k]
  nlinarith

/-- **The lower bound for `k` colours, explicit.** For `k ≥ 2`, `t ≥ 1` and `n ≥ 1`,
`n^{t+1} ≤ k^{2^t+1} t^t (4 M^2)^{t+1} F_k(n)` with `M = t^2 k^{2^t}`. -/
theorem bigFk_lower_explicit (hk : 2 ≤ Fintype.card κ) (t : ℕ) (ht : 1 ≤ t) (n : ℕ)
    (hn : 1 ≤ n) :
    n ^ (t + 1) ≤ Fintype.card κ ^ (2 ^ t + 1) * t ^ t *
      (4 * (t ^ 2 * Fintype.card κ ^ 2 ^ t) ^ 2) ^ (t + 1) * bigFk κ n := by
  have := nonempty_of_two_le hk
  set k := Fintype.card κ with hkdef
  rw [← boxM_eq_k]
  set M := boxM k t with hMdef
  have hMt : t + 1 ≤ M := succ_le_boxM_k k t hk ht
  have hM0 : 0 < M := by omega
  have hF : 1 ≤ bigFk κ n := one_le_bigFk n
  have hk0 : 0 < k := by omega
  by_cases hsmall : n < 4 * M * (t + 1)
  · have hA : 1 ≤ k ^ (2 ^ t + 1) * t ^ t := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc n ^ (t + 1) ≤ (4 * M * (t + 1)) ^ (t + 1) := Nat.pow_le_pow_left hsmall.le _
      _ ≤ (4 * M ^ 2) ^ (t + 1) := Nat.pow_le_pow_left (by nlinarith) _
      _ = 1 * (4 * M ^ 2) ^ (t + 1) * 1 := by ring
      _ ≤ k ^ (2 ^ t + 1) * t ^ t * (4 * M ^ 2) ^ (t + 1) * bigFk κ n :=
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
    -- a colouring attaining `F_k(n)`
    obtain ⟨χ, hχ⟩ := (bigFk_le_iff (κ := κ) (n := n) (bigFk κ n)).1 le_rfl
    obtain ⟨𝓕, hU, hMono, h𝓕⟩ := exists_large_family (k ^ 2 ^ t) ht χ
      (fun r => exists_good_pattern hk t ht r χ) hmn P hP hPt
    have hbound : #P ≤ k * k ^ 2 ^ t * M ^ (t + 1) * bigFk κ n :=
      h𝓕.trans (Nat.mul_le_mul_left _ (hχ 𝓕 hU hMono))
    have hcardP : #P = (m - s) * s.choose t := by
      simp only [P, card_product, card_powersetCard, card_filter_le_val,
        card_filter_lt_val m s hsm]
    have hch := pow_le_pow_mul_choose t s (by omega)
    have hsms : s ≤ m - s := by omega
    have h1 : s ^ (t + 1) ≤ t ^ t * (k * k ^ 2 ^ t * M ^ (t + 1) * bigFk κ n) := by
      calc s ^ (t + 1) = s * s ^ t := by ring
        _ ≤ (m - s) * (t ^ t * s.choose t) := Nat.mul_le_mul hsms hch
        _ = t ^ t * #P := by rw [hcardP]; ring
        _ ≤ t ^ t * (k * k ^ 2 ^ t * M ^ (t + 1) * bigFk κ n) := Nat.mul_le_mul_left _ hbound
    calc n ^ (t + 1) ≤ (4 * M * s) ^ (t + 1) := Nat.pow_le_pow_left hn4 _
      _ = (4 * M) ^ (t + 1) * s ^ (t + 1) := by ring
      _ ≤ (4 * M) ^ (t + 1) * (t ^ t * (k * k ^ 2 ^ t * M ^ (t + 1) * bigFk κ n)) :=
          Nat.mul_le_mul_left _ h1
      _ = k ^ (2 ^ t + 1) * t ^ t * (4 * M ^ 2) ^ (t + 1) * bigFk κ n := by ring

/-- For every fixed `c`, `F_k(n) ≥ n^c` for all large `n`. -/
theorem bigFk_superpolynomial (hk : 2 ≤ Fintype.card κ) (c : ℕ) :
    ∀ᶠ n : ℕ in atTop, n ^ c ≤ bigFk κ n := by
  have := nonempty_of_two_le hk
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact Eventually.of_forall fun n => by simpa using one_le_bigFk (κ := κ) n
  set C := Fintype.card κ ^ (2 ^ c + 1) * c ^ c *
    (4 * (c ^ 2 * Fintype.card κ ^ 2 ^ c) ^ 2) ^ (c + 1) with hC
  filter_upwards [eventually_ge_atTop (C + 1)] with n hn
  have h := bigFk_lower_explicit hk c hc n (by omega)
  have key : n * n ^ c ≤ n * bigFk κ n := by
    calc n * n ^ c = n ^ (c + 1) := by ring
      _ ≤ C * bigFk κ n := h
      _ ≤ n * bigFk κ n := Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-- **Both conjectures for `k ≥ 2` colours.** There is `ω(n) → ∞` with `n^{ω(n)} ≤ F_k(n)` for
every `n`, and there is `ε(n) → 0` with `F_k(n) < (1 + ε(n))^n` for every `n ≥ 1`. -/
theorem erdos_1183_colours (hk : 2 ≤ Fintype.card κ) :
    (∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧ ∀ n : ℕ, (n : ℝ) ^ ω n ≤ bigFk κ n) ∧
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ n : ℕ, 1 ≤ n → (bigFk κ n : ℝ) < (1 + ε n) ^ n := by
  have := nonempty_of_two_le hk
  constructor
  · refine ⟨fun n => ((Nat.findGreatest (fun c => n ^ c ≤ bigFk κ n) n : ℕ) : ℝ),
      tendsto_natCast_atTop_atTop.comp ?_, fun n => ?_⟩
    · rw [tendsto_atTop]
      intro c
      filter_upwards [bigFk_superpolynomial hk c, eventually_ge_atTop c] with n h1 h2
      exact Nat.le_findGreatest h2 h1
    · rw [Real.rpow_natCast]
      exact_mod_cast Nat.findGreatest_spec (P := fun c => n ^ c ≤ bigFk κ n) (Nat.zero_le n)
        (by simpa using one_le_bigFk (κ := κ) n)
  · obtain ⟨ε, hε, hlt⟩ := second_conjecture
    refine ⟨ε, hε, fun n hn => lt_of_le_of_lt ?_ (hlt n hn)⟩
    exact_mod_cast bigFk_le_bigF hk n

end Erdos1183
