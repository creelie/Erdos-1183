import Erdos1183.Random
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.IntervalCases

/-!
# The counting criterion gives nothing below `2^{n/4}`

`ucCount n N` is the number `U(n,N)` of union-closed families of `N` subsets of `[n]`. The
criterion `bigF_lt_of_count` gives `F(n) < N` whenever `2 U(n,N) < 2^N`. Here we show that
this never happens for `1 ≤ N ≤ C(n, ⌊n/12⌋)/5`, in particular for `N^4 ≤ 2^n`, once
`n ≥ 206`, so the answer to the question whether `2 U(n,N) < 2^N` for all
`N ≥ n^{C log₂ log₂ n}` and all large `n` is negative for every `C`.

* `choose_choose_le_ucCount`: for `W ⊆ [n]` with `|W| = m`, the families
  `{W \ X : X ∈ L ∪ G}`, with `L` the subsets of `W` of size `< k` and `G` any `g` of the
  `k`-subsets of `W`, are union-closed and pairwise distinct, so
  `C(C(m,k), g) ≤ U(n, S_k(m) + g)` with `S_k(m) = ∑_{j<k} C(m,j)`.
* `two_pow_le_ucCount`: `2^N ≤ 2 U(n,N)` for `n ≥ 206` and `1 ≤ N ≤ C(n,⌊n/12⌋)/5`.
* `two_pow_le_ucCount_of_pow_four`: the same for `n ≥ 206` and `1 ≤ N`, `N^4 ≤ 2^n`.
* `count_question_false`: no constant `C` makes `2 U(n,N) < 2^N` for all large `n` and all
  `N ≥ n^{C log₂ log₂ n}`.
-/

open Finset Filter

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The number `U(n,N)` of union-closed families of `N` subsets of `[n]`. -/
noncomputable def ucCount (n N : ℕ) : ℕ :=
  #(univ.filter fun 𝓕 : Finset (Finset (Fin n)) => UnionClosed 𝓕 ∧ #𝓕 = N)

/-- `S_k(m) = ∑_{j<k} C(m,j)`. -/
def lowSum (m k : ℕ) : ℕ := ∑ j ∈ range k, m.choose j

lemma lowSum_succ (m k : ℕ) : lowSum m (k + 1) = lowSum m k + m.choose k := by
  simp [lowSum, sum_range_succ]

lemma one_le_lowSum {m k : ℕ} (hk : 1 ≤ k) : 1 ≤ lowSum m k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  induction k with
  | zero => simp [lowSum]
  | succ k ih => rw [lowSum_succ]; have := ih (by omega); omega

/-- Pascal's rule for `S_k`: `S_{k+1}(m+1) = S_{k+1}(m) + S_k(m)`. -/
lemma lowSum_pascal (m k : ℕ) : lowSum (m + 1) (k + 1) = lowSum m (k + 1) + lowSum m k := by
  induction k with
  | zero => simp [lowSum]
  | succ k ih =>
    rw [lowSum_succ (m + 1), ih, Nat.choose_succ_succ, lowSum_succ m (k + 1), lowSum_succ m k]
    ring

/-! ### The construction -/

section Construction

variable (W : Finset (Fin n)) (k : ℕ)

/-- The subsets of `W` with fewer than `k` elements. -/
noncomputable def lowSets : Finset (Finset (Fin n)) := W.powerset.filter fun X => #X < k

lemma card_lowSets : #(lowSets W k) = lowSum #W k := by
  have h : lowSets W k = (range k).biUnion fun j => powersetCard j W := by
    ext X
    simp only [lowSets, mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨#X, h2, h1, rfl⟩
    · rintro ⟨j, hj, h1, rfl⟩; exact ⟨h1, hj⟩
  rw [h, card_biUnion]
  · simp [lowSum, card_powersetCard]
  · intro i _ j _ hij
    refine disjoint_left.2 fun X hi hj => hij ?_
    rw [mem_powersetCard] at hi hj
    rw [← hi.2, hj.2]

/-- The family `{W \ X : X ∈ L ∪ G}`. -/
noncomputable def famOf (G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (lowSets W k ∪ G).image fun X => W \ X

variable {W k}

lemma mem_low_union {G : Finset (Finset (Fin n))} (hG : G ⊆ powersetCard k W)
    {X : Finset (Fin n)} (hX : X ∈ lowSets W k ∪ G) : X ⊆ W ∧ #X ≤ k := by
  rcases mem_union.1 hX with h | h
  · obtain ⟨h1, h2⟩ := mem_filter.1 h
    exact ⟨mem_powerset.1 h1, h2.le⟩
  · obtain ⟨h1, h2⟩ := mem_powersetCard.1 (hG h)
    exact ⟨h1, h2.le⟩

lemma unionClosed_famOf {G : Finset (Finset (Fin n))} (hG : G ⊆ powersetCard k W) :
    UnionClosed (famOf W k G) := by
  intro A hA B hB
  obtain ⟨X, hX, rfl⟩ := mem_image.1 hA
  obtain ⟨Y, hY, rfl⟩ := mem_image.1 hB
  refine mem_image.2 ⟨X ∩ Y, ?_, by rw [sdiff_inter_distrib_right]⟩
  by_cases hXY : X = Y
  · subst hXY; rw [inter_self]; exact hX
  obtain ⟨hXW, hXk⟩ := mem_low_union hG hX
  obtain ⟨hYW, hYk⟩ := mem_low_union hG hY
  refine mem_union_left _ (mem_filter.2 ⟨mem_powerset.2 (inter_subset_left.trans hXW), ?_⟩)
  by_cases hX' : #X < k
  · exact (card_le_card inter_subset_left).trans_lt hX'
  by_cases hY' : #Y < k
  · exact (card_le_card inter_subset_right).trans_lt hY'
  have hsub : X ∩ Y ⊂ X := by
    refine ssubset_of_subset_of_ne inter_subset_left fun h => hXY ?_
    have hXsY : X ⊆ Y := by rw [← h]; exact inter_subset_right
    exact eq_of_subset_of_card_le hXsY (by omega)
  exact (card_lt_card hsub).trans_le hXk

lemma injOn_sdiff : Set.InjOn (fun X => W \ X) {X : Finset (Fin n) | X ⊆ W} := by
  intro X hX Y hY h
  have h' : W \ (W \ X) = W \ (W \ Y) := by simp only at h; rw [h]
  rwa [Finset.sdiff_sdiff_eq_self hX, Finset.sdiff_sdiff_eq_self hY] at h'

lemma card_famOf {G : Finset (Finset (Fin n))} (hG : G ⊆ powersetCard k W) :
    #(famOf W k G) = lowSum #W k + #G := by
  rw [famOf, card_image_of_injOn, card_union_of_disjoint, card_lowSets]
  · refine disjoint_left.2 fun X h1 h2 => ?_
    have := (mem_powersetCard.1 (hG h2)).2
    have := (mem_filter.1 h1).2
    omega
  · exact fun X hX Y hY h => injOn_sdiff (mem_low_union hG hX).1 (mem_low_union hG hY).1 h

lemma famOf_injOn :
    Set.InjOn (famOf W k) {G : Finset (Finset (Fin n)) | G ⊆ powersetCard k W} := by
  intro G hG H hH h
  have key : ∀ G : Finset (Finset (Fin n)), G ⊆ powersetCard k W →
      ((famOf W k G).image fun A => W \ A).filter (fun X => #X = k) = G := by
    intro G hG
    ext X
    simp only [famOf, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨A, ⟨Y, hY, rfl⟩, rfl⟩, hk⟩
      rw [Finset.sdiff_sdiff_eq_self (mem_low_union hG hY).1] at hk ⊢
      rcases mem_union.1 hY with h | h
      · exact absurd hk (mem_filter.1 h).2.ne
      · exact h
    · intro hX
      have hXW := (mem_powersetCard.1 (hG hX)).1
      exact ⟨⟨W \ X, ⟨X, mem_union_right _ hX, rfl⟩, Finset.sdiff_sdiff_eq_self hXW⟩,
        (mem_powersetCard.1 (hG hX)).2⟩
  rw [← key G hG, ← key H hH, h]

end Construction

/-- For `|W| = m`, `C(C(m,k), g) ≤ U(n, S_k(m) + g)`. -/
theorem choose_choose_le_ucCount (W : Finset (Fin n)) (k g : ℕ) :
    ((#W).choose k).choose g ≤ ucCount n (lowSum #W k + g) := by
  rw [← card_powersetCard k W, ← card_powersetCard g (powersetCard k W), ucCount]
  refine card_le_card_of_injOn (famOf W k) (fun G hG => ?_) fun G hG H hH h =>
    famOf_injOn (mem_powersetCard.1 (mem_coe.1 hG)).1 (mem_powersetCard.1 (mem_coe.1 hH)).1 h
  have hG' := mem_powersetCard.1 (mem_coe.1 hG)
  refine mem_coe.2 (mem_filter.2 ⟨mem_univ _, unionClosed_famOf hG'.1, ?_⟩)
  rw [card_famOf hG'.1, hG'.2]

/-! ### Arithmetic -/

/-- `a^g ≤ C(M, g)` when `(a+1) g ≤ M + 1`. -/
lemma pow_le_choose_of_mul_le (a M : ℕ) :
    ∀ g, (a + 1) * g ≤ M + 1 → a ^ g ≤ M.choose g
  | 0, _ => by simp
  | g + 1, h => by
    have ih := pow_le_choose_of_mul_le a M g (by nlinarith)
    have hstep := Nat.choose_succ_right_eq M g
    have hag : a * (g + 1) ≤ M - g := by
      have : a * (g + 1) + g ≤ M := by nlinarith
      omega
    have : a ^ (g + 1) * (g + 1) ≤ M.choose (g + 1) * (g + 1) := by
      rw [hstep, pow_succ]
      calc a ^ g * a * (g + 1) = a ^ g * (a * (g + 1)) := by ring
        _ ≤ M.choose g * (M - g) := Nat.mul_le_mul ih hag
    exact Nat.le_of_mul_le_mul_right this (by omega)

/-- One window: if `S ≤ N`, `2S ≤ N + 1` and `5 (N - S) ≤ C(m,k) + 1`, where
`S = S_k(m)` and `m ≤ n`, then `2^N ≤ 2 U(n,N)`. -/
lemma window {m k N : ℕ} (hm : m ≤ n) (h1 : lowSum m k ≤ N) (h2 : 2 * lowSum m k ≤ N + 1)
    (h5 : 5 * (N - lowSum m k) ≤ m.choose k + 1) : 2 ^ N ≤ 2 * ucCount n N := by
  obtain ⟨W, -, hW⟩ := (univ : Finset (Fin n)).exists_subset_card_eq
    (show m ≤ #(univ : Finset (Fin n)) by rw [card_univ, Fintype.card_fin]; exact hm)
  set g := N - lowSum m k with hg
  have hN : N = lowSum #W k + g := by rw [hW]; omega
  have hc := choose_choose_le_ucCount W k g
  rw [← hN, hW] at hc
  have h4 : 4 ^ g ≤ (m.choose k).choose g := pow_le_choose_of_mul_le 4 _ g (by omega)
  calc 2 ^ N ≤ 2 ^ (2 * g + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 * 4 ^ g := by rw [pow_succ, pow_mul, mul_comm]; norm_num
    _ ≤ 2 * ucCount n N := by omega

lemma eight_choose_le {m j k : ℕ} (hj : j < k) (hm : 9 * k ≤ m) :
    8 * m.choose j ≤ m.choose (j + 1) := by
  have hstep := Nat.choose_succ_right_eq m j
  have : 8 * m.choose j * (j + 1) ≤ m.choose (j + 1) * (j + 1) := by
    rw [hstep]
    calc 8 * m.choose j * (j + 1) = m.choose j * (8 * (j + 1)) := by ring
      _ ≤ m.choose j * (m - j) := Nat.mul_le_mul_left _ (by omega)
  exact Nat.le_of_mul_le_mul_right this (by omega)

lemma seven_lowSum_le {m k : ℕ} (hm : 9 * k ≤ m) :
    ∀ j, j ≤ k → 7 * lowSum m j ≤ m.choose j
  | 0, _ => by simp [lowSum]
  | j + 1, hj => by
    have ih := seven_lowSum_le hm j (by omega)
    have h8 := eight_choose_le (show j < k by omega) hm
    rw [lowSum_succ]
    omega

/-- **One level.** For `k ≥ 1` and `9k ≤ m ≤ n`, every `N` with `2 S_k(9k) ≤ N + 1` and
`5 (N - S_k(m)) ≤ C(m,k) + 1` satisfies `2^N ≤ 2 U(n,N)`. -/
lemma level {k : ℕ} (hk : 1 ≤ k) :
    ∀ m, 9 * k ≤ m → m ≤ n → ∀ N, 2 * lowSum (9 * k) k ≤ N + 1 →
      5 * (N - lowSum m k) ≤ m.choose k + 1 → 2 ^ N ≤ 2 * ucCount n N := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro hn N h2 h5
    have := one_le_lowSum (m := 9 * k) hk
    exact window hn (by omega) h2 h5
  | succ m hm ih =>
    intro hn N h2 h5
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hS1 := one_le_lowSum (m := m + 1) hk
    by_cases hc : 2 * lowSum (m + 1) (k + 1) ≤ N + 1
    · exact window hn (by omega) hc h5
    · refine ih (by omega) N h2 ?_
      have hp := lowSum_pascal m k
      have h7 := seven_lowSum_le hm (k + 1) le_rfl
      have h7' := seven_lowSum_le (show 9 * (k + 1) ≤ m by omega) k (by omega)
      have h8 := eight_choose_le (show k < k + 1 by omega) hm
      omega

/-- `C(a,k) n^k ≤ C(n,k) a^k` for `a ≤ n`. -/
lemma choose_mul_pow_le {a : ℕ} (ha : a ≤ n) (k : ℕ) :
    a.choose k * n ^ k ≤ n.choose k * a ^ k := by
  have key : ∀ k, a.descFactorial k * n ^ k ≤ n.descFactorial k * a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
      have hstep : (a - k) * n ≤ (n - k) * a := by
        rcases le_or_gt k a with h | h
        · have hkn : k ≤ n := h.trans ha
          zify [h, hkn]
          nlinarith
        · rw [Nat.sub_eq_zero_of_le h.le]; simp
      calc (a - k) * a.descFactorial k * (n ^ k * n)
          = ((a - k) * n) * (a.descFactorial k * n ^ k) := by ring
        _ ≤ ((n - k) * a) * (n.descFactorial k * a ^ k) := Nat.mul_le_mul hstep ih
        _ = (n - k) * n.descFactorial k * (a ^ k * a) := by ring
  have h := key k
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos k)

lemma eighty_pow_le {k : ℕ} (hk : 1 ≤ k) (hn : 206 ≤ n) (hkn : 12 * (k + 1) ≤ n) :
    80 * (9 * (k + 1)) ^ k ≤ 7 * n ^ k := by
  by_cases h8 : k ≤ 8
  · have h206 : 206 ^ k ≤ n ^ k := Nat.pow_le_pow_left hn k
    have : 80 * (9 * (k + 1)) ^ k ≤ 7 * 206 ^ k := by
      interval_cases k <;> norm_num
    omega
  · have h34 : ∀ j, 9 ≤ j → 80 * 3 ^ j ≤ 7 * 4 ^ j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => norm_num
      | succ j _ ih => rw [pow_succ, pow_succ]; omega
    have hpow : (12 * (k + 1)) ^ k ≤ n ^ k := Nat.pow_le_pow_left hkn k
    calc 80 * (9 * (k + 1)) ^ k = (80 * 3 ^ k) * (3 * (k + 1)) ^ k := by
          rw [show 9 * (k + 1) = 3 * (3 * (k + 1)) by ring, mul_pow, mul_assoc]
      _ ≤ (7 * 4 ^ k) * (3 * (k + 1)) ^ k := Nat.mul_le_mul_right _ (h34 k (by omega))
      _ = 7 * (12 * (k + 1)) ^ k := by
          rw [show 12 * (k + 1) = 4 * (3 * (k + 1)) by ring, mul_pow 4 (3 * (k + 1)) k]; ring
      _ ≤ 7 * n ^ k := Nat.mul_le_mul_left _ hpow

/-- The start of level `k + 1` lies below the end of level `k`. -/
lemma cross {k : ℕ} (hk : 1 ≤ k) (hn : 206 ≤ n) (hkn : 12 * (k + 1) ≤ n) :
    10 * lowSum (9 * (k + 1)) (k + 1) ≤ n.choose k := by
  set a := 9 * (k + 1) with ha
  have h7 := seven_lowSum_le (show 9 * k ≤ a by omega) k le_rfl
  have hcm := choose_mul_pow_le (show a ≤ n by omega) k
  have hp := eighty_pow_le hk hn hkn
  have hnk : 0 < n ^ k := pow_pos (by omega) k
  have h80 : 80 * a.choose k ≤ 7 * n.choose k := by
    have : 80 * a.choose k * n ^ k ≤ 7 * n.choose k * n ^ k := by
      calc 80 * a.choose k * n ^ k = 80 * (a.choose k * n ^ k) := by ring
        _ ≤ 80 * (n.choose k * a ^ k) := Nat.mul_le_mul_left _ hcm
        _ = n.choose k * (80 * a ^ k) := by ring
        _ ≤ n.choose k * (7 * n ^ k) := Nat.mul_le_mul_left _ hp
        _ = 7 * n.choose k * n ^ k := by ring
    exact Nat.le_of_mul_le_mul_right this hnk
  rw [lowSum_succ]
  omega

/-- All levels up to `k`: every `N ≥ 1` with `5 (N - S_k(n)) ≤ C(n,k) + 1`. -/
lemma levels (hn : 206 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : 12 * k ≤ n) :
    ∀ N, 1 ≤ N → 5 * (N - lowSum n k) ≤ n.choose k + 1 → 2 ^ N ≤ 2 * ucCount n N := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro N hN h5
    have : lowSum n 1 = 1 := by simp [lowSum]
    exact window le_rfl (by omega) (by omega) h5
  | succ k hk ih =>
    intro N hN h5
    by_cases hc : 2 * lowSum (9 * (k + 1)) (k + 1) ≤ N + 1
    · exact level (by omega) n (by omega) le_rfl N hc h5
    · have := cross hk hn hkn
      exact ih (by omega) N hN (by omega)

/-- **The counting criterion fails below `C(n, ⌊n/12⌋)/5`.** For `n ≥ 206` and
`1 ≤ N ≤ C(n,⌊n/12⌋)/5`, `U(n,N) ≥ 2^{N-1}`. -/
theorem two_pow_le_ucCount (hn : 206 ≤ n) {N : ℕ} (hN : 1 ≤ N)
    (hNc : 5 * N ≤ n.choose (n / 12)) : 2 ^ N ≤ 2 * ucCount n N :=
  levels hn (k := n / 12) (by omega) (by omega) N hN (by omega)

/-- **In particular below `2^{n/4}`.** For `n ≥ 206`, `1 ≤ N` and `N^4 ≤ 2^n`,
`U(n,N) ≥ 2^{N-1}`. -/
theorem two_pow_le_ucCount_of_pow_four (hn : 206 ≤ n) {N : ℕ} (hN : 1 ≤ N)
    (hN4 : N ^ 4 ≤ 2 ^ n) : 2 ^ N ≤ 2 * ucCount n N := by
  refine two_pow_le_ucCount hn hN ?_
  set K := n / 12 with hK
  have h11 : 11 ^ K ≤ n.choose K := pow_le_choose_of_mul_le 11 n K (by omega)
  have hK12 : 12 ≤ K := by omega
  have hbig : ∀ j, 12 ≤ j → 1280000 * 4096 ^ j ≤ 14641 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j _ ih =>
      rw [pow_succ, pow_succ]
      calc 1280000 * (4096 ^ j * 4096) = 1280000 * 4096 ^ j * 4096 := by ring
        _ ≤ 14641 ^ j * 4096 := Nat.mul_le_mul_right _ ih
        _ ≤ 14641 ^ j * 14641 := Nat.mul_le_mul_left _ (by norm_num)
  have h2n : 2 ^ n ≤ 2 ^ (12 * K + 11) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (5 * N) ^ 4 ≤ (n.choose K) ^ 4 := by
    calc (5 * N) ^ 4 = 625 * N ^ 4 := by ring
      _ ≤ 625 * 2 ^ (12 * K + 11) := Nat.mul_le_mul_left _ (hN4.trans h2n)
      _ = 1280000 * 4096 ^ K := by rw [pow_add, pow_mul]; norm_num; ring
      _ ≤ 14641 ^ K := hbig K hK12
      _ = (11 ^ K) ^ 4 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (n.choose K) ^ 4 := Nat.pow_le_pow_left h11 4
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h4

/-- **The answer to the counting question is negative.** There is no constant `C` such that
`2 U(n,N) < 2^N` (that is, `U(n,N) < 2^{N-1}`) for all large `n` and all
`N ≥ n^{C log₂ log₂ n}`. -/
theorem count_question_false :
    ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ N : ℕ,
      (n : ℝ) ^ (C * Real.logb 2 (Real.logb 2 n)) ≤ N → 2 * ucCount n N < 2 ^ N := by
  rintro ⟨C, hC⟩
  set c := |C| / Real.log 2 ^ 2 + 1 with hc
  have hc0 : 0 < c := by positivity
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show (0 : ℝ) < Real.log 2 / (8 * c) by positivity)
  have h3 : ∀ᶠ x : ℝ in atTop, 8 ≤ x := eventually_ge_atTop _
  have hnat := tendsto_natCast_atTop_atTop.eventually (h1.and h3)
  obtain ⟨n, hn⟩ := (hC.and (hnat.and (eventually_ge_atTop 206))).exists
  obtain ⟨hCn, ⟨hlo, hn8⟩, hn206⟩ := hn
  set N := 2 ^ (n / 4) with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hN4 : N ^ 4 ≤ 2 ^ n := by
    rw [hNdef, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hgood := two_pow_le_ucCount_of_pow_four hn206 hN1 hN4
  refine absurd (hCn N ?_) (not_lt.2 hgood)
  -- `n^{C log₂ log₂ n} ≤ 2^{⌊n/4⌋}`
  have hnR : (8 : ℝ) ≤ n := hn8
  have hnpos : (0 : ℝ) < n := by linarith
  set L := Real.log n with hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < L := Real.log_pos (by linarith)
  simp only [id, Real.norm_eq_abs, abs_of_pos hnpos, abs_of_nonneg (sq_nonneg L)] at hlo
  have hb1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos]; norm_num; linarith
  have hll0 : 0 ≤ Real.logb 2 (Real.logb 2 n) := Real.logb_nonneg (by norm_num) hb1
  have hll : Real.logb 2 (Real.logb 2 n) ≤ L / Real.log 2 ^ 2 := by
    have hle := Real.log_le_sub_one_of_pos (show 0 < Real.logb 2 n by linarith)
    rw [Real.logb, Real.logb] at *
    rw [div_le_div_iff₀ hlog2 (by positivity)]
    have : Real.log (L / Real.log 2) ≤ L / Real.log 2 := by linarith
    calc Real.log (L / Real.log 2) * Real.log 2 ^ 2
        ≤ L / Real.log 2 * Real.log 2 ^ 2 := by gcongr
      _ = L * Real.log 2 := by field_simp
  have hexp : C * Real.logb 2 (Real.logb 2 n) ≤ c * L := by
    calc C * Real.logb 2 (Real.logb 2 n) ≤ |C| * Real.logb 2 (Real.logb 2 n) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hll0
      _ ≤ |C| * (L / Real.log 2 ^ 2) := mul_le_mul_of_nonneg_left hll (abs_nonneg C)
      _ = |C| / Real.log 2 ^ 2 * L := by ring
      _ ≤ c * L := mul_le_mul_of_nonneg_right (by rw [hc]; linarith) hL0.le
  have hNR : ((N : ℕ) : ℝ) = (2 : ℝ) ^ (n / 4) := by rw [hNdef]; push_cast; ring
  rw [hNR]
  have hn4 : ((n / 4 : ℕ) : ℝ) ≥ (n : ℝ) / 4 - 1 := by
    have : (n : ℝ) ≤ 4 * ((n / 4 : ℕ) : ℝ) + 3 := by
      have := Nat.lt_mul_div_succ n (show 0 < 4 by norm_num)
      exact_mod_cast (by omega : n ≤ 4 * (n / 4) + 3)
    linarith
  rw [← Real.rpow_natCast, ← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_rpow hnpos, Real.log_rpow (by norm_num)]
  calc C * Real.logb 2 (Real.logb 2 n) * L ≤ c * L * L := mul_le_mul_of_nonneg_right hexp hL0.le
    _ = c * L ^ 2 := by ring
    _ ≤ c * (Real.log 2 / (8 * c) * n) := mul_le_mul_of_nonneg_left hlo hc0.le
    _ = Real.log 2 * (n / 8) := by field_simp
    _ ≤ Real.log 2 * ((n : ℝ) / 4 - 1) := by
        apply mul_le_mul_of_nonneg_left _ hlog2.le; linarith
    _ ≤ ((n / 4 : ℕ) : ℝ) * Real.log 2 := by nlinarith

end Erdos1183
