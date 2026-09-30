import Erdos1183.Lattice
import Erdos1183.Explicit

/-!
# Random colourings

* `exists_unionClosed_subfamily`: a union-closed family has union-closed subfamilies of every
  smaller size (remove a smallest member).
* `bigF_lt_of_count`: if fewer than `2^{N-1}` union-closed families of size `N` exist, then
  `F(n) < N`. This is the first-moment method for a uniformly random colouring.
* `sum_maxUC_ge`: summed over all colourings, the largest monochromatic union-closed family
  has size at least `∑_j C(n, j) 2^{2^n + 1 - 2^j}`; that is, for a uniformly random colouring
  its expected size is at least `∑_j C(n, j) 2^{1 - 2^j}`.
-/

open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- Removing a smallest member keeps a family union-closed. -/
lemma unionClosed_erase_min {𝓕 : Finset (Finset (Fin n))} (hU : UnionClosed 𝓕)
    {A : Finset (Fin n)} (_hA : A ∈ 𝓕) (hmin : ∀ B ∈ 𝓕, #A ≤ #B) : UnionClosed (𝓕.erase A) := by
  intro B hB C hC
  obtain ⟨hBA, hB⟩ := mem_erase.1 hB
  obtain ⟨-, hC⟩ := mem_erase.1 hC
  refine mem_erase.2 ⟨fun h => hBA ?_, hU B hB C hC⟩
  have hsub : B ⊆ A := h ▸ subset_union_left
  exact eq_of_subset_of_card_le hsub (hmin B hB)

/-- A union-closed family has union-closed subfamilies of every smaller size. -/
theorem exists_unionClosed_subfamily : ∀ (k : ℕ) (𝓕 : Finset (Finset (Fin n))),
    UnionClosed 𝓕 → ∀ N, N + k = #𝓕 → ∃ 𝓖 ⊆ 𝓕, UnionClosed 𝓖 ∧ #𝓖 = N
  | 0, 𝓕, hU, N, hN => ⟨𝓕, subset_rfl, hU, by omega⟩
  | k + 1, 𝓕, hU, N, hN => by
    have hne : 𝓕.Nonempty := card_pos.1 (by omega)
    obtain ⟨A, hA, hmin⟩ := exists_min_image 𝓕 card hne
    obtain ⟨𝓖, h𝓖, hU', hcard⟩ := exists_unionClosed_subfamily k (𝓕.erase A)
      (unionClosed_erase_min hU hA hmin) N (by rw [card_erase_of_mem hA]; omega)
    exact ⟨𝓖, h𝓖.trans (erase_subset _ _), hU', hcard⟩

/-- **The counting criterion.** If fewer than `2^{N-1}` union-closed families of `N` sets
exist, then some colouring has no monochromatic union-closed family of `N` or more sets, so
`F(n) < N`. -/
theorem bigF_lt_of_count (N : ℕ)
    (h : 2 * #(univ.filter fun 𝓕 : Finset (Finset (Fin n)) => UnionClosed 𝓕 ∧ #𝓕 = N) <
      2 ^ N) : bigF n < N := by
  set 𝒜 := univ.filter fun 𝓕 : Finset (Finset (Fin n)) => UnionClosed 𝓕 ∧ #𝓕 = N
  have hsum : ∑ 𝓕 ∈ 𝒜, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓕) <
      2 ^ (2 ^ n) := by
    have h1 : (∑ 𝓕 ∈ 𝒜, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓕)) * 2 ^ N ≤
        #𝒜 * (2 * 2 ^ (2 ^ n)) := by
      rw [sum_mul]
      calc ∑ 𝓕 ∈ 𝒜, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓕) * 2 ^ N
          ≤ ∑ _𝓕 ∈ 𝒜, 2 * 2 ^ (2 ^ n) := sum_le_sum fun 𝓕 h𝓕 => by
            have := (mem_filter.1 h𝓕).2.2
            rw [← this]
            exact card_mono_mul_le 𝓕
        _ = #𝒜 * (2 * 2 ^ (2 ^ n)) := by rw [sum_const, smul_eq_mul]
    have hpos : 0 < 2 ^ (2 ^ n) := by positivity
    have h2 : #𝒜 * (2 * 2 ^ (2 ^ n)) < 2 ^ N * 2 ^ (2 ^ n) := by
      calc #𝒜 * (2 * 2 ^ (2 ^ n)) = (2 * #𝒜) * 2 ^ (2 ^ n) := by ring
        _ < 2 ^ N * 2 ^ (2 ^ n) := Nat.mul_lt_mul_of_pos_right h hpos
    have h3 := h1.trans_lt h2
    rw [mul_comm (2 ^ N)] at h3
    exact Nat.lt_of_mul_lt_mul_right h3
  obtain ⟨χ, hχ⟩ := exists_colouring_avoiding 𝒜 hsum
  have hle : bigF n ≤ N - 1 := by
    rw [bigF_le_iff]
    refine ⟨χ, fun 𝓕 hU hM => ?_⟩
    by_contra hbig
    push Not at hbig
    obtain ⟨𝓖, h𝓖, hU', hcard⟩ :=
      exists_unionClosed_subfamily (#𝓕 - N) 𝓕 hU N (by omega)
    exact hχ 𝓖 (mem_filter.2 ⟨mem_univ _, hU', hcard⟩)
      fun A hA B hB => hM A (h𝓖 hA) B (h𝓖 hB)
  have hN : 1 ≤ N := by
    by_contra h0
    have hN0 : N = 0 := by omega
    have hmem : (∅ : Finset (Finset (Fin n))) ∈ 𝒜 :=
      mem_filter.2 ⟨mem_univ _, by simp [UnionClosed], by simp [hN0]⟩
    have := card_pos.2 ⟨_, hmem⟩
    rw [hN0, pow_zero] at h
    omega
  omega

/-! ### The random colouring from below -/

/-- Colourings with prescribed value `b` on a family `S`: at least `2^{2^n - |S|}`. -/
lemma card_const_ge (S : Finset (Finset (Fin n))) (b : Bool) :
    2 ^ (2 ^ n - #S) ≤ #(univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = b) := by
  have hinj := card_le_card_of_injOn (s := (univ : Finset (↥(Sᶜ) → Bool)))
    (t := univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = b)
    (fun h B => if hB : B ∈ S then b else h ⟨B, mem_compl.2 hB⟩)
    (fun h _ => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      intro B hB
      simp [hB])
    (by
      intro h₁ _ h₂ _ he
      funext ⟨B, hB⟩
      have := congrFun he B
      simpa [(mem_compl.1 hB)] using this)
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, card_compl,
    Fintype.card_finset, Fintype.card_fin] at hinj
  exact hinj

/-- The sets `Y` whose every subset `Y'` has `[n] \ Y'` of the colour of `[n]`. -/
def goodSets (χ : Colouring n) : Finset (Finset (Fin n)) :=
  univ.filter fun Y => ∀ Y' ⊆ Y, χ (univ \ Y') = χ univ

lemma card_goodSets_le_maxUC (χ : Colouring n) : #(goodSets χ) ≤ maxUC χ := by
  rw [le_maxUC_iff]
  refine ⟨(goodSets χ).image fun Y => univ \ Y, ?_, ?_, ?_⟩
  · intro A hA B hB
    simp only [mem_image] at hA hB ⊢
    obtain ⟨Y, hY, rfl⟩ := hA
    obtain ⟨Y', hY', rfl⟩ := hB
    refine ⟨Y ∩ Y', ?_, by rw [sdiff_inter_distrib_right]⟩
    simp only [goodSets, mem_filter, mem_univ, true_and] at hY hY' ⊢
    exact fun Z hZ => hY Z (hZ.trans inter_subset_left)
  · have hcol : ∀ A ∈ (goodSets χ).image (fun Y => univ \ Y), χ A = χ univ := by
      intro A hA
      simp only [mem_image] at hA
      obtain ⟨Y, hY, rfl⟩ := hA
      simp only [goodSets, mem_filter, mem_univ, true_and] at hY
      exact hY Y subset_rfl
    intro A hA B hB
    rw [hcol A hA, hcol B hB]
  · rw [card_image_of_injective _ (fun Y Y' h => by
      simpa [← compl_eq_univ_sdiff] using h)]

/-- For each `Y`, the colourings with `Y` good number at least `2 · 2^{2^n - 2^{|Y|}}`. -/
lemma card_good_ge (Y : Finset (Fin n)) :
    2 * 2 ^ (2 ^ n - 2 ^ #Y) ≤ #(univ.filter fun χ : Colouring n => Y ∈ goodSets χ) := by
  set S := Y.powerset.image fun Y' => univ \ Y' with hS
  have hScard : #S = 2 ^ #Y := by
    rw [hS, card_image_of_injective _ (fun Y Y' h => by
      simpa [← compl_eq_univ_sdiff] using h), card_powerset]
  have huniv : (univ : Finset (Fin n)) ∈ S :=
    mem_image.2 ⟨∅, empty_mem_powerset _, sdiff_empty⟩
  have hsub : ∀ b : Bool, (univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = b) ⊆
      univ.filter fun χ : Colouring n => Y ∈ goodSets χ := by
    intro b χ hχ
    simp only [mem_filter, mem_univ, true_and] at hχ ⊢
    simp only [goodSets, mem_filter, mem_univ, true_and]
    intro Y' hY'
    rw [hχ _ (mem_image.2 ⟨Y', mem_powerset.2 hY', rfl⟩), hχ _ huniv]
  have hdisj : Disjoint (univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = true)
      (univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = false) := by
    rw [disjoint_left]
    intro χ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have := (h1 _ huniv).symm.trans (h2 _ huniv)
    simp at this
  calc 2 * 2 ^ (2 ^ n - 2 ^ #Y) = 2 ^ (2 ^ n - #S) + 2 ^ (2 ^ n - #S) := by rw [hScard]; ring
    _ ≤ #(univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = true) +
        #(univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = false) :=
        Nat.add_le_add (card_const_ge S true) (card_const_ge S false)
    _ = #((univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = true) ∪
        univ.filter fun χ : Colouring n => ∀ B ∈ S, χ B = false) :=
        (card_union_of_disjoint hdisj).symm
    _ ≤ _ := card_le_card (union_subset (hsub true) (hsub false))

/-- **The random colouring from below.** Summed over all `2^{2^n}` colourings,
`∑_χ maxUC χ ≥ ∑_j C(n, j) 2^{2^n + 1 - 2^j}`. -/
theorem sum_maxUC_ge (n : ℕ) :
    ∑ j ∈ range (n + 1), n.choose j * 2 ^ (2 ^ n + 1 - 2 ^ j) ≤
      ∑ χ : Colouring n, maxUC χ := by
  have h1 : ∑ χ : Colouring n, #(goodSets χ) ≤ ∑ χ : Colouring n, maxUC χ :=
    sum_le_sum fun χ _ => card_goodSets_le_maxUC χ
  have h2 : ∑ χ : Colouring n, #(goodSets χ) =
      ∑ Y : Finset (Fin n), #(univ.filter fun χ : Colouring n => Y ∈ goodSets χ) := by
    calc ∑ χ : Colouring n, #(goodSets χ) =
        ∑ χ : Colouring n, ∑ Y : Finset (Fin n), if Y ∈ goodSets χ then 1 else 0 := by
          refine sum_congr rfl fun χ _ => ?_
          rw [← card_filter]
          congr 1
          ext Y
          simp
      _ = ∑ Y : Finset (Fin n), ∑ χ : Colouring n, if Y ∈ goodSets χ then 1 else 0 := sum_comm
      _ = _ := sum_congr rfl fun Y _ => by rw [card_filter]
  have h3 : ∑ Y : Finset (Fin n), 2 * 2 ^ (2 ^ n - 2 ^ #Y) ≤
      ∑ Y : Finset (Fin n), #(univ.filter fun χ : Colouring n => Y ∈ goodSets χ) :=
    sum_le_sum fun Y _ => card_good_ge Y
  have h4 : ∑ Y : Finset (Fin n), 2 * 2 ^ (2 ^ n - 2 ^ #Y) =
      ∑ j ∈ range (n + 1), n.choose j * 2 ^ (2 ^ n + 1 - 2 ^ j) := by
    rw [← powerset_univ, sum_powerset_apply_card (f := fun m => 2 * 2 ^ (2 ^ n - 2 ^ m)),
      card_univ, Fintype.card_fin]
    refine sum_congr rfl fun j hj => ?_
    have hj : 2 ^ j ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by rw [mem_range] at hj; omega)
    rw [smul_eq_mul, show 2 ^ n + 1 - 2 ^ j = (2 ^ n - 2 ^ j) + 1 by omega, pow_succ]
    ring
  rw [← h4]
  exact h3.trans (h2 ▸ h1)

/-- **Explicit form.** If `j ≤ n` and `2^{2^j} ≤ n`, the expected size of the largest
monochromatic union-closed family of a random colouring is at least `(2/n)(n/j)^j`:
`2 n^j 2^{2^n} ≤ n j^j ∑_χ maxUC χ`. -/
theorem sum_maxUC_ge_pow (j : ℕ) (hj : j ≤ n) (hjn : 2 ^ 2 ^ j ≤ n) :
    2 * n ^ j * 2 ^ (2 ^ n) ≤ n * j ^ j * ∑ χ : Colouring n, maxUC χ := by
  have hterm : n.choose j * 2 ^ (2 ^ n + 1 - 2 ^ j) ≤ ∑ χ : Colouring n, maxUC χ :=
    (single_le_sum (f := fun j => n.choose j * 2 ^ (2 ^ n + 1 - 2 ^ j))
      (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))).trans (sum_maxUC_ge n)
  have hch := pow_le_pow_mul_choose j n hj
  have hj2 : 2 ^ j ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hj
  have hsplit : 2 * 2 ^ (2 ^ n) = 2 ^ (2 ^ n + 1 - 2 ^ j) * 2 ^ 2 ^ j := by
    rw [← pow_add, show 2 ^ n + 1 - 2 ^ j + 2 ^ j = 2 ^ n + 1 by omega, pow_succ']
  calc 2 * n ^ j * 2 ^ (2 ^ n) = n ^ j * (2 ^ (2 ^ n + 1 - 2 ^ j) * 2 ^ 2 ^ j) := by
        rw [← hsplit]; ring
    _ ≤ (j ^ j * n.choose j) * (2 ^ (2 ^ n + 1 - 2 ^ j) * n) :=
        Nat.mul_le_mul hch (Nat.mul_le_mul_left _ hjn)
    _ = n * j ^ j * (n.choose j * 2 ^ (2 ^ n + 1 - 2 ^ j)) := by ring
    _ ≤ n * j ^ j * ∑ χ : Colouring n, maxUC χ := Nat.mul_le_mul_left _ hterm

end Erdos1183
