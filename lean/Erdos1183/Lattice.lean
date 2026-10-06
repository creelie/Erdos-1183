import Erdos1183.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The lattice function `f(n)`

A sublattice of `2^{[n]}` (a family closed under union and intersection) is determined by its
least member and by the least member containing each point. Counting these data and applying a
first-moment argument to a random colouring gives a first upper bound for `f(n)`; the sharper
count is in `Erdos1183.LatticeCount`.

* `sublattice_eq_image`: a nonempty sublattice is `{B ∪ ⋃_{x ∈ X} A x : X ⊆ [n]}` for its least
  member `B` and the least members `A x` containing the points `x`.
* `smallF_le_sq`: `f(n) ≤ n^2 + n + 1`.
-/
open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

variable {n : ℕ}

lemma smallF_le_of {m : ℕ}
    (h : ∃ χ : Colouring n, ∀ 𝓕, LatticeClosed 𝓕 → Monochromatic χ 𝓕 → #𝓕 ≤ m) :
    smallF n ≤ m := by
  obtain ⟨χ, hχ⟩ := h
  refine (ciInf_le (OrderBot.bddBelow _) χ).trans ?_
  unfold maxLat
  rw [Finset.sup_le_iff]
  intro 𝓕 h𝓕
  simp only [mem_filter, mem_univ, true_and] at h𝓕
  exact hχ 𝓕 h𝓕.1 h𝓕.2

/-- Colourings that are constant on a family `𝓕`: at most `2 · 2^{2^n - |𝓕|}`. -/
lemma card_mono_mul_le (𝓕 : Finset (Finset (Fin n))) :
    #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓕) * 2 ^ #𝓕 ≤ 2 * 2 ^ (2 ^ n) := by
  have hsub : univ.filter (fun χ : Colouring n => Monochromatic χ 𝓕) ⊆
      univ.filter (fun χ : Colouring n => ∀ B ∈ 𝓕, χ B = true) ∪
        univ.filter (fun χ : Colouring n => ∀ B ∈ 𝓕, χ B = false) := by
    intro χ hχ
    have hm := (mem_filter.1 hχ).2
    simp only [mem_union, mem_filter, mem_univ, true_and]
    by_cases hex : ∃ B ∈ 𝓕, χ B = true
    · obtain ⟨B₀, hB₀, h₀⟩ := hex
      exact Or.inl fun B hB => (hm B hB B₀ hB₀).trans h₀
    · push Not at hex
      exact Or.inr fun B hB => by simpa using hex B hB
  calc #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓕) * 2 ^ #𝓕
      ≤ (#(univ.filter fun χ : Colouring n => ∀ B ∈ 𝓕, χ B = true) +
          #(univ.filter fun χ : Colouring n => ∀ B ∈ 𝓕, χ B = false)) * 2 ^ #𝓕 :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans (card_union_le _ _))
    _ = #(univ.filter fun χ : Colouring n => ∀ B ∈ 𝓕, χ B = true) * 2 ^ #𝓕 +
          #(univ.filter fun χ : Colouring n => ∀ B ∈ 𝓕, χ B = false) * 2 ^ #𝓕 := by ring
    _ ≤ 2 ^ (2 ^ n) + 2 ^ (2 ^ n) :=
        Nat.add_le_add (card_const_mul_le 𝓕 true) (card_const_mul_le 𝓕 false)
    _ = 2 * 2 ^ (2 ^ n) := by ring

/-! ### The structure of a sublattice -/

section Structure

variable (𝓛 : Finset (Finset (Fin n)))

/-- The least member of `𝓛`. -/
def lbot : Finset (Fin n) := 𝓛.inf id

/-- The greatest member of `𝓛`. -/
def ltop : Finset (Fin n) := 𝓛.sup id

/-- The least member of `𝓛` containing `x`. -/
def low (x : Fin n) : Finset (Fin n) := (𝓛.filter (x ∈ ·)).inf id

/-- `A x` is `low x` for points `x` of `ltop \ lbot`, and `lbot` otherwise. -/
def lowB (x : Fin n) : Finset (Fin n) := if x ∈ ltop 𝓛 \ lbot 𝓛 then low 𝓛 x else lbot 𝓛

variable {𝓛}

lemma lbot_subset {S : Finset (Fin n)} (hS : S ∈ 𝓛) : lbot 𝓛 ⊆ S :=
  Finset.inf_le (f := id) hS

lemma subset_ltop {S : Finset (Fin n)} (hS : S ∈ 𝓛) : S ⊆ ltop 𝓛 :=
  Finset.le_sup (f := id) hS

lemma low_subset {S : Finset (Fin n)} (hS : S ∈ 𝓛) {x : Fin n} (hx : x ∈ S) : low 𝓛 x ⊆ S :=
  Finset.inf_le (f := id) (mem_filter.2 ⟨hS, hx⟩)

lemma lbot_subset_low (x : Fin n) : lbot 𝓛 ⊆ low 𝓛 x :=
  Finset.le_inf fun _ hS => lbot_subset (mem_filter.1 hS).1

lemma mem_low (x : Fin n) : x ∈ low 𝓛 x := by
  have : ({x} : Finset (Fin n)) ⊆ low 𝓛 x :=
    Finset.le_inf fun S hS => singleton_subset_iff.2 (mem_filter.1 hS).2
  exact this (mem_singleton_self x)

variable (hL : LatticeClosed 𝓛) (hne : 𝓛.Nonempty)
include hL

lemma lbot_mem (hne : 𝓛.Nonempty) : lbot 𝓛 ∈ 𝓛 :=
  InfClosed.finsetInf_mem (s := (𝓛 : Set (Finset (Fin n))))
    (fun a ha b hb => (hL a ha b hb).2) hne fun _ hi => hi

lemma sup_mem {X : Finset (Fin n)} (hX : X.Nonempty) (A : Fin n → Finset (Fin n))
    (hA : ∀ x ∈ X, A x ∈ 𝓛) : X.sup A ∈ 𝓛 :=
  SupClosed.finsetSup_mem (s := (𝓛 : Set (Finset (Fin n))))
    (fun a ha b hb => (hL a ha b hb).1) hX hA

lemma low_mem {x : Fin n} (hx : x ∈ ltop 𝓛) : low 𝓛 x ∈ 𝓛 := by
  obtain ⟨S, hS, hxS⟩ := mem_sup.1 hx
  exact InfClosed.finsetInf_mem (s := (𝓛 : Set (Finset (Fin n))))
    (fun a ha b hb => (hL a ha b hb).2) ⟨S, mem_filter.2 ⟨hS, hxS⟩⟩
    fun i hi => (mem_filter.1 hi).1

lemma lowB_mem (hne : 𝓛.Nonempty) (x : Fin n) : lowB 𝓛 x ∈ 𝓛 := by
  unfold lowB
  split_ifs with hx
  · exact low_mem hL (mem_sdiff.1 hx).1
  · exact lbot_mem hL hne

lemma union_lowB_mem (hne : 𝓛.Nonempty) (X : Finset (Fin n)) :
    lbot 𝓛 ∪ X.biUnion (lowB 𝓛) ∈ 𝓛 := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simpa using lbot_mem hL hne
  · rw [← sup_eq_biUnion]
    exact (hL _ (lbot_mem hL hne) _ (sup_mem hL hX _ fun x _ => lowB_mem hL hne x)).1

omit hL in
lemma eq_union_lowB {S : Finset (Fin n)} (hS : S ∈ 𝓛) : S = lbot 𝓛 ∪ S.biUnion (lowB 𝓛) := by
  apply Subset.antisymm
  · intro x hx
    refine mem_union.2 (Or.inr (mem_biUnion.2 ⟨x, hx, ?_⟩))
    unfold lowB
    split_ifs with hxT
    · exact mem_low x
    · have : x ∈ lbot 𝓛 := by
        by_contra hb
        exact hxT (mem_sdiff.2 ⟨subset_ltop hS hx, hb⟩)
      exact this
  · refine union_subset (lbot_subset hS) (biUnion_subset.2 fun x hx => ?_)
    unfold lowB
    split_ifs
    · exact low_subset hS hx
    · exact lbot_subset hS

/-- **Representation.** A nonempty sublattice is the family of the sets `B ∪ ⋃_{x ∈ X} A x`. -/
theorem sublattice_eq_image (hne : 𝓛.Nonempty) :
    𝓛 = univ.image fun X : Finset (Fin n) => lbot 𝓛 ∪ X.biUnion (lowB 𝓛) := by
  ext S
  simp only [mem_image, mem_univ, true_and]
  constructor
  · intro hS
    exact ⟨S, (eq_union_lowB hS).symm⟩
  · rintro ⟨X, rfl⟩
    exact union_lowB_mem hL hne X

end Structure

/-! ### A first count -/

/-- A sublattice is determined by its least member and the least members containing the points. -/
theorem card_sublattices_le (m : ℕ) :
    #(univ.filter fun 𝓛 : Finset (Finset (Fin n)) => LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ m ≤ #𝓛) ≤
      2 ^ (n * (n + 1)) := by
  have hinj := card_le_card_of_injOn (s := univ.filter fun 𝓛 : Finset (Finset (Fin n)) =>
      LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ m ≤ #𝓛) (t := (univ : Finset (Finset (Fin n) ×
      (Fin n → Finset (Fin n)))))
    (fun 𝓛 => (lbot 𝓛, lowB 𝓛)) (fun _ _ => mem_univ _) (by
      intro 𝓛₁ h₁ 𝓛₂ h₂ he
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
      simp only [Prod.mk.injEq] at he
      rw [sublattice_eq_image h₁.1 h₁.2.1, sublattice_eq_image h₂.1 h₂.2.1, he.1, he.2])
  refine hinj.trans (le_of_eq ?_)
  rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin,
    ← pow_mul, ← pow_add]
  congr 1
  ring


/-! ### First moment -/

/-- If `C · 2^{m}` bounds `4 · 2^{2^n}`… in general: when the colourings that make some family of
a set `𝒜` monochromatic are fewer than all colourings, some colouring makes none of them
monochromatic. -/
lemma exists_colouring_avoiding (𝒜 : Finset (Finset (Finset (Fin n))))
    (h : ∑ 𝓛 ∈ 𝒜, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) < 2 ^ (2 ^ n)) :
    ∃ χ : Colouring n, ∀ 𝓛 ∈ 𝒜, ¬ Monochromatic χ 𝓛 := by
  by_contra hall
  push Not at hall
  have hcover : (univ : Finset (Colouring n)) ⊆
      𝒜.biUnion fun 𝓛 => univ.filter fun χ : Colouring n => Monochromatic χ 𝓛 := by
    intro χ _
    obtain ⟨𝓛, h𝓛, hm⟩ := hall χ
    exact mem_biUnion.2 ⟨𝓛, h𝓛, mem_filter.2 ⟨mem_univ _, hm⟩⟩
  have := (card_le_card hcover).trans card_biUnion_le
  rw [card_univ, card_colouring] at this
  omega

/-- **`f(n) ≤ n^2 + n + 1`.** -/
theorem smallF_le_sq (n : ℕ) : smallF n ≤ n ^ 2 + n + 1 := by
  set m := n * (n + 1) + 2 with hm
  set 𝒜 := univ.filter fun 𝓛 : Finset (Finset (Fin n)) => LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ m ≤ #𝓛
  have hsum : (∑ 𝓛 ∈ 𝒜, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛)) * 2 ^ m ≤
      2 ^ (n * (n + 1)) * (2 * 2 ^ (2 ^ n)) := by
    rw [sum_mul]
    calc ∑ 𝓛 ∈ 𝒜, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) * 2 ^ m
        ≤ ∑ _𝓛 ∈ 𝒜, 2 * 2 ^ (2 ^ n) := sum_le_sum fun 𝓛 h𝓛 => by
          have hm𝓛 := (mem_filter.1 h𝓛).2.2.2
          exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hm𝓛)).trans
            (card_mono_mul_le 𝓛)
      _ = #𝒜 * (2 * 2 ^ (2 ^ n)) := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 ^ (n * (n + 1)) * (2 * 2 ^ (2 ^ n)) :=
          Nat.mul_le_mul_right _ (card_sublattices_le m)
  have hlt : ∑ 𝓛 ∈ 𝒜, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) < 2 ^ (2 ^ n) := by
    have h4 : 2 ^ m = 4 * 2 ^ (n * (n + 1)) := by rw [hm, pow_add]; ring
    rw [h4] at hsum
    have hpos : 0 < 2 ^ (n * (n + 1)) := by positivity
    have hpos' : 0 < 2 ^ (2 ^ n) := by positivity
    nlinarith
  obtain ⟨χ, hχ⟩ := exists_colouring_avoiding 𝒜 hlt
  refine smallF_le_of ⟨χ, fun 𝓕 hL hM => ?_⟩
  by_contra hbig
  push Not at hbig
  have hne : 𝓕.Nonempty := card_pos.1 (by omega)
  exact hχ 𝓕 (mem_filter.2 ⟨mem_univ _, hL, hne, by rw [hm]; nlinarith⟩) hM

end Erdos1183
