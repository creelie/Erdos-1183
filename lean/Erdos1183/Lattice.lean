import Erdos1183.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The lattice function `f(n)`

A sublattice of `2^{[n]}` (a family closed under union and intersection) is determined by its
least member and by the least member containing each point. Refining this description by the
maximal elements below each point, we count sublattices of a given size and apply a first-moment
argument to a random colouring.

* `sublattice_eq_image`: a nonempty sublattice is `{B ∪ ⋃_{x ∈ X} A x : X ⊆ [n]}` for its least
  member `B` and the least members `A x` containing the points `x`.
* `smallF_le_sq`: `f(n) ≤ n^2 + n + 1`.
* `smallF_le_log`: `f(n) ≤ n L (3 L + 2) + 2 n + 3 L + 3` with `L = ⌊log₂ n⌋ + 1`, so that
  `f(n) = O(n (log n)^2)`.
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

/-! ### Below a point -/

omit hL in
lemma mem_low_iff {x y : Fin n} (_hy : y ∈ ltop 𝓛) (hx : x ∈ ltop 𝓛) (hL : LatticeClosed 𝓛) :
    y ∈ low 𝓛 x ↔ low 𝓛 y ⊆ low 𝓛 x :=
  ⟨fun h => low_subset (low_mem hL hx) h, fun h => h (mem_low y)⟩

variable (𝓛) in
/-- The points strictly below `x`: those `y` with `low y ⊂ low x`. -/
def below (x : Fin n) : Finset (Fin n) :=
  univ.filter fun y => y ∈ ltop 𝓛 \ lbot 𝓛 ∧ low 𝓛 y ⊂ low 𝓛 x

variable (𝓛) in
/-- The points equivalent to `x`: those `y` with `low y = low x`. -/
def cls (x : Fin n) : Finset (Fin n) :=
  univ.filter fun y => y ∈ ltop 𝓛 \ lbot 𝓛 ∧ low 𝓛 y = low 𝓛 x

lemma low_eq_union {x : Fin n} (hx : x ∈ ltop 𝓛 \ lbot 𝓛) :
    low 𝓛 x = lbot 𝓛 ∪ cls 𝓛 x ∪ (below 𝓛 x).biUnion (low 𝓛) := by
  have hxT := (mem_sdiff.1 hx).1
  apply Subset.antisymm
  · intro z hz
    simp only [mem_union, cls, below, mem_filter, mem_univ, true_and, mem_biUnion]
    by_cases hzB : z ∈ lbot 𝓛
    · exact Or.inl (Or.inl hzB)
    · have hzT : z ∈ ltop 𝓛 := subset_ltop (low_mem hL hxT) hz
      have hzx : low 𝓛 z ⊆ low 𝓛 x := (mem_low_iff hzT hxT hL).1 hz
      have hzTB : z ∈ ltop 𝓛 \ lbot 𝓛 := mem_sdiff.2 ⟨hzT, hzB⟩
      by_cases heq : low 𝓛 z = low 𝓛 x
      · exact Or.inl (Or.inr ⟨hzTB, heq⟩)
      · exact Or.inr ⟨z, ⟨hzTB, ssubset_of_subset_of_ne hzx heq⟩, mem_low z⟩
  · refine union_subset (union_subset (lbot_subset_low x) ?_) (biUnion_subset.2 ?_)
    · intro y hy
      simp only [cls, mem_filter, mem_univ, true_and] at hy
      rw [← hy.2]
      exact mem_low y
    · intro y hy
      simp only [below, mem_filter, mem_univ, true_and] at hy
      exact hy.2.1

variable (𝓛) in
/-- The subsets `R` of `below x` whose points cover everything below `x`. -/
def covers (x : Fin n) : Finset (Finset (Fin n)) :=
  (below 𝓛 x).powerset.filter fun R => R.biUnion (low 𝓛) = (below 𝓛 x).biUnion (low 𝓛)

omit hL in
lemma covers_nonempty (x : Fin n) : (covers 𝓛 x).Nonempty :=
  ⟨below 𝓛 x, mem_filter.2 ⟨mem_powerset_self _, rfl⟩⟩

variable (𝓛) in
/-- A smallest covering set of points below `x`. -/
noncomputable def rsel (x : Fin n) : Finset (Fin n) :=
  (exists_min_image (covers 𝓛 x) card (covers_nonempty x)).choose

omit hL in
lemma rsel_mem (x : Fin n) : rsel 𝓛 x ∈ covers 𝓛 x :=
  (exists_min_image (covers 𝓛 x) card (covers_nonempty x)).choose_spec.1

omit hL in
lemma rsel_min (x : Fin n) {R : Finset (Fin n)} (hR : R ∈ covers 𝓛 x) :
    #(rsel 𝓛 x) ≤ #R :=
  (exists_min_image (covers 𝓛 x) card (covers_nonempty x)).choose_spec.2 R hR

omit hL in
lemma rsel_subset (x : Fin n) : rsel 𝓛 x ⊆ below 𝓛 x :=
  mem_powerset.1 (mem_filter.1 (rsel_mem x)).1

omit hL in
lemma rsel_cover (x : Fin n) :
    (rsel 𝓛 x).biUnion (low 𝓛) = (below 𝓛 x).biUnion (low 𝓛) :=
  (mem_filter.1 (rsel_mem x)).2

omit hL in
/-- The selected points form an antichain. -/
lemma rsel_antichain (x : Fin n) {y y' : Fin n} (hy : y ∈ rsel 𝓛 x) (hy' : y' ∈ rsel 𝓛 x)
    (hne : y ≠ y') : ¬ low 𝓛 y ⊆ low 𝓛 y' := by
  intro hsub
  have hR : (rsel 𝓛 x).erase y ∈ covers 𝓛 x := by
    refine mem_filter.2 ⟨mem_powerset.2 ((erase_subset _ _).trans (rsel_subset x)), ?_⟩
    rw [← rsel_cover x]
    apply Subset.antisymm (biUnion_subset_biUnion_of_subset_left _ (erase_subset _ _))
    refine biUnion_subset.2 fun z hz => ?_
    by_cases hzy : z = y
    · subst hzy
      exact hsub.trans (subset_biUnion_of_mem (low 𝓛) (mem_erase.2 ⟨Ne.symm hne, hy'⟩))
    · exact subset_biUnion_of_mem (low 𝓛) (mem_erase.2 ⟨hzy, hz⟩)
  have h1 := rsel_min x hR
  rw [card_erase_of_mem hy] at h1
  have h2 : 0 < #(rsel 𝓛 x) := card_pos.2 ⟨y, hy⟩
  omega

lemma low_eq_union_rsel {x : Fin n} (hx : x ∈ ltop 𝓛 \ lbot 𝓛) :
    low 𝓛 x = lbot 𝓛 ∪ cls 𝓛 x ∪ (rsel 𝓛 x).biUnion (low 𝓛) := by
  rw [rsel_cover x]
  exact low_eq_union hL hx

/-- **Width.** The selected points below `x` span `2^{|R|}` distinct members. -/
lemma two_pow_card_rsel_le (hne : 𝓛.Nonempty) (x : Fin n) : 2 ^ #(rsel 𝓛 x) ≤ #𝓛 := by
  rw [← card_powerset]
  refine card_le_card_of_injOn (fun Y => lbot 𝓛 ∪ Y.biUnion (low 𝓛)) ?_ ?_
  · intro Y hY
    have hY' := mem_powerset.1 hY
    rcases Y.eq_empty_or_nonempty with rfl | hYne
    · simpa using lbot_mem hL hne
    · show lbot 𝓛 ∪ Y.biUnion (low 𝓛) ∈ 𝓛
      rw [← sup_eq_biUnion]
      refine (hL _ (lbot_mem hL hne) _ (sup_mem hL hYne _ fun y hy => ?_)).1
      have := rsel_subset x (hY' hy)
      simp only [below, mem_filter, mem_univ, true_and] at this
      exact low_mem hL (mem_sdiff.1 this.1).1
  · -- two different subsets give different members
    have key : ∀ Y ∈ (rsel 𝓛 x).powerset, ∀ Y' ∈ (rsel 𝓛 x).powerset, ∀ y ∈ Y, y ∉ Y' →
        y ∉ lbot 𝓛 ∪ Y'.biUnion (low 𝓛) := by
      intro Y hY Y' hY' y hy hy'
      have hyR := mem_powerset.1 hY hy
      have hyB := rsel_subset x hyR
      simp only [below, mem_filter, mem_univ, true_and] at hyB
      simp only [mem_union, mem_biUnion, not_or, not_exists, not_and]
      refine ⟨(mem_sdiff.1 hyB.1).2, fun y' hy'Y' hmem => ?_⟩
      have hy'R := mem_powerset.1 hY' hy'Y'
      have hy'B := rsel_subset x hy'R
      simp only [below, mem_filter, mem_univ, true_and] at hy'B
      have hsub : low 𝓛 y ⊆ low 𝓛 y' :=
        (mem_low_iff (mem_sdiff.1 hyB.1).1 (mem_sdiff.1 hy'B.1).1 hL).1 hmem
      exact rsel_antichain x hyR hy'R (fun h => hy' (h ▸ hy'Y')) hsub
    intro Y hY Y' hY' hYY
    simp only at hYY
    by_contra hne'
    obtain ⟨y, hy⟩ : ∃ y, (y ∈ Y ∧ y ∉ Y') ∨ (y ∈ Y' ∧ y ∉ Y) := by
      by_contra hall
      push Not at hall
      exact hne' (ext fun y => ⟨(hall y).1, (hall y).2⟩)
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key Y hY Y' hY' y h1 h2 (hYY ▸ mem_union.2 (Or.inr (mem_biUnion.2 ⟨y, h1, mem_low y⟩)))
    · exact key Y' hY' Y hY y h1 h2 (hYY.symm ▸ mem_union.2 (Or.inr (mem_biUnion.2 ⟨y, h1, mem_low y⟩)))

variable (𝓛) in
/-- A canonical representative of the class of `x`. -/
noncomputable def rep (x : Fin n) : Fin n :=
  if h : (cls 𝓛 x).Nonempty then (cls 𝓛 x).min' h else x

omit hL in
lemma cls_eq_of_low_eq {x y : Fin n} (h : low 𝓛 y = low 𝓛 x) : cls 𝓛 y = cls 𝓛 x := by
  ext z
  simp only [cls, mem_filter, mem_univ, true_and, h]

omit hL in
lemma mem_cls_self {x : Fin n} (hx : x ∈ ltop 𝓛 \ lbot 𝓛) : x ∈ cls 𝓛 x := by
  simp only [cls, mem_filter, mem_univ, true_and]
  exact ⟨hx, trivial⟩

omit hL in
lemma cls_eq_rep {x : Fin n} (hx : x ∈ ltop 𝓛 \ lbot 𝓛) :
    cls 𝓛 x = univ.filter fun y => y ∈ ltop 𝓛 \ lbot 𝓛 ∧ rep 𝓛 y = rep 𝓛 x := by
  ext y
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hy
    have hy' := hy
    simp only [cls, mem_filter, mem_univ, true_and] at hy'
    refine ⟨hy'.1, ?_⟩
    have hc : cls 𝓛 y = cls 𝓛 x := cls_eq_of_low_eq hy'.2
    have hxne : (cls 𝓛 x).Nonempty := ⟨x, mem_cls_self hx⟩
    simp only [rep, hc, hxne, dite_true]
  · rintro ⟨hyTB, hrep⟩
    have hyne : (cls 𝓛 y).Nonempty := ⟨y, mem_cls_self hyTB⟩
    have hxne : (cls 𝓛 x).Nonempty := ⟨x, mem_cls_self hx⟩
    simp only [rep, hyne, hxne, dite_true] at hrep
    have h1 := min'_mem _ hyne
    have h2 := min'_mem _ hxne
    rw [hrep] at h1
    simp only [cls, mem_filter, mem_univ, true_and] at h1 h2
    simp only [cls, mem_filter, mem_univ, true_and]
    exact ⟨hyTB, h1.2.symm.trans h2.2⟩

end Structure

/-! ### Codes of sublattices -/

section Codes

/-- The code of a family: least and greatest members, class representatives and the selected
points below each point. -/
noncomputable def code (𝓛 : Finset (Finset (Fin n))) :
    Finset (Fin n) × Finset (Fin n) × (Fin n → Fin n) × (Fin n → Finset (Fin n)) :=
  (lbot 𝓛, ltop 𝓛, rep 𝓛, rsel 𝓛)

/-- **Injectivity of codes.** Two nonempty sublattices with the same code are equal. -/
theorem code_injOn {𝓛₁ 𝓛₂ : Finset (Finset (Fin n))} (h₁ : LatticeClosed 𝓛₁)
    (h₂ : LatticeClosed 𝓛₂) (hne₁ : 𝓛₁.Nonempty) (hne₂ : 𝓛₂.Nonempty)
    (hc : code 𝓛₁ = code 𝓛₂) : 𝓛₁ = 𝓛₂ := by
  simp only [code, Prod.mk.injEq] at hc
  obtain ⟨hB, hT, hrep, hR⟩ := hc
  -- the least members containing a point agree, by induction on their size
  have hlow : ∀ k, ∀ x, #(low 𝓛₁ x) = k → x ∈ ltop 𝓛₁ \ lbot 𝓛₁ → low 𝓛₁ x = low 𝓛₂ x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hk hx
      have hx₂ : x ∈ ltop 𝓛₂ \ lbot 𝓛₂ := by rw [← hT, ← hB]; exact hx
      rw [low_eq_union_rsel h₁ hx, low_eq_union_rsel h₂ hx₂, cls_eq_rep hx, cls_eq_rep hx₂,
        ← hB, ← hT, ← hrep, ← hR]
      congr 1
      refine biUnion_congr rfl fun y hy => ?_
      have hyb := rsel_subset x hy
      simp only [below, mem_filter, mem_univ, true_and] at hyb
      exact ih _ (hk ▸ card_lt_card hyb.2) y rfl hyb.1
  have hA : lowB 𝓛₁ = lowB 𝓛₂ := by
    funext x
    unfold lowB
    rw [← hB, ← hT]
    split_ifs with hx
    · exact hlow _ x rfl hx
    · rfl
  rw [sublattice_eq_image h₁ hne₁, sublattice_eq_image h₂ hne₂, hA, hB]

/-- The first, coarser code: least member and least members containing the points. -/
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

/-- Sets of at most `w` points. -/
def smallSets (w : ℕ) : Finset (Finset (Fin n)) := univ.filter fun s => #s ≤ w

lemma sum_pow_le (n : ℕ) : ∀ w, ∑ i ∈ range (w + 1), n ^ i ≤ (n + 1) ^ w
  | 0 => by simp
  | w + 1 => by
    rw [sum_range_succ]
    have ih := sum_pow_le n w
    have h2 : n ^ (w + 1) ≤ n * (n + 1) ^ w := by
      rw [pow_succ']
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    calc ∑ i ∈ range (w + 1), n ^ i + n ^ (w + 1) ≤ (n + 1) ^ w + n * (n + 1) ^ w :=
          Nat.add_le_add ih h2
      _ = (n + 1) ^ (w + 1) := by ring

lemma card_smallSets (w : ℕ) : #(smallSets (n := n) w) ≤ (n + 1) ^ w := by
  have hsub : smallSets (n := n) w ⊆ (range (w + 1)).biUnion fun i => powersetCard i univ := by
    intro s hs
    simp only [smallSets, mem_filter, mem_univ, true_and] at hs
    simp only [mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and]
    exact ⟨#s, by omega, rfl⟩
  calc #(smallSets (n := n) w) ≤ ∑ i ∈ range (w + 1), #(powersetCard i (univ : Finset (Fin n))) :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ i ∈ range (w + 1), n ^ i := sum_le_sum fun i _ => by
        rw [card_powersetCard, card_univ, Fintype.card_fin]
        exact Nat.choose_le_pow n i
    _ ≤ (n + 1) ^ w := sum_pow_le n w

/-- Codes whose selected sets all have at most `w` points. -/
noncomputable def codes (w : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n) × (Fin n → Fin n) × (Fin n → Finset (Fin n))) :=
  univ ×ˢ univ ×ˢ univ ×ˢ Fintype.piFinset fun _ => smallSets w

lemma card_codes (w : ℕ) : #(codes (n := n) w) ≤ 2 ^ n * 2 ^ n * n ^ n * ((n + 1) ^ w) ^ n := by
  simp only [codes, card_product, card_univ, Fintype.card_finset, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_piFinset, prod_const]
  have := Nat.pow_le_pow_left (card_smallSets (n := n) w) n
  calc 2 ^ n * (2 ^ n * (n ^ n * #(smallSets (n := n) w) ^ n)) =
      2 ^ n * 2 ^ n * n ^ n * #(smallSets (n := n) w) ^ n := by ring
    _ ≤ 2 ^ n * 2 ^ n * n ^ n * ((n + 1) ^ w) ^ n := Nat.mul_le_mul_left _ this

/-- The number of nonempty sublattices whose size has binary logarithm `w`. -/
lemma card_sublattices_log_le (m w : ℕ) :
    #(univ.filter fun 𝓛 : Finset (Finset (Fin n)) =>
        LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ m ≤ #𝓛 ∧ Nat.log 2 #𝓛 = w) ≤
      2 ^ n * 2 ^ n * n ^ n * ((n + 1) ^ w) ^ n := by
  refine le_trans ?_ (card_codes w)
  refine card_le_card_of_injOn code ?_ ?_
  · intro 𝓛 h𝓛
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h𝓛
    obtain ⟨hL, hne, -, hw⟩ := h𝓛
    simp only [codes, code, mem_coe, mem_product, mem_univ, true_and, Fintype.mem_piFinset,
      smallSets, mem_filter]
    intro x
    rw [← hw]
    exact Nat.le_log_of_pow_le (by norm_num) (two_pow_card_rsel_le hL hne x)
  · intro 𝓛₁ h₁ 𝓛₂ h₂ he
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
    exact code_injOn h₁.1 h₂.1 h₁.2.1 h₂.2.1 he

end Codes

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

/-! ### The bound `f(n) = O(n (log n)^2)` -/

lemma sum_two_pow_lt : ∀ k, ∑ w ∈ range k, 2 ^ w < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [sum_range_succ, pow_succ]
    have := sum_two_pow_lt k
    omega

/-- The exponent bookkeeping: `E(w) = n (L (w+1) + 2) + w + 3`. -/
def expo (n L w : ℕ) : ℕ := n * (L * (w + 1) + 2) + w + 3

lemma expo_mono (n L : ℕ) {w w' : ℕ} (h : w ≤ w') : expo n L w ≤ expo n L w' := by
  unfold expo
  have := Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left L
    (Nat.add_le_add_right h 1)) 2)
  omega

lemma expo_le_two_pow (n L : ℕ) (hL : 1 ≤ L) (hn : n + 1 ≤ 2 ^ L) :
    ∀ w, 3 * L + 2 ≤ w → expo n L w ≤ 2 ^ w := by
  intro w hw
  induction w, hw using Nat.le_induction with
  | base =>
    have hLt : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
    set P := 2 ^ L with hP
    have hsplit : 2 ^ (3 * L + 2) = 4 * P * P * P := by
      rw [hP, show 3 * L + 2 = L + L + L + 2 by ring, pow_add, pow_add, pow_add]; ring
    rw [hsplit, expo]
    have hsq : (L + 1) * (L + 1) ≤ P * P := Nat.mul_le_mul hLt hLt
    have h1 : n * (L * (3 * L + 2 + 1) + 2) ≤ (P - 1) * (3 * L * L + 3 * L + 2) := by
      have : n ≤ P - 1 := by omega
      calc n * (L * (3 * L + 2 + 1) + 2) = n * (3 * L * L + 3 * L + 2) := by ring
        _ ≤ (P - 1) * (3 * L * L + 3 * L + 2) := Nat.mul_le_mul_right _ this
    have hP1 : 1 ≤ P := by omega
    have h2 : (P - 1) * (3 * L * L + 3 * L + 2) + (3 * L + 2) + 3 ≤ P * (3 * L * L + 3 * L + 5) := by
      obtain ⟨Q, hQ⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
      rw [hQ, Nat.add_sub_cancel]
      nlinarith
    have h3 : P * (3 * L * L + 3 * L + 5) ≤ 4 * P * P * P := by
      have : 3 * L * L + 3 * L + 5 ≤ 4 * (P * P) := by nlinarith
      calc P * (3 * L * L + 3 * L + 5) ≤ P * (4 * (P * P)) := Nat.mul_le_mul_left _ this
        _ = 4 * P * P * P := by ring
    omega
  | succ w hw ih =>
    have : expo n L (w + 1) ≤ 2 * expo n L w := by
      unfold expo
      have h1 : n * (L * (w + 1 + 1) + 2) = n * (L * (w + 1) + 2) + n * L := by ring
      have h2 : n * L ≤ n * (L * (w + 1) + 2) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      omega
    rw [pow_succ]
    omega

/-- **`f(n) = O(n (log n)^2)`.** With `L = ⌊log₂ n⌋ + 1`,
`f(n) ≤ n L (3 L + 2) + 2 n + 3 L + 3`. -/
theorem smallF_le_log (n : ℕ) :
    smallF n ≤ n * (Nat.log 2 n + 1) * (3 * (Nat.log 2 n + 1) + 2) + 2 * n +
      3 * (Nat.log 2 n + 1) + 3 := by
  set L := Nat.log 2 n + 1 with hLdef
  have hL1 : 1 ≤ L := by omega
  have hnL : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) n
  set m := expo n L (3 * L + 1) with hm
  have hmval : m = n * L * (3 * L + 2) + 2 * n + 3 * L + 4 := by
    rw [hm, expo]; ring
  -- `E(w) ≤ max(m, 2^w)` for every `w`
  have hE : ∀ w, expo n L w ≤ m ∨ expo n L w ≤ 2 ^ w := by
    intro w
    by_cases hw : w ≤ 3 * L + 1
    · exact Or.inl (expo_mono n L hw)
    · exact Or.inr (expo_le_two_pow n L hL1 hnL w (by omega))
  set 𝒜 : ℕ → Finset (Finset (Finset (Fin n))) := fun w =>
    univ.filter fun 𝓛 => LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ m ≤ #𝓛 ∧ Nat.log 2 #𝓛 = w with h𝒜
  set X : ℕ → ℕ := fun w =>
    ∑ 𝓛 ∈ 𝒜 w, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) with hX
  -- each layer is small
  have hlayer : ∀ w, X w * 2 ^ (w + 2) ≤ 2 ^ (2 ^ n) := by
    intro w
    have hcodes : #(𝒜 w) ≤ 2 ^ (n * (L * (w + 1) + 2)) := by
      refine (card_sublattices_log_le m w).trans ?_
      have h1 : n ≤ 2 ^ L := by omega
      calc 2 ^ n * 2 ^ n * n ^ n * ((n + 1) ^ w) ^ n
          ≤ 2 ^ n * 2 ^ n * (2 ^ L) ^ n * ((2 ^ L) ^ w) ^ n := by
            gcongr
      _ = 2 ^ (n * (L * (w + 1) + 2)) := by
            rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
            congr 1
            ring
    have hfam : ∀ 𝓛 ∈ 𝒜 w, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) *
        2 ^ expo n L w ≤ 2 * 2 ^ (2 ^ n) := by
      intro 𝓛 h𝓛
      simp only [h𝒜, mem_filter, mem_univ, true_and] at h𝓛
      obtain ⟨-, hne, hm𝓛, hw⟩ := h𝓛
      have hpow : 2 ^ w ≤ #𝓛 := by
        rw [← hw]
        exact Nat.pow_log_le_self 2 (card_pos.2 hne).ne'
      have hle : expo n L w ≤ #𝓛 := by
        rcases hE w with h | h
        · omega
        · omega
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hle)).trans
        (card_mono_mul_le 𝓛)
    have hsum : X w * 2 ^ expo n L w ≤ 2 ^ (n * (L * (w + 1) + 2)) * (2 * 2 ^ (2 ^ n)) := by
      simp only [hX]
      rw [sum_mul]
      calc ∑ 𝓛 ∈ 𝒜 w, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) * 2 ^ expo n L w
          ≤ ∑ _𝓛 ∈ 𝒜 w, 2 * 2 ^ (2 ^ n) := sum_le_sum hfam
        _ = #(𝒜 w) * (2 * 2 ^ (2 ^ n)) := by rw [sum_const, smul_eq_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ hcodes
    have hsplit : 2 ^ expo n L w = 2 ^ (n * (L * (w + 1) + 2)) * 2 * 2 ^ (w + 2) := by
      rw [expo, show n * (L * (w + 1) + 2) + w + 3 = n * (L * (w + 1) + 2) + 1 + (w + 2) by ring,
        pow_add, pow_add, pow_one]
    rw [hsplit] at hsum
    have hpos : 0 < 2 ^ (n * (L * (w + 1) + 2)) * 2 := by positivity
    have key : (X w * 2 ^ (w + 2)) * (2 ^ (n * (L * (w + 1) + 2)) * 2) ≤
        2 ^ (2 ^ n) * (2 ^ (n * (L * (w + 1) + 2)) * 2) := by
      calc (X w * 2 ^ (w + 2)) * (2 ^ (n * (L * (w + 1) + 2)) * 2)
          = X w * (2 ^ (n * (L * (w + 1) + 2)) * 2 * 2 ^ (w + 2)) := by ring
        _ ≤ 2 ^ (n * (L * (w + 1) + 2)) * (2 * 2 ^ (2 ^ n)) := hsum
        _ = 2 ^ (2 ^ n) * (2 ^ (n * (L * (w + 1) + 2)) * 2) := by ring
    exact Nat.le_of_mul_le_mul_right key hpos
  -- summing the layers `w = 0, …, n`
  set 𝒜all := (range (n + 1)).biUnion 𝒜 with h𝒜all
  have hall : ∑ 𝓛 ∈ 𝒜all, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) <
      2 ^ (2 ^ n) := by
    have hdisj : (↑(range (n + 1)) : Set ℕ).PairwiseDisjoint 𝒜 := by
      intro w _ w' _ hww'
      simp only [Function.onFun]
      rw [disjoint_left]
      intro 𝓛 h1 h2
      simp only [h𝒜, mem_filter, mem_univ, true_and] at h1 h2
      exact hww' (h1.2.2.2.symm.trans h2.2.2.2)
    have h1 : ∑ 𝓛 ∈ 𝒜all, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) ≤
        ∑ w ∈ range (n + 1), X w := by
      rw [h𝒜all, sum_biUnion hdisj]
    have h2 : (∑ w ∈ range (n + 1), X w) * 2 ^ (n + 2) ≤
        ∑ w ∈ range (n + 1), 2 ^ (2 ^ n) * 2 ^ (n - w) := by
      rw [sum_mul]
      refine sum_le_sum fun w hw => ?_
      have hwn : w ≤ n := by rw [mem_range] at hw; omega
      calc X w * 2 ^ (n + 2) = X w * 2 ^ (w + 2) * 2 ^ (n - w) := by
            rw [mul_assoc, ← pow_add]; congr 2; omega
        _ ≤ 2 ^ (2 ^ n) * 2 ^ (n - w) := Nat.mul_le_mul_right _ (hlayer w)
    have h3 : ∑ w ∈ range (n + 1), 2 ^ (2 ^ n) * 2 ^ (n - w) < 2 ^ (2 ^ n) * 2 ^ (n + 2) := by
      rw [← mul_sum]
      have hg : ∑ w ∈ range (n + 1), 2 ^ (n - w) = ∑ w ∈ range (n + 1), 2 ^ w := by
        rw [← sum_range_reflect]
        refine sum_congr rfl fun w hw => ?_
        rw [mem_range] at hw
        congr 1
        omega
      have hgeom : ∑ w ∈ range (n + 1), 2 ^ w < 2 ^ (n + 2) :=
        (sum_two_pow_lt (n + 1)).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
      rw [hg]
      exact Nat.mul_lt_mul_of_pos_left hgeom (by positivity)
    have h4 : (∑ w ∈ range (n + 1), X w) < 2 ^ (2 ^ n) := by
      have := h2.trans_lt h3
      exact Nat.lt_of_mul_lt_mul_right this
    exact h1.trans_lt h4
  obtain ⟨χ, hχ⟩ := exists_colouring_avoiding 𝒜all hall
  refine smallF_le_of ⟨χ, fun 𝓕 hL hM => ?_⟩
  by_contra hbig
  push Not at hbig
  have hm𝓕 : m ≤ #𝓕 := by rw [hmval]; omega
  have hne : 𝓕.Nonempty := card_pos.1 (by omega)
  have hlog : Nat.log 2 #𝓕 ≤ n := by
    have hc : #𝓕 ≤ 2 ^ n := by
      simpa [Fintype.card_finset] using card_le_univ 𝓕
    calc Nat.log 2 #𝓕 ≤ Nat.log 2 (2 ^ n) := Nat.log_mono_right hc
      _ = n := Nat.log_pow (by norm_num) n
  refine hχ 𝓕 (mem_biUnion.2 ⟨Nat.log 2 #𝓕, mem_range.2 (by omega), ?_⟩) hM
  exact mem_filter.2 ⟨mem_univ _, hL, hne, hm𝓕, rfl⟩

end Erdos1183
