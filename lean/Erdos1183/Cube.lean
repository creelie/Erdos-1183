import Erdos1183.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Labelled cubes, and how many orderings make them monochromatic

A *labelling* `lab : α → Fin t ⊕ Bool` of a finite ground set describes a `t`-dimensional
"hole cube": the elements labelled `inr true` form the fixed part of the top, those labelled
`inl i` form the `i`-th generator, and those labelled `inr false` are never used. For
`x : Fin t → Bool` the member `cubeSet lab x` is the top with the generators `i` such that
`x i = true` removed.

`Ncount χ lab` counts the permutations `σ` of the ground set for which the cube is
monochromatic for the colouring `S ↦ χ (σ S)`. The main fact is that `Ncount` depends
only on the sizes of the label classes (`Ncount_eq_of_card_fiber_eq`). Patterns `π` on a window
of `M` positions describe cubes inside that window (`patLab`, `cubeSet_patLab`).
-/

open Finset

namespace Erdos1183

open scoped Classical

section Labels

variable {α : Type*} [Fintype α] [DecidableEq α] {G : Type*} [Fintype G] [DecidableEq G]

set_option linter.unusedSectionVars false

/-- The member of the hole cube of `lab` in which the generators with `x i = true` are
removed. -/
def cubeSet (lab : α → G ⊕ Bool) (x : G → Bool) : Finset α :=
  univ.filter fun p => lab p = Sum.inr true ∨ ∃ i, lab p = Sum.inl i ∧ x i = false

/-- The hole cube of `lab` is monochromatic for `χ`. -/
def CubeMono (χ : Finset α → Bool) (lab : α → G ⊕ Bool) : Prop :=
  ∀ x, χ (cubeSet lab x) = χ (cubeSet lab fun _ => false)

/-- The colouring `S ↦ χ (σ S)`. -/
def pull (χ : Finset α → Bool) (σ : Equiv.Perm α) : Finset α → Bool :=
  fun S => χ (S.map σ.toEmbedding)

/-- The number of permutations making the hole cube of `lab` monochromatic. -/
noncomputable def Ncount (χ : Finset α → Bool) (lab : α → G ⊕ Bool) : ℕ :=
  #(univ.filter fun σ : Equiv.Perm α => CubeMono (pull χ σ) lab)

lemma mem_cubeSet (lab : α → G ⊕ Bool) (x : G → Bool) (p : α) :
    p ∈ cubeSet lab x ↔ lab p = Sum.inr true ∨ ∃ i, lab p = Sum.inl i ∧ x i = false := by
  simp [cubeSet]

/-- Renaming the generators along an embedding does not change the cube. -/
lemma cubeSet_relabel {G' : Type*} [Fintype G'] [DecidableEq G'] (ι : G ↪ G') (lab : α → G ⊕ Bool) (y : G' → Bool) :
    cubeSet (Sum.map ι id ∘ lab) y = cubeSet lab (y ∘ ι) := by
  ext p
  simp only [mem_cubeSet, Function.comp_apply]
  rcases lab p with i | b <;> simp

lemma Ncount_relabel {G' : Type*} [Fintype G'] [DecidableEq G'] (χ : Finset α → Bool)
    (ι : G ↪ G') (lab : α → G ⊕ Bool) : Ncount χ (Sum.map ι id ∘ lab) = Ncount χ lab := by
  have key : ∀ σ, CubeMono (pull χ σ) (Sum.map ι id ∘ lab) ↔ CubeMono (pull χ σ) lab := by
    intro σ
    unfold CubeMono
    simp only [cubeSet_relabel]
    constructor
    · intro h x
      let y : G' → Bool := fun k => if h : ∃ i, ι i = k then x h.choose else false
      have hy : y ∘ ι = x := by
        funext i
        have hex : ∃ i', ι i' = ι i := ⟨i, rfl⟩
        simp only [Function.comp_apply, y, hex, dite_true]
        rw [ι.injective hex.choose_spec]
      have h1 := h y
      rw [hy] at h1
      exact h1
    · intro h y
      exact h (y ∘ ι)
  unfold Ncount
  simp only [key]

lemma cubeSet_comp (lab : α → G ⊕ Bool) (τ : Equiv.Perm α) (x : G → Bool) :
    cubeSet (lab ∘ τ) x = (cubeSet lab x).map τ.symm.toEmbedding := by
  ext p
  simp only [cubeSet, Function.comp_apply, mem_filter, mem_univ, true_and, mem_map_equiv,
    Equiv.symm_symm]

lemma pull_cubeSet_comp (χ : Finset α → Bool) (σ τ : Equiv.Perm α) (lab : α → G ⊕ Bool)
    (x : G → Bool) :
    pull χ σ (cubeSet (lab ∘ τ) x) = pull χ (τ.symm.trans σ) (cubeSet lab x) := by
  simp only [pull, cubeSet_comp, map_map]
  rfl

lemma cubeMono_comp_iff (χ : Finset α → Bool) (σ τ : Equiv.Perm α) (lab : α → G ⊕ Bool) :
    CubeMono (pull χ σ) (lab ∘ τ) ↔ CubeMono (pull χ (τ.symm.trans σ)) lab := by
  simp only [CubeMono, pull_cubeSet_comp]

lemma Ncount_comp (χ : Finset α → Bool) (lab : α → G ⊕ Bool) (τ : Equiv.Perm α) :
    Ncount χ (lab ∘ τ) = Ncount χ lab := by
  unfold Ncount
  have key : ∀ σ : Equiv.Perm α, Equiv.mulRight τ⁻¹ σ = τ.symm.trans σ := fun σ => by
    ext; simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  refine card_equiv (Equiv.mulRight τ⁻¹) fun σ => ?_
  simp only [mem_filter, mem_univ, true_and, cubeMono_comp_iff, key]

/-- Two labellings with the same class sizes differ by a permutation. -/
lemma exists_perm_of_card_fiber_eq (lab lab' : α → G ⊕ Bool)
    (h : ∀ ℓ, #(univ.filter fun p => lab p = ℓ) = #(univ.filter fun p => lab' p = ℓ)) :
    ∃ τ : Equiv.Perm α, lab' = lab ∘ τ := by
  have e : ∀ ℓ, {p // lab' p = ℓ} ≃ {p // lab p = ℓ} := fun ℓ =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, h ℓ])
  refine ⟨(Equiv.sigmaFiberEquiv lab').symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv lab)), ?_⟩
  funext p
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaFiberEquiv_apply]
  exact ((e (lab' p)) ((Equiv.sigmaFiberEquiv lab').symm p).2).2.symm

lemma Ncount_eq_of_card_fiber_eq (χ : Finset α → Bool) (lab lab' : α → G ⊕ Bool)
    (h : ∀ ℓ, #(univ.filter fun p => lab p = ℓ) = #(univ.filter fun p => lab' p = ℓ)) :
    Ncount χ lab' = Ncount χ lab := by
  obtain ⟨τ, rfl⟩ := exists_perm_of_card_fiber_eq lab lab' h
  exact Ncount_comp χ lab τ

/-- If two labellings agree on all class sizes but one, they agree on that one too. -/
lemma card_fiber_eq_of_ne (lab lab' : α → G ⊕ Bool) (ℓ₀ : G ⊕ Bool)
    (h : ∀ ℓ, ℓ ≠ ℓ₀ →
      #(univ.filter fun p => lab p = ℓ) = #(univ.filter fun p => lab' p = ℓ)) :
    ∀ ℓ, #(univ.filter fun p => lab p = ℓ) = #(univ.filter fun p => lab' p = ℓ) := by
  have hsum : ∀ f : α → G ⊕ Bool,
      ∑ ℓ, #(univ.filter fun p => f p = ℓ) = Fintype.card α := fun f => by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := f) (t := univ) (fun _ _ => mem_univ _)]
  intro ℓ
  by_cases hℓ : ℓ = ℓ₀
  · subst hℓ
    have h1 := hsum lab
    have h2 := hsum lab'
    rw [← add_sum_erase _ _ (mem_univ ℓ)] at h1 h2
    rw [sum_congr rfl fun ℓ' hℓ' => h ℓ' (ne_of_mem_erase hℓ')] at h1
    omega
  · exact h ℓ hℓ

end Labels

section Pattern

variable {n t M r : ℕ}

/-- How a pattern letter labels a position: fixed-`true` coordinates are removed from the
top, fixed-`false` coordinates are kept, and direction `i` becomes generator `i`. -/
def patVal : Bool ⊕ Fin t → Fin t ⊕ Bool := Sum.elim (fun b => Sum.inr (!b)) Sum.inl

/-- The labelling of `Fin n` given by a pattern `π` on the first `M` positions, followed by
`r` positions of fixed top and then unused positions. -/
def patLab (M r : ℕ) (π : Fin M → Bool ⊕ Fin t) : Fin n → Fin t ⊕ Bool := fun p =>
  if hp : p.val < M then patVal (π ⟨p.val, hp⟩)
  else if p.val < M + r then Sum.inr true else Sum.inr false

/-- The top `{0, …, M + r - 1}` with the positions `q < M` where `w q = true` removed. -/
def topMinus (M r : ℕ) (w : Fin M → Bool) : Finset (Fin n) :=
  univ.filter fun p => p.val < M + r ∧ (if hp : p.val < M then w ⟨p.val, hp⟩ = false else True)

lemma cubeSet_patLab (M r : ℕ) (π : Fin M → Bool ⊕ Fin t) (x : Fin t → Bool) :
    cubeSet (patLab (n := n) M r π) x = topMinus M r fun q => (π q).elim id x := by
  ext p
  rw [mem_cubeSet]
  simp only [topMinus, patLab, mem_filter, mem_univ, true_and]
  by_cases hp : p.val < M
  · simp only [hp, dite_true]
    have hMr : p.val < M + r := by omega
    rcases hπ : π ⟨p.val, hp⟩ with b | i
    · cases b <;> simp [patVal, hMr]
    · simp [patVal, hMr]
  · simp only [hp, dite_false, and_true]
    by_cases hr : p.val < M + r
    · simp [hr]
    · simp [hr]

lemma patVal_eq_inl (a : Bool ⊕ Fin t) (i : Fin t) :
    patVal a = Sum.inl i ↔ a = Sum.inr i := by
  rcases a with b | j <;> simp [patVal]

lemma patVal_eq_inr_true (a : Bool ⊕ Fin t) : patVal a = Sum.inr true ↔ a = Sum.inl false := by
  rcases a with b | j <;> simp [patVal]

/-- Class sizes of `patLab`, part 1: the positions below `M`. -/
lemma card_patLab_lt (hM : M ≤ n) (r : ℕ) (π : Fin M → Bool ⊕ Fin t) (ℓ : Fin t ⊕ Bool) :
    #(univ.filter fun p : Fin n => patLab M r π p = ℓ ∧ p.val < M) =
      #(univ.filter fun q : Fin M => patVal (π q) = ℓ) := by
  rw [← card_map (Fin.castLEEmb hM)]
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
  constructor
  · rintro ⟨h, hp⟩
    refine ⟨⟨p.val, hp⟩, ?_, Fin.ext rfl⟩
    simpa [patLab, hp] using h
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, by simp⟩
    simpa [patLab] using hq

lemma card_Ico_fin (a c : ℕ) (hc : c ≤ n) :
    #(univ.filter fun p : Fin n => a ≤ p.val ∧ p.val < c) = c - a := by
  rw [← card_map Fin.valEmbedding, ← Nat.card_Ico]
  congr 1
  ext k
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hk
    exact ⟨⟨k, by omega⟩, hk, rfl⟩

lemma card_patLab_inl (hM : M ≤ n) (r : ℕ) (π : Fin M → Bool ⊕ Fin t) (i : Fin t) :
    #(univ.filter fun p : Fin n => patLab M r π p = Sum.inl i) =
      #(univ.filter fun q : Fin M => π q = Sum.inr i) := by
  have h := card_filter_add_card_filter_not
    (s := univ.filter fun p : Fin n => patLab M r π p = Sum.inl i) (fun p => p.val < M)
  rw [filter_filter, filter_filter, card_patLab_lt hM] at h
  have h0 : (univ.filter fun p : Fin n => patLab M r π p = Sum.inl i ∧ ¬ p.val < M) = ∅ := by
    ext p
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro h1 h2
    simp only [patLab, h2, dite_false] at h1
    split_ifs at h1
  rw [h0, card_empty, add_zero] at h
  rw [← h]
  simp only [patVal_eq_inl]

lemma card_patLab_true (hMr : M + r ≤ n) (π : Fin M → Bool ⊕ Fin t) :
    #(univ.filter fun p : Fin n => patLab M r π p = Sum.inr true) =
      r + #(univ.filter fun q : Fin M => π q = Sum.inl false) := by
  have h := card_filter_add_card_filter_not
    (s := univ.filter fun p : Fin n => patLab M r π p = Sum.inr true) (fun p => p.val < M)
  rw [filter_filter, filter_filter, card_patLab_lt (by omega)] at h
  have h1 : (univ.filter fun p : Fin n => patLab M r π p = Sum.inr true ∧ ¬ p.val < M) =
      univ.filter fun p : Fin n => M ≤ p.val ∧ p.val < M + r := by
    ext p
    simp only [mem_filter, mem_univ, true_and]
    by_cases hp : p.val < M
    · simp [hp]
    · simp only [patLab, hp, dite_false, not_false_eq_true, and_true]
      by_cases hr : p.val < M + r
      · simp [hr]; omega
      · simp [hr]
  rw [h1, card_Ico_fin _ _ hMr] at h
  rw [← h]
  simp only [patVal_eq_inr_true]
  omega

end Pattern

end Erdos1183
