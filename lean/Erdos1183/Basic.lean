import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.SupClosed
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 1183: definitions and the Sauer–Shelah bound for `F(n)`

We work with `[n] = Fin n`. A 2-colouring is a map `Finset (Fin n) → Bool`.

* `bigF n` is `F(n)`: the largest `m` such that every 2-colouring of the subsets of
  `[n]` has a monochromatic union-closed family of at least `m` sets
  (see `le_bigF_iff` and `bigF_le_iff`).
* `smallF n` is `f(n)`: the same with families closed under union and intersection
  (see `le_smallF_iff`).

Main results of this file:

* `bigF_le_sum_choose`: if `n * d + 2 < 2 ^ d` then `F(n) ≤ ∑_{k < d} (n choose k)`.
* `half_le_smallF`, `smallF_le_bigF`: the trivial bound `⌈(n+1)/2⌉ ≤ f(n) ≤ F(n)`.
-/

open Finset

namespace Erdos1183

open scoped Classical

/-- A 2-colouring of the subsets of `[n] = Fin n`. -/
abbrev Colouring (n : ℕ) := Finset (Fin n) → Bool

variable {n : ℕ}

/-- A family of subsets of `[n]` closed under (pairwise) unions. -/
def UnionClosed (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ∪ B ∈ 𝓕

/-- A family of subsets of `[n]` closed under (pairwise) unions and intersections. -/
def LatticeClosed (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ∪ B ∈ 𝓕 ∧ A ∩ B ∈ 𝓕

/-- All members of `𝓕` receive the same colour under `χ`. -/
def Monochromatic (χ : Colouring n) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, χ A = χ B

/-- The size of the largest monochromatic union-closed family for `χ`. -/
noncomputable def maxUC (χ : Colouring n) : ℕ :=
  ((univ : Finset (Finset (Finset (Fin n)))).filter
    (fun 𝓕 => UnionClosed 𝓕 ∧ Monochromatic χ 𝓕)).sup card

/-- The size of the largest monochromatic family closed under unions and intersections. -/
noncomputable def maxLat (χ : Colouring n) : ℕ :=
  ((univ : Finset (Finset (Finset (Fin n)))).filter
    (fun 𝓕 => LatticeClosed 𝓕 ∧ Monochromatic χ 𝓕)).sup card

/-- Erdős–Ulam's `F(n)`. -/
noncomputable def bigF (n : ℕ) : ℕ := ⨅ χ : Colouring n, maxUC χ

/-- Erdős–Ulam's `f(n)`. -/
noncomputable def smallF (n : ℕ) : ℕ := ⨅ χ : Colouring n, maxLat χ

/-! ### Unfolding the definitions -/

lemma maxUC_le_iff (χ : Colouring n) (m : ℕ) :
    maxUC χ ≤ m ↔ ∀ 𝓕, UnionClosed 𝓕 → Monochromatic χ 𝓕 → #𝓕 ≤ m := by
  unfold maxUC
  rw [Finset.sup_le_iff]
  simp only [mem_filter, mem_univ, true_and, and_imp]

lemma le_maxUC_iff (χ : Colouring n) (m : ℕ) :
    m ≤ maxUC χ ↔ ∃ 𝓕, UnionClosed 𝓕 ∧ Monochromatic χ 𝓕 ∧ m ≤ #𝓕 := by
  unfold maxUC
  constructor
  · intro h
    obtain ⟨𝓕, h𝓕, heq⟩ := Finset.exists_mem_eq_sup
      (univ.filter fun 𝓕 => UnionClosed 𝓕 ∧ Monochromatic χ 𝓕)
      ⟨∅, mem_filter.2 ⟨mem_univ _, by simp [UnionClosed], by simp [Monochromatic]⟩⟩ card
    rw [heq] at h
    obtain ⟨-, h1, h2⟩ := mem_filter.1 h𝓕
    exact ⟨𝓕, h1, h2, h⟩
  · rintro ⟨𝓕, h1, h2, hm⟩
    exact hm.trans (Finset.le_sup (f := card) (mem_filter.2 ⟨mem_univ _, h1, h2⟩))

lemma le_maxLat_iff (χ : Colouring n) (m : ℕ) :
    m ≤ maxLat χ ↔ ∃ 𝓕, LatticeClosed 𝓕 ∧ Monochromatic χ 𝓕 ∧ m ≤ #𝓕 := by
  unfold maxLat
  constructor
  · intro h
    obtain ⟨𝓕, h𝓕, heq⟩ := Finset.exists_mem_eq_sup
      (univ.filter fun 𝓕 => LatticeClosed 𝓕 ∧ Monochromatic χ 𝓕)
      ⟨∅, mem_filter.2 ⟨mem_univ _, by simp [LatticeClosed], by simp [Monochromatic]⟩⟩ card
    rw [heq] at h
    obtain ⟨-, h1, h2⟩ := mem_filter.1 h𝓕
    exact ⟨𝓕, h1, h2, h⟩
  · rintro ⟨𝓕, h1, h2, hm⟩
    exact hm.trans (Finset.le_sup (f := card) (mem_filter.2 ⟨mem_univ _, h1, h2⟩))

instance : Nonempty (Colouring n) := ⟨fun _ => false⟩

/-- `F(n) ≥ m` iff every colouring has a monochromatic union-closed family of `≥ m` sets. -/
theorem le_bigF_iff (m : ℕ) :
    m ≤ bigF n ↔ ∀ χ : Colouring n, ∃ 𝓕, UnionClosed 𝓕 ∧ Monochromatic χ 𝓕 ∧ m ≤ #𝓕 := by
  unfold bigF
  rw [le_ciInf_iff (OrderBot.bddBelow _)]
  simp only [le_maxUC_iff]

/-- `F(n) ≤ m` iff some colouring has no monochromatic union-closed family of `> m` sets. -/
theorem bigF_le_iff (m : ℕ) :
    bigF n ≤ m ↔
      ∃ χ : Colouring n, ∀ 𝓕, UnionClosed 𝓕 → Monochromatic χ 𝓕 → #𝓕 ≤ m := by
  unfold bigF
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := ciInf_mem (fun χ : Colouring n => maxUC χ)
    have hχ' : maxUC χ = ⨅ χ : Colouring n, maxUC χ := hχ
    refine ⟨χ, (maxUC_le_iff χ m).1 ?_⟩
    rw [hχ']
    exact h
  · rintro ⟨χ, hχ⟩
    exact (ciInf_le (OrderBot.bddBelow _) χ).trans ((maxUC_le_iff χ m).2 hχ)

/-- `f(n) ≥ m` iff every colouring has a monochromatic sublattice of `≥ m` sets. -/
theorem le_smallF_iff (m : ℕ) :
    m ≤ smallF n ↔ ∀ χ : Colouring n, ∃ 𝓕, LatticeClosed 𝓕 ∧ Monochromatic χ 𝓕 ∧ m ≤ #𝓕 := by
  unfold smallF
  rw [le_ciInf_iff (OrderBot.bddBelow _)]
  simp only [le_maxLat_iff]

/-! ### The trivial lower bound `⌈(n+1)/2⌉ ≤ f(n) ≤ F(n)` -/

lemma maxLat_le_maxUC (χ : Colouring n) : maxLat χ ≤ maxUC χ := by
  obtain ⟨𝓕, h1, h2, h3⟩ := (le_maxLat_iff χ _).1 le_rfl
  exact (le_maxUC_iff χ _).2 ⟨𝓕, fun A hA B hB => (h1 A hA B hB).1, h2, h3⟩

theorem smallF_le_bigF : smallF n ≤ bigF n :=
  ciInf_mono (OrderBot.bddBelow _) maxLat_le_maxUC

/-- The initial segment `{0, …, i-1}` of `Fin n`. -/
def seg (n i : ℕ) : Finset (Fin n) := univ.filter (fun x => x.val < i)

lemma seg_mono {i j : ℕ} (h : i ≤ j) : seg n i ⊆ seg n j := by
  intro x hx
  simp only [seg, mem_filter, mem_univ, true_and] at hx ⊢
  omega

theorem half_le_smallF : (n + 2) / 2 ≤ smallF n := by
  classical
  rw [le_smallF_iff]
  intro χ
  set 𝓒 := (range (n + 1)).image (seg n) with h𝓒
  have hcard : #𝓒 = n + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (⟨i, by omega⟩ : Fin n) ∈ seg n j := by simp [seg, h]
      rw [← hij] at this
      simp [seg] at this
    · have : (⟨j, by omega⟩ : Fin n) ∈ seg n i := by simp [seg, h]
      rw [hij] at this
      simp [seg] at this
  have hchain : ∀ A ∈ 𝓒, ∀ B ∈ 𝓒, A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    obtain ⟨i, -, rfl⟩ := mem_image.1 hA
    obtain ⟨j, -, rfl⟩ := mem_image.1 hB
    rcases le_total i j with h | h
    · exact Or.inl (seg_mono h)
    · exact Or.inr (seg_mono h)
  have hlat : ∀ 𝓖 ⊆ 𝓒, LatticeClosed 𝓖 := by
    intro 𝓖 h𝓖 A hA B hB
    rcases hchain A (h𝓖 hA) B (h𝓖 hB) with h | h
    · rw [union_eq_right.2 h, inter_eq_left.2 h]
      exact ⟨hB, hA⟩
    · rw [union_eq_left.2 h, inter_eq_right.2 h]
      exact ⟨hA, hB⟩
  have hsum := card_filter_add_card_filter_not (s := 𝓒) (fun A => χ A = true)
  rw [hcard] at hsum
  by_cases h : (n + 2) / 2 ≤ #(𝓒.filter (fun A => χ A = true))
  · refine ⟨𝓒.filter (fun A => χ A = true), hlat _ (filter_subset _ _), ?_, h⟩
    intro A hA B hB
    rw [(mem_filter.1 hA).2, (mem_filter.1 hB).2]
  · refine ⟨𝓒.filter (fun A => ¬ χ A = true), hlat _ (filter_subset _ _), ?_, by omega⟩
    intro A hA B hB
    have hA' : χ A = false := by simpa using (mem_filter.1 hA).2
    have hB' : χ B = false := by simpa using (mem_filter.1 hB).2
    rw [hA', hB']

/-! ### Independent systems and bad tuples -/

/-- `A₀, …, A_{d-1}` is an *independent system*: each `Aᵢ` has a private element. -/
def Independent {d : ℕ} (A : Fin d → Finset (Fin n)) : Prop :=
  ∀ i, ∃ x ∈ A i, ∀ j, j ≠ i → x ∉ A j

/-- A tuple is *bad* for `χ` if it is independent and all its nonempty unions have
the same colour. -/
def Bad (χ : Colouring n) {d : ℕ} (A : Fin d → Finset (Fin n)) : Prop :=
  Independent A ∧ ∀ I J : Finset (Fin d), I.Nonempty → J.Nonempty → χ (I.sup A) = χ (J.sup A)

/-- The unions of an independent system are pairwise distinct. -/
lemma sup_injective_of_independent {d : ℕ} {A : Fin d → Finset (Fin n)}
    (hA : Independent A) : Function.Injective (fun I : Finset (Fin d) => I.sup A) := by
  intro I J h
  ext i
  obtain ⟨x, hx, hpriv⟩ := hA i
  have key : ∀ K : Finset (Fin d), x ∈ K.sup A ↔ i ∈ K := by
    intro K
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨j, hj, hxj⟩
      by_contra hi
      exact hpriv j (by rintro rfl; exact hi hj) hxj
    · intro hi
      exact ⟨i, hi, hx⟩
  rw [← key I, ← key J]
  simp only at h
  rw [h]

lemma card_colouring : Fintype.card (Colouring n) = 2 ^ (2 ^ n) := by
  simp [Colouring, Fintype.card_finset]

/-- Colourings constant (with value `b`) on a set `S` of subsets: at most `2 ^ (2 ^ n - #S)`. -/
lemma card_const_mul_le (S : Finset (Finset (Fin n))) (b : Bool) :
    #(univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = b)) * 2 ^ #S ≤ 2 ^ (2 ^ n) := by
  classical
  have hS : #S ≤ 2 ^ n := by
    simpa [Fintype.card_finset] using card_le_univ S
  have hinj : #(univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = b)) ≤
      #(univ : Finset (↥(Sᶜ) → Bool)) := by
    refine card_le_card_of_injOn (fun χ B => χ B) (fun _ _ => mem_univ _) ?_
    intro χ hχ χ' hχ' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hχ hχ'
    funext B
    by_cases hB : B ∈ S
    · rw [hχ B hB, hχ' B hB]
    · exact congrFun h ⟨B, mem_compl.2 hB⟩
  rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, card_compl,
    Fintype.card_finset, Fintype.card_fin] at hinj
  calc _ ≤ 2 ^ (2 ^ n - #S) * 2 ^ #S := Nat.mul_le_mul_right _ hinj
    _ = 2 ^ (2 ^ n) := by rw [← pow_add, Nat.sub_add_cancel hS]

lemma card_nonempty_finsets (d : ℕ) :
    #((univ : Finset (Finset (Fin d))).filter Finset.Nonempty) + 1 = 2 ^ d := by
  classical
  have h := card_filter_add_card_filter_not
    (s := (univ : Finset (Finset (Fin d)))) Finset.Nonempty
  have h2 : (univ : Finset (Finset (Fin d))).filter (fun s => ¬ s.Nonempty) = {∅} := by
    ext s
    simp [Finset.not_nonempty_iff_eq_empty]
  rw [h2, card_singleton, card_univ, Fintype.card_finset, Fintype.card_fin] at h
  exact h

/-- For a fixed tuple, few colourings make it bad. -/
lemma card_bad_mul_le {d : ℕ} (A : Fin d → Finset (Fin n)) :
    #(univ.filter (fun χ : Colouring n => Bad χ A)) * 2 ^ (2 ^ d) ≤ 4 * 2 ^ (2 ^ n) := by
  classical
  by_cases hA : Independent A
  swap
  · have : univ.filter (fun χ : Colouring n => Bad χ A) = ∅ := by
      ext χ
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hA h.1
    rw [this]
    simp
  set S := ((univ : Finset (Finset (Fin d))).filter Finset.Nonempty).image (fun I => I.sup A)
    with hSdef
  have hScard : #S + 1 = 2 ^ d := by
    rw [hSdef, card_image_of_injective _ (sup_injective_of_independent hA)]
    exact card_nonempty_finsets d
  have hsub : univ.filter (fun χ : Colouring n => Bad χ A) ⊆
      univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = true) ∪
        univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = false) := by
    intro χ hχ
    have hbad := (mem_filter.1 hχ).2
    simp only [mem_union, mem_filter, mem_univ, true_and]
    by_cases hex : ∃ B ∈ S, χ B = true
    · left
      obtain ⟨B₀, hB₀, hχB₀⟩ := hex
      obtain ⟨I₀, hI₀, rfl⟩ := mem_image.1 hB₀
      intro B hB
      obtain ⟨I, hI, rfl⟩ := mem_image.1 hB
      rw [hbad.2 I I₀ (mem_filter.1 hI).2 (mem_filter.1 hI₀).2, hχB₀]
    · right
      push Not at hex
      intro B hB
      simpa using hex B hB
  have h1 := card_const_mul_le S true
  have h2 := card_const_mul_le S false
  calc #(univ.filter (fun χ : Colouring n => Bad χ A)) * 2 ^ (2 ^ d)
      ≤ (#(univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = true)) +
          #(univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = false))) * 2 ^ (2 ^ d) :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans (card_union_le _ _))
    _ = (#(univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = true)) * 2 ^ #S +
          #(univ.filter (fun χ : Colouring n => ∀ B ∈ S, χ B = false)) * 2 ^ #S) * 2 := by
        rw [← hScard, pow_succ]
        ring
    _ ≤ (2 ^ (2 ^ n) + 2 ^ (2 ^ n)) * 2 := Nat.mul_le_mul_right _ (Nat.add_le_add h1 h2)
    _ = 4 * 2 ^ (2 ^ n) := by ring

/-- **First-moment step.** If `n d + 2 < 2 ^ d`, some colouring has no bad `d`-tuple. -/
theorem exists_good_colouring {d : ℕ} (hd : n * d + 2 < 2 ^ d) :
    ∃ χ : Colouring n, ∀ A : Fin d → Finset (Fin n), ¬ Bad χ A := by
  classical
  by_contra h
  push Not at h
  have hcover : (univ : Finset (Colouring n)) ⊆
      (univ : Finset (Fin d → Finset (Fin n))).biUnion
        (fun A => univ.filter (fun χ : Colouring n => Bad χ A)) := by
    intro χ _
    obtain ⟨A, hA⟩ := h χ
    exact mem_biUnion.2 ⟨A, mem_univ _, mem_filter.2 ⟨mem_univ _, hA⟩⟩
  have hc := (card_le_card hcover).trans card_biUnion_le
  rw [card_univ, card_colouring] at hc
  have htuples : Fintype.card (Fin d → Finset (Fin n)) = 2 ^ (n * d) := by
    rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin, pow_mul]
  have hsum : (∑ A : Fin d → Finset (Fin n),
      #(univ.filter (fun χ : Colouring n => Bad χ A))) * 2 ^ (2 ^ d) ≤
      2 ^ (n * d) * (4 * 2 ^ (2 ^ n)) := by
    rw [Finset.sum_mul, ← htuples, ← card_univ, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun A _ => card_bad_mul_le A
  have hlt : 2 ^ (n * d + 2) < 2 ^ (2 ^ d) := Nat.pow_lt_pow_right (by norm_num) hd
  have : 2 ^ (2 ^ n) * 2 ^ (2 ^ d) < 2 ^ (2 ^ n) * 2 ^ (2 ^ d) := by
    calc 2 ^ (2 ^ n) * 2 ^ (2 ^ d)
        ≤ (∑ A : Fin d → Finset (Fin n),
            #(univ.filter (fun χ : Colouring n => Bad χ A))) * 2 ^ (2 ^ d) :=
          Nat.mul_le_mul_right _ hc
      _ ≤ 2 ^ (n * d) * (4 * 2 ^ (2 ^ n)) := hsum
      _ = 2 ^ (n * d + 2) * 2 ^ (2 ^ n) := by rw [pow_add]; ring
      _ < 2 ^ (2 ^ d) * 2 ^ (2 ^ n) := Nat.mul_lt_mul_of_pos_right hlt (pow_pos (by norm_num) _)
      _ = 2 ^ (2 ^ n) * 2 ^ (2 ^ d) := by ring
  exact lt_irrefl _ this

/-- For a colouring with no bad `d`-tuple, a monochromatic union-closed family shatters
no set of size `≥ d`. -/
lemma card_lt_of_shatters {χ : Colouring n} {d : ℕ}
    (hχ : ∀ A : Fin d → Finset (Fin n), ¬ Bad χ A)
    {𝓕 : Finset (Finset (Fin n))} (hU : UnionClosed 𝓕) (hM : Monochromatic χ 𝓕)
    {s : Finset (Fin n)} (hs : 𝓕.Shatters s) : #s < d := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨t, hts, htd⟩ := exists_subset_card_eq hlt
  have ht : 𝓕.Shatters t := hs.mono_right hts
  let e : Fin d ≃ t := (t.equivFinOfCardEq htd).symm
  have hx : ∀ i, ∃ B ∈ 𝓕, t ∩ B = {(e i : Fin n)} :=
    fun i => ht.exists_inter_eq_singleton (e i).2
  choose A hA𝓕 hAt using hx
  apply hχ A
  have hsup : SupClosed (𝓕 : Set (Finset (Fin n))) :=
    fun a ha b hb => hU a ha b hb
  refine ⟨fun i => ⟨e i, ?_, fun j hji hmem => ?_⟩, fun I J hI hJ => ?_⟩
  · have : (e i : Fin n) ∈ t ∩ A i := by rw [hAt i]; exact mem_singleton_self _
    exact (mem_inter.1 this).2
  · have : (e i : Fin n) ∈ t ∩ A j := mem_inter.2 ⟨(e i).2, hmem⟩
    rw [hAt j, mem_singleton] at this
    exact hji (e.injective (Subtype.ext this)).symm
  · exact hM _ (hsup.finsetSup_mem hI fun i _ => hA𝓕 i) _
      (hsup.finsetSup_mem hJ fun i _ => hA𝓕 i)

/-- **Theorem (upper bound for `F(n)`).** If `n d + 2 < 2 ^ d`, then
`F(n) ≤ ∑_{k < d} (n choose k)`. -/
theorem bigF_le_sum_choose {d : ℕ} (hd : n * d + 2 < 2 ^ d) :
    bigF n ≤ ∑ k ∈ range d, n.choose k := by
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hd
    · exact h
  obtain ⟨χ, hχ⟩ := exists_good_colouring hd
  refine (bigF_le_iff _).2 ⟨χ, fun 𝓕 hU hM => ?_⟩
  have hvc : 𝓕.vcDim < d := by
    unfold vcDim
    rw [Finset.sup_lt_iff (by simpa using hd0)]
    intro s hs
    exact card_lt_of_shatters hχ hU hM (mem_shatterer.1 hs)
  calc #𝓕 ≤ #𝓕.shatterer := card_le_card_shatterer 𝓕
    _ ≤ ∑ k ∈ Iic 𝓕.vcDim, (Fintype.card (Fin n)).choose k := card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ range d, n.choose k := by
      rw [Fintype.card_fin]
      apply sum_le_sum_of_subset
      intro k hk
      rw [mem_Iic] at hk
      rw [mem_range]
      omega

end Erdos1183
