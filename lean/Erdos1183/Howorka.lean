import Erdos1183.Hilbert
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Arithmetic progressions and Howorka's theorem

For a colouring `χ(S) = g(|S|)` by cardinality, a monochromatic arithmetic progression of sizes
gives a large monochromatic union-closed family and a monochromatic sublattice.

* `ap_family`: if `g` is constant on `a, a + e, …, a + (k - 1) e ≤ n`, then `χ` has a
  monochromatic union-closed family with `∑_{i < k} C(⌊a/e⌋ + k - 1, i)` members.
* `ap_lattice`: under the same hypothesis `χ` has a monochromatic sublattice with `2^(k-1)`
  members.
* `exists_vdW`: van der Waerden's theorem, derived from the Hales–Jewett theorem.
* `howorka`: if `n ≥ 2W`, where every colouring of `{0, …, W - 1}` has a monochromatic `k`-term
  progression, then every cardinality colouring of `2^[n]` has a monochromatic union-closed
  family with at least `C(⌊n/(2W)⌋ + k - 1, k - 1)` members.
-/

open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

section Blocks

variable {n : ℕ}

/-- The set `D ∪ ⋃_{i ∈ I} X_i ⊆ [n]`, where `D = {0, …, a₀ - 1}` and `X_i` is the block of
`e` consecutive elements starting at `a₀ + i e`. -/
def blockSet (n a₀ e : ℕ) (I : Finset ℕ) : Finset (Fin n) :=
  univ.filter fun x => x.val < a₀ ∨ (a₀ ≤ x.val ∧ (x.val - a₀) / e ∈ I)

lemma blockSet_union (a₀ e : ℕ) (I J : Finset ℕ) :
    blockSet n a₀ e (I ∪ J) = blockSet n a₀ e I ∪ blockSet n a₀ e J := by
  ext x
  simp only [blockSet, mem_filter, mem_univ, true_and, mem_union]
  tauto

lemma blockSet_inter (a₀ e : ℕ) (I J : Finset ℕ) :
    blockSet n a₀ e (I ∩ J) = blockSet n a₀ e I ∩ blockSet n a₀ e J := by
  ext x
  simp only [blockSet, mem_filter, mem_univ, true_and, mem_inter]
  tauto

lemma lt_of_block {a₀ e b i : ℕ} (hb : a₀ + b * e ≤ n) (hi : i < b) :
    a₀ + i * e + e ≤ n := by
  have := Nat.mul_le_mul_right e (show i + 1 ≤ b from hi)
  rw [add_one_mul] at this
  omega

lemma mem_blockSet_iff {a₀ e b : ℕ} (he : 1 ≤ e) (hb : a₀ + b * e ≤ n) (I : Finset ℕ) {i : ℕ}
    (hi : i < b) :
    (⟨a₀ + i * e, by have := lt_of_block hb hi; omega⟩ : Fin n) ∈ blockSet n a₀ e I ↔
      i ∈ I := by
  have hdiv : (a₀ + i * e - a₀) / e = i := by
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ he]
  simp only [blockSet, mem_filter, mem_univ, true_and, hdiv]
  constructor
  · rintro (h | ⟨_, h⟩)
    · omega
    · exact h
  · intro h
    exact Or.inr ⟨by omega, h⟩

lemma blockSet_injOn {a₀ e b : ℕ} (he : 1 ≤ e) (hb : a₀ + b * e ≤ n) :
    Set.InjOn (blockSet n a₀ e) ((range b).powerset : Set (Finset ℕ)) := by
  intro I hI J hJ hIJ
  have hI' : I ⊆ range b := mem_powerset.1 (mem_coe.1 hI)
  have hJ' : J ⊆ range b := mem_powerset.1 (mem_coe.1 hJ)
  ext i
  by_cases hi : i < b
  · rw [← mem_blockSet_iff he hb I hi, ← mem_blockSet_iff he hb J hi, hIJ]
  · have h1 : i ∉ I := fun h => hi (mem_range.1 (hI' h))
    have h2 : i ∉ J := fun h => hi (mem_range.1 (hJ' h))
    simp [h1, h2]

/-- The size of `D ∪ ⋃_{i ∈ I} X_i` is `a₀ + e |I|`. -/
lemma card_blockSet {a₀ e b : ℕ} (he : 1 ≤ e) (hb : a₀ + b * e ≤ n) {I : Finset ℕ}
    (hI : I ⊆ range b) :
    #(blockSet n a₀ e I) = a₀ + e * #I := by
  have hmap : (blockSet n a₀ e I).map Fin.valEmbedding =
      range a₀ ∪ I.biUnion fun i => Ico (a₀ + i * e) (a₀ + i * e + e) := by
    ext x
    simp only [mem_map, blockSet, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_union, mem_range, mem_biUnion, mem_Ico]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with h | ⟨h1, h2⟩
      · exact Or.inl h
      · right
        refine ⟨_, h2, ?_, ?_⟩
        · have := Nat.div_mul_le_self (y.val - a₀) e
          omega
        · have := Nat.lt_div_mul_add (a := y.val - a₀) (show 0 < e by omega)
          omega
    · rintro (h | ⟨i, hi, h1, h2⟩)
      · refine ⟨⟨x, ?_⟩, Or.inl h, rfl⟩
        have : 0 ≤ b * e := Nat.zero_le _
        omega
      · have hib : i < b := mem_range.1 (hI hi)
        have hlt := lt_of_block hb hib
        refine ⟨⟨x, by omega⟩, Or.inr ⟨show a₀ ≤ x by omega, ?_⟩, rfl⟩
        have : (x - a₀) / e = i := by
          apply Nat.div_eq_of_lt_le
          · omega
          · rw [add_one_mul]
            omega
        simpa [this] using hi
  rw [← card_map Fin.valEmbedding, hmap, card_union_of_disjoint, card_biUnion]
  · simp only [card_range, Nat.card_Ico, add_tsub_cancel_left, sum_const, smul_eq_mul]
    rw [mul_comm]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_Ico] at hx hx'
    rcases lt_or_gt_of_ne hij with h | h
    · have := Nat.mul_le_mul_right e (show i + 1 ≤ j from h)
      rw [add_one_mul] at this
      omega
    · have := Nat.mul_le_mul_right e (show j + 1 ≤ i from h)
      rw [add_one_mul] at this
      omega
  · rw [disjoint_left]
    intro x hx hx'
    rw [mem_range] at hx
    obtain ⟨i, _, hi⟩ := mem_biUnion.1 hx'
    rw [mem_Ico] at hi
    omega

end Blocks

section Progressions

variable {κ : Type*} {n : ℕ}

/-- The number of subsets of `[b]` with at least `b - (k - 1)` elements. -/
lemma card_large_subsets (q k : ℕ) (hk : 1 ≤ k) :
    #((range (q + (k - 1))).powerset.filter fun I => q ≤ #I) =
      ∑ i ∈ range k, (q + (k - 1)).choose i := by
  set b := q + (k - 1) with hb
  rw [card_filter, sum_powerset_apply_card (f := fun m => if q ≤ m then 1 else 0), card_range,
    ← sum_range_reflect]
  have hset : range k = (range (b + 1)).filter fun j => j < k := by
    ext j
    simp only [mem_range, mem_filter]
    omega
  rw [hset, sum_filter]
  refine sum_congr rfl fun j hj => ?_
  have hjb : j ≤ b := by
    rw [mem_range] at hj
    omega
  simp only [smul_eq_mul]
  rw [show b + 1 - 1 - j = b - j by omega, Nat.choose_symm hjb]
  by_cases hjk : j < k
  · simp [hjk, show q ≤ b - j by omega]
  · simp [hjk, show ¬ q ≤ b - j by omega]

/-- **Progressions give union-closed families.** If `g` is constant on the progression
`a, a + e, …, a + (k - 1) e` and `a + (k - 1) e ≤ n`, then the cardinality colouring
`S ↦ g |S|` of `2^[n]` has a monochromatic union-closed family with
`∑_{i < k} C(⌊a/e⌋ + k - 1, i)` members. -/
theorem ap_family (g : ℕ → κ) {a e k : ℕ} (he : 1 ≤ e) (hk : 1 ≤ k)
    (han : a + (k - 1) * e ≤ n) (hg : ∀ i < k, g (a + i * e) = g a) :
    ∃ 𝓕 : Finset (Finset (Fin n)), UnionClosed 𝓕 ∧ Monochromatic (fun S => g #S) 𝓕 ∧
      #𝓕 = ∑ i ∈ range k, (a / e + (k - 1)).choose i := by
  have hdiv := Nat.mod_add_div a e
  have hb : a % e + (a / e + (k - 1)) * e ≤ n := by
    have : a / e * e = e * (a / e) := mul_comm _ _
    rw [add_mul]
    omega
  set D := (range (a / e + (k - 1))).powerset.filter fun I => a / e ≤ #I with hD
  have hsub : ∀ I ∈ D, I ⊆ range (a / e + (k - 1)) := fun I hI =>
    mem_powerset.1 (mem_filter.1 hI).1
  have key : ∀ A ∈ D.image (blockSet n (a % e) e), g #A = g a := by
    intro A hA
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hA
    rw [card_blockSet he hb (hsub I hI)]
    have hqI : a / e ≤ #I := (mem_filter.1 hI).2
    have hIb : #I ≤ a / e + (k - 1) := by
      simpa using card_le_card (hsub I hI)
    obtain ⟨j, hj⟩ : ∃ j, #I = a / e + j := ⟨#I - a / e, by omega⟩
    have hcard : a % e + e * #I = a + j * e := by
      rw [hj, mul_add, mul_comm e j]
      omega
    rw [hcard]
    exact hg j (by omega)
  refine ⟨D.image (blockSet n (a % e) e), ?_, ?_, ?_⟩
  · intro A hA B hB
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hA
    obtain ⟨J, hJ, rfl⟩ := mem_image.1 hB
    rw [← blockSet_union]
    refine mem_image.2 ⟨I ∪ J, ?_, rfl⟩
    rw [hD, mem_filter, mem_powerset] at hI hJ ⊢
    exact ⟨union_subset hI.1 hJ.1, le_trans hI.2 (card_le_card subset_union_left)⟩
  · intro A hA B hB
    show g #A = g #B
    rw [key A hA, key B hB]
  · rw [card_image_of_injOn ((blockSet_injOn he hb).mono fun I hI => ?_)]
    · exact card_large_subsets _ _ hk
    · exact mem_coe.2 (mem_powerset.2 (hsub I (mem_coe.1 hI)))

/-- **Progressions give sublattices.** Under the same hypothesis the cardinality colouring
has a monochromatic family with `2^(k-1)` members closed under unions and intersections. -/
theorem ap_lattice (g : ℕ → κ) {a e k : ℕ} (he : 1 ≤ e) (hk : 1 ≤ k)
    (han : a + (k - 1) * e ≤ n) (hg : ∀ i < k, g (a + i * e) = g a) :
    ∃ 𝓛 : Finset (Finset (Fin n)), LatticeClosed 𝓛 ∧ Monochromatic (fun S => g #S) 𝓛 ∧
      #𝓛 = 2 ^ (k - 1) := by
  have key : ∀ A ∈ (range (k - 1)).powerset.image (blockSet n a e), g #A = g a := by
    intro A hA
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hA
    have hI' := mem_powerset.1 hI
    rw [card_blockSet he han hI', mul_comm]
    have : #I ≤ k - 1 := by simpa using card_le_card hI'
    exact hg _ (by omega)
  refine ⟨(range (k - 1)).powerset.image (blockSet n a e), ?_, ?_, ?_⟩
  · intro A hA B hB
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hA
    obtain ⟨J, hJ, rfl⟩ := mem_image.1 hB
    rw [mem_powerset] at hI hJ
    rw [← blockSet_union, ← blockSet_inter]
    exact ⟨mem_image.2 ⟨I ∪ J, mem_powerset.2 (union_subset hI hJ), rfl⟩,
      mem_image.2 ⟨I ∩ J, mem_powerset.2 (inter_subset_left.trans hI), rfl⟩⟩
  · intro A hA B hB
    show g #A = g #B
    rw [key A hA, key B hB]
  · rw [card_image_of_injOn (blockSet_injOn he han), card_powerset, card_range]

end Progressions

section VanDerWaerden

/-- `W` is a van der Waerden bound for `k`-term progressions in the colours `κ`: every colouring
of `{0, 1, …, W - 1}` is constant on some progression `a, a + e, …, a + (k - 1) e` with
`e ≥ 1`. -/
def VdW (κ : Type*) (k W : ℕ) : Prop :=
  ∀ g : ℕ → κ, ∃ a e, 1 ≤ e ∧ a + (k - 1) * e < W ∧ ∀ i < k, g (a + i * e) = g a

/-- **Van der Waerden's theorem**, derived from the Hales–Jewett theorem by summing
coordinates. -/
theorem exists_vdW (κ : Type*) [Finite κ] (k : ℕ) : ∃ W, VdW κ k W := by
  obtain ⟨ι, _, h⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin (k + 1)) κ
  refine ⟨Fintype.card ι * k + 1, fun g => ?_⟩
  obtain ⟨l, c, hc⟩ := h fun x => g (∑ i, (x i).val)
  set E := #(univ.filter fun i => l.idxFun i = none) with hEdef
  set A := ∑ i, ((l.idxFun i).getD 0).val with hAdef
  have hsum : ∀ x : Fin (k + 1), ∑ i, (l x i).val = A + x.val * E := by
    intro x
    have : ∀ i, (l x i).val =
        ((l.idxFun i).getD 0).val + if l.idxFun i = none then x.val else 0 := by
      intro i
      cases h : l.idxFun i <;> simp [h]
    rw [sum_congr rfl fun i _ => this i, sum_add_distrib, sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul, mul_comm]
  have hE : 1 ≤ E := by
    obtain ⟨i₀, hi₀⟩ := l.proper
    exact card_pos.2 ⟨i₀, mem_filter.2 ⟨mem_univ _, hi₀⟩⟩
  refine ⟨A, E, hE, ?_, ?_⟩
  · have hle : ∑ i, (l (Fin.last k) i).val ≤ ∑ _i : ι, k :=
      sum_le_sum fun i _ => Fin.is_le _
    rw [hsum, sum_const, card_univ, smul_eq_mul, Fin.val_last] at hle
    have : (k - 1) * E ≤ k * E := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  · intro i hi
    have h1 := hc ⟨i, by omega⟩
    have h0 := hc 0
    simp only at h1 h0
    rw [hsum] at h1 h0
    rw [h1, ← h0]
    simp

/-- **Howorka's theorem.** Let `k ≥ 2` and let `W` be a van der Waerden bound for `k`-term
progressions. If `n ≥ 2W`, every cardinality colouring of `2^[n]` has a monochromatic
union-closed family with at least `C(⌊n/(2W)⌋ + k - 1, k - 1)` members, and this number is at
least `(⌊n/(2W)⌋ + 1)^(k-1) / (k-1)!`. -/
theorem howorka {κ : Type*} {k W n : ℕ} (hk : 2 ≤ k) (hW : VdW κ k W) (hn : 2 * W ≤ n)
    (g : ℕ → κ) :
    ∃ 𝓕 : Finset (Finset (Fin n)), UnionClosed 𝓕 ∧ Monochromatic (fun S => g #S) 𝓕 ∧
      (n / (2 * W) + (k - 1)).choose (k - 1) ≤ #𝓕 ∧
      (n / (2 * W) + 1) ^ (k - 1) ≤ (k - 1).factorial * #𝓕 := by
  obtain ⟨a', e, he, hae, hg⟩ := hW fun j => g (n - W + j)
  have heW : e < W := by
    have : e ≤ (k - 1) * e := Nat.le_mul_of_pos_left e (by omega)
    omega
  obtain ⟨𝓕, h1, h2, h3⟩ := ap_family (n := n) g (a := n - W + a') he (by omega : 1 ≤ k)
    (by omega) (fun i hi => by rw [add_assoc]; exact hg i hi)
  have hchoose : (n / (2 * W) + (k - 1)).choose (k - 1) ≤ #𝓕 := by
    rw [h3]
    calc (n / (2 * W) + (k - 1)).choose (k - 1)
        ≤ ((n - W + a') / e + (k - 1)).choose (k - 1) := by
          apply Nat.choose_le_choose
          have : n / (2 * W) ≤ (n - W + a') / e :=
            calc n / (2 * W) = n / 2 / W := (Nat.div_div_eq_div_mul n 2 W).symm
              _ ≤ (n - W + a') / W := Nat.div_le_div_right (by omega)
              _ ≤ (n - W + a') / e := Nat.div_le_div_left heW.le (by omega)
          omega
      _ ≤ ∑ i ∈ range k, ((n - W + a') / e + (k - 1)).choose i :=
          single_le_sum (f := fun i => ((n - W + a') / e + (k - 1)).choose i)
            (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega))
  refine ⟨𝓕, h1, h2, hchoose, ?_⟩
  generalize n / (2 * W) = N at hchoose ⊢
  have hq := Nat.pow_le_choose (α := ℚ) (k - 1) (N + (k - 1))
  rw [show N + (k - 1) + 1 - (k - 1) = N + 1 by omega,
    div_le_iff₀ (by exact_mod_cast Nat.factorial_pos _)] at hq
  have hle : (((N + 1) ^ (k - 1) : ℕ) : ℚ) ≤ (((k - 1).factorial * #𝓕 : ℕ) : ℚ) := by
    push_cast
    calc ((N : ℚ) + 1) ^ (k - 1)
        ≤ (N + (k - 1)).choose (k - 1) * (k - 1).factorial := by exact_mod_cast hq
      _ ≤ #𝓕 * (k - 1).factorial := by
          gcongr
      _ = (k - 1).factorial * #𝓕 := mul_comm _ _
  exact_mod_cast hle

end VanDerWaerden

end Erdos1183
