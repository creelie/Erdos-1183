import Erdos1183.Lattice
import Mathlib.Data.Nat.Log

/-!
# Counting sublattices point by point

Removing the largest point `x` from the members of a sublattice gives a sublattice on the
remaining points, and the original sublattice is recovered from it together with two of its
members: the least member containing `x` (with `x` removed) and the greatest member not
containing `x`. Hence there are at most `(m + 1)^{2n}` nonempty sublattices of `2^{[n]}` with at
most `m` members, and a first-moment argument gives `f(n) ≤ (2 + o(1)) n log₂ n`.
-/

open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The greatest member of `𝓛` not containing `x`. -/
def high (𝓛 : Finset (Finset (Fin n))) (x : Fin n) : Finset (Fin n) :=
  (𝓛.filter (x ∉ ·)).sup id

lemma subset_high {𝓛 : Finset (Finset (Fin n))} {S : Finset (Fin n)} (hS : S ∈ 𝓛) {x : Fin n}
    (hx : x ∉ S) : S ⊆ high 𝓛 x :=
  Finset.le_sup (f := id) (mem_filter.2 ⟨hS, hx⟩)

lemma not_mem_high (𝓛 : Finset (Finset (Fin n))) (x : Fin n) : x ∉ high 𝓛 x := by
  intro h
  obtain ⟨S, hS, hxS⟩ := mem_sup.1 h
  exact (mem_filter.1 hS).2 hxS

lemma high_mem {𝓛 : Finset (Finset (Fin n))} (hL : LatticeClosed 𝓛) {S : Finset (Fin n)}
    (hS : S ∈ 𝓛) {x : Fin n} (hx : x ∉ S) : high 𝓛 x ∈ 𝓛 :=
  SupClosed.finsetSup_mem (s := (𝓛 : Set (Finset (Fin n))))
    (fun a ha b hb => (hL a ha b hb).1) ⟨S, mem_filter.2 ⟨hS, hx⟩⟩
    fun _i hi => (mem_filter.1 hi).1

/-- The members of `𝓛` cut down to the points below `k`. -/
noncomputable def restr (k : ℕ) (𝓛 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  𝓛.image (· ∩ seg n k)

/-- Nonempty sublattices with at most `m` members, all inside `{0, …, k-1}`. -/
noncomputable def subl (k m : ℕ) : Finset (Finset (Finset (Fin n))) :=
  univ.filter fun 𝓛 => LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ #𝓛 ≤ m ∧ ∀ S ∈ 𝓛, S ⊆ seg n k

lemma mem_seg {k : ℕ} {y : Fin n} : y ∈ seg n k ↔ y.val < k := by
  simp [seg]

lemma restr_mem_subl {k m : ℕ} {𝓛 : Finset (Finset (Fin n))} (h : 𝓛 ∈ subl (k + 1) m) :
    restr k 𝓛 ∈ subl k m := by
  simp only [subl, mem_filter, mem_univ, true_and] at h ⊢
  obtain ⟨hL, hne, hm, -⟩ := h
  refine ⟨?_, hne.image _, card_image_le.trans hm, fun S hS => ?_⟩
  · intro A hA B hB
    obtain ⟨S, hS, rfl⟩ := mem_image.1 hA
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hB
    refine ⟨mem_image.2 ⟨S ∪ T, (hL S hS T hT).1, ?_⟩, mem_image.2 ⟨S ∩ T, (hL S hS T hT).2, ?_⟩⟩
    · exact union_inter_distrib_right S T _
    · exact inter_inter_distrib_right S T _
  · obtain ⟨T, -, rfl⟩ := mem_image.1 hS
    exact inter_subset_right

section Fibre

variable {k : ℕ} (hk : k < n)

/-- The point `k` of `Fin n`. -/
def pt : Fin n := ⟨k, hk⟩

variable {hk}

lemma inter_seg_of_not_mem {S : Finset (Fin n)} (hS : S ⊆ seg n (k + 1)) (hx : pt hk ∉ S) :
    S ∩ seg n k = S := by
  refine inter_eq_left.2 fun y hy => mem_seg.2 ?_
  have h1 := mem_seg.1 (hS hy)
  have h2 : y ≠ pt hk := fun h => hx (h ▸ hy)
  have h3 : y.val ≠ k := fun h => h2 (Fin.ext h)
  omega

lemma insert_inter_seg {S : Finset (Fin n)} (hS : S ⊆ seg n (k + 1)) (hx : pt hk ∈ S) :
    insert (pt hk) (S ∩ seg n k) = S := by
  ext y
  simp only [mem_insert, mem_inter, mem_seg]
  constructor
  · rintro (rfl | ⟨hy, -⟩)
    · exact hx
    · exact hy
  · intro hy
    by_cases hyx : y = pt hk
    · exact Or.inl hyx
    · right
      refine ⟨hy, ?_⟩
      have h1 := mem_seg.1 (hS hy)
      have h3 : y.val ≠ k := fun h => hyx (Fin.ext h)
      omega

/-- The code of the point `k`: the least member containing it, cut below `k`. -/
noncomputable def loCode (𝓛 : Finset (Finset (Fin n))) : Option (Finset (Fin n)) :=
  if pt hk ∈ ltop 𝓛 then some (low 𝓛 (pt hk) ∩ seg n k) else none

/-- The code of the point `k`: the greatest member not containing it. -/
noncomputable def hiCode (𝓛 : Finset (Finset (Fin n))) : Option (Finset (Fin n)) :=
  if pt hk ∈ lbot 𝓛 then none else some (high 𝓛 (pt hk))

variable (hk) in
/-- Rebuilding a sublattice from its restriction and the two codes. -/
noncomputable def decode (𝓛' : Finset (Finset (Fin n))) (a b : Option (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  a.elim ∅ (fun A => (𝓛'.filter (A ⊆ ·)).image (insert (pt hk))) ∪
    b.elim ∅ (fun B => 𝓛'.filter (· ⊆ B))

lemma decode_eq {m : ℕ} {𝓛 : Finset (Finset (Fin n))} (h : 𝓛 ∈ subl (k + 1) m) :
    decode hk (restr k 𝓛) (loCode (hk := hk) 𝓛) (hiCode (hk := hk) 𝓛) = 𝓛 := by
  simp only [subl, mem_filter, mem_univ, true_and] at h
  obtain ⟨hL, hne, -, hsub⟩ := h
  ext S
  simp only [decode, loCode, hiCode, mem_union]
  set x := pt hk with hxdef
  constructor
  · rintro (hS | hS)
    · -- `S` contains `x`
      by_cases hxT : x ∈ ltop 𝓛
      · simp only [hxT, ↓reduceIte] at hS
        simp only [Option.elim, mem_image, mem_filter] at hS
        obtain ⟨T, ⟨hT, hlowT⟩, rfl⟩ := hS
        obtain ⟨U, hU, rfl⟩ := mem_image.1 hT
        have hlow := low_mem hL hxT
        have hUsub := hsub U hU
        have hlowsub := hsub _ hlow
        have heq : insert x (U ∩ seg n k) = U ∪ low 𝓛 x := by
          ext y
          simp only [mem_insert, mem_inter, mem_union, mem_seg]
          constructor
          · rintro (rfl | ⟨hy, -⟩)
            · exact Or.inr (mem_low _)
            · exact Or.inl hy
          · rintro (hy | hy)
            · by_cases hyx : y = x
              · exact Or.inl hyx
              · have h1 := mem_seg.1 (hUsub hy)
                have h3 : y.val ≠ k := fun h => hyx (Fin.ext h)
                exact Or.inr ⟨hy, by omega⟩
            · by_cases hyx : y = x
              · exact Or.inl hyx
              · have h1 := mem_seg.1 (hlowsub hy)
                have h3 : y.val ≠ k := fun h => hyx (Fin.ext h)
                exact Or.inr ⟨(mem_inter.1 (hlowT (mem_inter.2 ⟨hy, mem_seg.2 (by omega)⟩))).1,
                  by omega⟩
        rw [heq]
        exact (hL U hU _ hlow).1
      · simp only [hxT, ↓reduceIte] at hS
        simp at hS
    · -- `S` avoids `x`
      by_cases hxB : x ∈ lbot 𝓛
      · simp only [hxB, ↓reduceIte] at hS
        simp at hS
      · simp only [hxB, ↓reduceIte] at hS
        simp only [Option.elim, mem_filter] at hS
        obtain ⟨hT, hTsub⟩ := hS
        obtain ⟨U, hU, rfl⟩ := mem_image.1 hT
        obtain ⟨S₀, hS₀, hxS₀⟩ : ∃ S₀ ∈ 𝓛, x ∉ S₀ := ⟨lbot 𝓛, lbot_mem hL hne, hxB⟩
        have hhigh := high_mem hL hS₀ hxS₀
        have hhsub := hsub _ hhigh
        have heq : U ∩ high 𝓛 x = U ∩ seg n k := by
          ext y
          simp only [mem_inter]
          constructor
          · rintro ⟨hy, hyh⟩
            refine ⟨hy, mem_seg.2 ?_⟩
            have h1 := mem_seg.1 (hhsub hyh)
            have hyx : y ≠ x := fun h => not_mem_high 𝓛 x (h ▸ hyh)
            have h3 : y.val ≠ k := fun h => hyx (Fin.ext h)
            omega
          · rintro ⟨hy, hys⟩
            exact ⟨hy, hTsub (mem_inter.2 ⟨hy, hys⟩)⟩
        rw [← heq]
        exact (hL U hU _ hhigh).2
  · intro hS
    by_cases hxS : x ∈ S
    · left
      have hxT : x ∈ ltop 𝓛 := subset_ltop hS hxS
      simp only [hxT, ↓reduceIte]
      simp only [Option.elim, mem_image, mem_filter]
      refine ⟨S ∩ seg n k, ⟨mem_image.2 ⟨S, hS, rfl⟩, ?_⟩, insert_inter_seg (hsub S hS) hxS⟩
      exact inter_subset_inter_right (low_subset hS hxS)
    · right
      have hxB : x ∉ lbot 𝓛 := fun h => hxS (lbot_subset hS h)
      simp only [hxB, ↓reduceIte]
      simp only [Option.elim, mem_filter]
      refine ⟨mem_image.2 ⟨S, hS, inter_seg_of_not_mem (hsub S hS) hxS⟩, subset_high hS hxS⟩

/-- The codes lie in `𝓛'` (or are absent). -/
lemma codes_mem {m : ℕ} {𝓛 : Finset (Finset (Fin n))} (h : 𝓛 ∈ subl (k + 1) m) :
    loCode (hk := hk) 𝓛 ∈ insert none ((restr k 𝓛).image some) ∧
      hiCode (hk := hk) 𝓛 ∈ insert none ((restr k 𝓛).image some) := by
  simp only [subl, mem_filter, mem_univ, true_and] at h
  obtain ⟨hL, hne, -, hsub⟩ := h
  constructor
  · unfold loCode
    split_ifs with hxT
    · exact mem_insert_of_mem (mem_image.2 ⟨_, mem_image.2 ⟨_, low_mem hL hxT, rfl⟩, rfl⟩)
    · exact mem_insert_self _ _
  · unfold hiCode
    split_ifs with hxB
    · exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_image.2 ⟨_, mem_image.2 ⟨high 𝓛 (pt hk), ?_, ?_⟩, rfl⟩)
      · exact high_mem hL (lbot_mem hL hne) hxB
      · exact inter_seg_of_not_mem (hsub _ (high_mem hL (lbot_mem hL hne) hxB))
          (not_mem_high 𝓛 _)

variable (hk) in
include hk in
/-- **Fibres.** At most `(m+1)^2` sublattices restrict to a given one. -/
lemma card_fibre_le (m : ℕ) {𝓛' : Finset (Finset (Fin n))} (h' : 𝓛' ∈ subl k m) :
    #((subl (k + 1) m).filter fun 𝓛 => restr k 𝓛 = 𝓛') ≤ (m + 1) ^ 2 := by
  set t := insert none (𝓛'.image some) with ht
  have hcard : #t ≤ m + 1 := by
    have hm : #𝓛' ≤ m := by
      simp only [subl, mem_filter, mem_univ, true_and] at h'
      exact h'.2.2.1
    calc #t ≤ #(𝓛'.image some) + 1 := card_insert_le _ _
      _ ≤ #𝓛' + 1 := Nat.add_le_add_right card_image_le 1
      _ ≤ m + 1 := Nat.add_le_add_right hm 1
  calc #((subl (k + 1) m).filter fun 𝓛 => restr k 𝓛 = 𝓛')
      ≤ #(t ×ˢ t) := by
        refine card_le_card_of_injOn (fun 𝓛 => (loCode (hk := hk) 𝓛, hiCode (hk := hk) 𝓛)) ?_ ?_
        · intro 𝓛 h𝓛
          have h𝓛' := mem_filter.1 h𝓛
          have hc := codes_mem (hk := hk) h𝓛'.1
          rw [h𝓛'.2] at hc
          exact mem_product.2 hc
        · intro 𝓛₁ h₁ 𝓛₂ h₂ he
          have h₁' := mem_filter.1 h₁
          have h₂' := mem_filter.1 h₂
          simp only [Prod.mk.injEq] at he
          rw [← decode_eq (hk := hk) h₁'.1, ← decode_eq (hk := hk) h₂'.1, h₁'.2, h₂'.2, he.1, he.2]
    _ = #t * #t := card_product _ _
    _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul hcard hcard
    _ = (m + 1) ^ 2 := by ring

end Fibre

lemma card_subl_succ {k : ℕ} (hk : k < n) (m : ℕ) :
    #(subl (n := n) (k + 1) m) ≤ (m + 1) ^ 2 * #(subl (n := n) k m) :=
  card_le_mul_card_image_of_maps_to (fun _ h => restr_mem_subl h) _
    fun _ h' => card_fibre_le hk m h'

lemma card_subl_zero (m : ℕ) : #(subl (n := n) 0 m) ≤ 1 := by
  refine card_le_one.2 fun 𝓛₁ h₁ 𝓛₂ h₂ => ?_
  have key : ∀ 𝓛 ∈ subl (n := n) 0 m, 𝓛 = {∅} := by
    intro 𝓛 h𝓛
    simp only [subl, mem_filter, mem_univ, true_and] at h𝓛
    obtain ⟨-, hne, -, hsub⟩ := h𝓛
    refine (hne.subset_singleton_iff).1 fun S hS => ?_
    have : S = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      have := mem_seg.1 (hsub S hS hy)
      omega
    exact mem_singleton.2 this
  rw [key _ h₁, key _ h₂]

lemma card_subl_le (m : ℕ) : ∀ k ≤ n, #(subl (n := n) k m) ≤ (m + 1) ^ (2 * k)
  | 0, _ => by simpa using card_subl_zero m
  | k + 1, hk => by
    calc #(subl (n := n) (k + 1) m) ≤ (m + 1) ^ 2 * #(subl (n := n) k m) :=
          card_subl_succ (by omega) m
      _ ≤ (m + 1) ^ 2 * (m + 1) ^ (2 * k) :=
          Nat.mul_le_mul_left _ (card_subl_le m k (by omega))
      _ = (m + 1) ^ (2 * (k + 1)) := by rw [← pow_add]; congr 1; ring

/-- **Counting sublattices.** There are at most `(m + 1)^{2n}` nonempty sublattices of `2^{[n]}`
with at most `m` members. -/
theorem card_sublattices_le_pow (m : ℕ) :
    #(univ.filter fun 𝓛 : Finset (Finset (Fin n)) => LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ #𝓛 ≤ m) ≤
      (m + 1) ^ (2 * n) := by
  refine le_trans (card_le_card fun 𝓛 h𝓛 => ?_) (card_subl_le m n le_rfl)
  simp only [subl, mem_filter, mem_univ, true_and] at h𝓛 ⊢
  exact ⟨h𝓛.1, h𝓛.2.1, h𝓛.2.2, fun S _ y _ => mem_seg.2 y.isLt⟩

/-! ### The bound `f(n) ≤ (2 + o(1)) n log₂ n` -/
lemma sum_two_pow_lt : ∀ k, ∑ w ∈ range k, 2 ^ w < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [sum_range_succ, pow_succ]
    have := sum_two_pow_lt k
    omega


/-- The exponent bookkeeping: `E(w) = 2n(w+1) + w + 3`. -/
def expo2 (n w : ℕ) : ℕ := 2 * n * (w + 1) + w + 3

lemma expo2_mono (n : ℕ) {w w' : ℕ} (h : w ≤ w') : expo2 n w ≤ expo2 n w' := by
  unfold expo2
  have := Nat.mul_le_mul_left (2 * n) (Nat.add_le_add_right h 1)
  omega

lemma expo2_le_two_pow (n L K : ℕ) (hKL : K ≤ L) (hn : n + 1 ≤ 2 ^ L) (hK : L + 1 ≤ 2 ^ K) :
    ∀ w, L + K + 3 ≤ w → expo2 n w ≤ 2 ^ w := by
  intro w hw
  induction w, hw using Nat.le_induction with
  | base =>
    have hsplit : 2 ^ (L + K + 3) = 8 * (2 ^ L * 2 ^ K) := by rw [pow_add, pow_add]; ring
    have h1 : (n + 1) * (L + 1) ≤ 2 ^ L * 2 ^ K := Nat.mul_le_mul hn hK
    rw [hsplit, expo2]
    nlinarith
  | succ w hw ih =>
    have : expo2 n (w + 1) ≤ 2 * expo2 n w := by
      unfold expo2
      nlinarith
    rw [pow_succ]
    omega

/-- **`f(n) ≤ (2 + o(1)) n log₂ n`.** With `L = ⌊log₂ n⌋ + 1` and `K = ⌊log₂ L⌋ + 1`,
`f(n) ≤ 2n(L + K + 3) + L + K + 4`. -/
theorem smallF_le_log (n : ℕ) :
    smallF n ≤ 2 * n * (Nat.log 2 n + Nat.log 2 (Nat.log 2 n + 1) + 5) +
      Nat.log 2 n + Nat.log 2 (Nat.log 2 n + 1) + 6 := by
  set L := Nat.log 2 n + 1 with hLdef
  set K := Nat.log 2 L + 1 with hKdef
  have hnL : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) n
  have hLK : L + 1 ≤ 2 ^ K := Nat.lt_pow_succ_log_self (by norm_num) L
  have hKL : K ≤ L := by
    have h1 : Nat.log 2 L < L := Nat.log_lt_self 2 (by omega)
    omega
  set m := expo2 n (L + K + 2) with hm
  have hmval : m = 2 * n * (Nat.log 2 n + Nat.log 2 L + 5) + Nat.log 2 n + Nat.log 2 L + 7 := by
    rw [hm, expo2, hKdef, hLdef]; ring
  -- `E(w) ≤ max(m, 2^w)` for every `w`
  have hE : ∀ w, expo2 n w ≤ m ∨ expo2 n w ≤ 2 ^ w := by
    intro w
    by_cases hw : w ≤ L + K + 2
    · exact Or.inl (expo2_mono n hw)
    · exact Or.inr (expo2_le_two_pow n L K hKL hnL hLK w (by omega))
  set 𝒜 : ℕ → Finset (Finset (Finset (Fin n))) := fun w =>
    univ.filter fun 𝓛 => LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ m ≤ #𝓛 ∧ Nat.log 2 #𝓛 = w with h𝒜
  set X : ℕ → ℕ := fun w =>
    ∑ 𝓛 ∈ 𝒜 w, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) with hX
  -- each layer is small
  have hlayer : ∀ w, X w * 2 ^ (w + 2) ≤ 2 ^ (2 ^ n) := by
    intro w
    have hcount : #(𝒜 w) ≤ 2 ^ (2 * n * (w + 1)) := by
      have hsub : 𝒜 w ⊆ univ.filter fun 𝓛 : Finset (Finset (Fin n)) =>
          LatticeClosed 𝓛 ∧ 𝓛.Nonempty ∧ #𝓛 ≤ 2 ^ (w + 1) - 1 := by
        intro 𝓛 h𝓛
        simp only [h𝒜, mem_filter, mem_univ, true_and] at h𝓛 ⊢
        obtain ⟨hL, hne, -, hw⟩ := h𝓛
        have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) #𝓛
        rw [hw] at this
        exact ⟨hL, hne, by omega⟩
      refine (card_le_card hsub).trans ((card_sublattices_le_pow _).trans (le_of_eq ?_))
      have h1 : 2 ^ (w + 1) - 1 + 1 = 2 ^ (w + 1) := Nat.sub_add_cancel Nat.one_le_two_pow
      rw [h1, ← pow_mul]
      congr 1
      ring
    have hfam : ∀ 𝓛 ∈ 𝒜 w, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) *
        2 ^ expo2 n w ≤ 2 * 2 ^ (2 ^ n) := by
      intro 𝓛 h𝓛
      simp only [h𝒜, mem_filter, mem_univ, true_and] at h𝓛
      obtain ⟨-, hne, hm𝓛, hw⟩ := h𝓛
      have hpow : 2 ^ w ≤ #𝓛 := by
        rw [← hw]
        exact Nat.pow_log_le_self 2 (card_pos.2 hne).ne'
      have hle : expo2 n w ≤ #𝓛 := by
        rcases hE w with h | h
        · omega
        · omega
      exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hle)).trans
        (card_mono_mul_le 𝓛)
    have hsum : X w * 2 ^ expo2 n w ≤ 2 ^ (2 * n * (w + 1)) * (2 * 2 ^ (2 ^ n)) := by
      simp only [hX]
      rw [sum_mul]
      calc ∑ 𝓛 ∈ 𝒜 w, #(univ.filter fun χ : Colouring n => Monochromatic χ 𝓛) * 2 ^ expo2 n w
          ≤ ∑ _𝓛 ∈ 𝒜 w, 2 * 2 ^ (2 ^ n) := sum_le_sum hfam
        _ = #(𝒜 w) * (2 * 2 ^ (2 ^ n)) := by rw [sum_const, smul_eq_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ hcount
    have hsplit : 2 ^ expo2 n w = 2 ^ (2 * n * (w + 1)) * 2 * 2 ^ (w + 2) := by
      rw [expo2, show 2 * n * (w + 1) + w + 3 = 2 * n * (w + 1) + 1 + (w + 2) by ring,
        pow_add, pow_add, pow_one]
    rw [hsplit] at hsum
    have hpos : 0 < 2 ^ (2 * n * (w + 1)) * 2 := by positivity
    have key : (X w * 2 ^ (w + 2)) * (2 ^ (2 * n * (w + 1)) * 2) ≤
        2 ^ (2 ^ n) * (2 ^ (2 * n * (w + 1)) * 2) := by
      calc (X w * 2 ^ (w + 2)) * (2 ^ (2 * n * (w + 1)) * 2)
          = X w * (2 ^ (2 * n * (w + 1)) * 2 * 2 ^ (w + 2)) := by ring
        _ ≤ 2 ^ (2 * n * (w + 1)) * (2 * 2 ^ (2 ^ n)) := hsum
        _ = 2 ^ (2 ^ n) * (2 ^ (2 * n * (w + 1)) * 2) := by ring
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
