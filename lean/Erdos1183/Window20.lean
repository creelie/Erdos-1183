import Erdos1183.LatticeLower
import Erdos1183.Window20Gadgets

/-!
# The size colourings of `2^{[19]}`

Every colouring of the subsets of `[19]` that depends only on the size of the set has a red and a
blue sublattice with `22` members in total (`splits_card19`), two more than a maximal chain.

The colouring is a word `g 0, g 1, …, g 19`. The kernel walks through the binary tree of prefixes
`tree20` (`tree20_ok`); at each leaf a prefix of the word is fixed, and the leaf names a red and a
blue gadget of `gadgets` (`gadgets_ok`) placed on levels inside the prefix. A gadget is a
sublattice of a cube `2^{[t]}`; placed above the initial segment `seg 19 d` and completed by the
sets `seg 19 v` of its colour outside the levels `d, …, d + t`, it gives a sublattice of that
colour with `gain` more members than there are levels of the colour. The two gains add up to at
least `2`.
-/

open Finset

namespace Erdos1183.W20

set_option linter.unusedSectionVars false

/-! ### The kernel checks -/

set_option maxRecDepth 100000 in
theorem tree20_ok : walk gadgets 20 0 1 tree20 = some [] := by decide +kernel

/-! ### The tree of prefixes covers every word -/

/-- The word `g` begins with the prefix `w` of length `L`. -/
def Extends (g : ℕ → Bool) (w L : ℕ) : Prop := ∀ i < L, g i = w.testBit i

lemma testBit_add_two_pow {w L : ℕ} (hw : w < 2 ^ L) (i : ℕ) (hi : i ≤ L) :
    (w + 2 ^ L).testBit i = (w.testBit i || decide (i = L)) := by
  rw [Nat.add_comm]
  rcases Nat.lt_or_eq_of_le hi with h | rfl
  · rw [Nat.testBit_two_pow_add_gt h]
    simp [Nat.ne_of_lt h]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hw]
    simp

theorem walk_sound (T : GTree) : ∀ f w L l r, walk T f w L l = some r → w < 2 ^ L → L ≤ 20 →
    ∀ g, Extends g w L → ∃ x w' L', w' < 2 ^ L' ∧ L' ≤ 20 ∧ Extends g w' L' ∧
      leafOK T x w' L' = true := by
  intro f
  induction f with
  | zero => intro w L l r h; simp [walk] at h
  | succ f ih =>
    intro w L l r h hw hL g hg
    cases l with
    | nil => simp [walk] at h
    | cons x xs =>
      simp only [walk] at h
      split_ifs at h with hx hL20 hleaf
      · cases h1 : walk T f w (L + 1) xs with
        | none => simp [h1] at h
        | some r' =>
          simp only [h1] at h
          cases hgL : g L
          · refine ih w (L + 1) xs r' h1 ?_ (by omega) g fun i hi => ?_
            · calc w < 2 ^ L := hw
                _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hi | rfl
              · exact hg i hi
              · rw [hgL, Nat.testBit_lt_two_pow hw]
          · refine ih (w + 2 ^ L) (L + 1) r' r h ?_ (by omega) g fun i hi => ?_
            · rw [Nat.pow_succ]
              omega
            · rw [testBit_add_two_pow hw i (by omega)]
              rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hi | rfl
              · simp [hg i hi, Nat.ne_of_lt hi]
              · simp [hgL]
      · exact ⟨x - 1, w, L, hw, hL, hg, hleaf⟩

/-! ### Placing a gadget -/

/-- The bits `0, …, t-1` of `a`, as a subset of `[t]`. -/
def toSetT (t a : ℕ) : Finset (Fin t) := univ.filter fun i => a.testBit i.val

lemma toSetT_or (t a b : ℕ) : toSetT t (a ||| b) = toSetT t a ∪ toSetT t b := by
  ext i
  simp [toSetT, Nat.testBit_or]

lemma toSetT_and (t a b : ℕ) : toSetT t (a &&& b) = toSetT t a ∩ toSetT t b := by
  ext i
  simp [toSetT, Nat.testBit_and]

lemma toSetT_injOn (t : ℕ) : Set.InjOn (toSetT t) {a | a < 2 ^ t} := by
  intro a ha b hb h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < t
  · have : (⟨i, hi⟩ : Fin t) ∈ toSetT t a ↔ (⟨i, hi⟩ : Fin t) ∈ toSetT t b := by rw [h]
    simp only [toSetT, mem_filter, mem_univ, true_and] at this
    exact Bool.eq_iff_iff.2 this
  · have h2 : 2 ^ t ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (show a < 2 ^ t from ha) h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (show b < 2 ^ t from hb) h2)]

lemma card_toSetT {t a : ℕ} (ht : t ≤ 20) (ha : a < 2 ^ t) : #(toSetT t a) = pc20 a := by
  have : (toSetT t a).map Fin.valEmbedding = (range 20).filter fun i => a.testBit i = true := by
    ext x
    simp only [toSetT, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, hi⟩
    · rintro ⟨hx, h⟩
      by_cases hxt : x < t
      · exact ⟨⟨x, hxt⟩, h, rfl⟩
      · have h2 : 2 ^ t ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h2)] at h
        exact absurd h (by simp)
  rw [pc20, ← card_filter_range_countP, ← this, card_map]

lemma pc20_le {t a : ℕ} (ht : t ≤ 20) (ha : a < 2 ^ t) : pc20 a ≤ t := by
  rw [← card_toSetT ht ha]
  simpa using card_le_univ (toSetT t a)

variable {n : ℕ}

/-- The shift `i ↦ d + i` from `[t]` into `[n]`. -/
def shiftT (d t : ℕ) (h : d + t ≤ n) : Fin t ↪ Fin n :=
  ⟨fun i => ⟨d + i.val, by omega⟩, fun i j hij => by
    simp only [Fin.mk.injEq] at hij
    exact Fin.ext (by omega)⟩

@[simp] lemma shiftT_apply {d t : ℕ} (h : d + t ≤ n) (i : Fin t) :
    (shiftT d t h i).val = d + i.val := rfl

/-- The cube `2^{[t]}` placed above the initial segment `seg n d`. -/
def embT (d t : ℕ) (h : d + t ≤ n) (T : Finset (Fin t)) : Finset (Fin n) :=
  seg n d ∪ T.map (shiftT d t h)

lemma embT_union {d t : ℕ} (h : d + t ≤ n) (T U : Finset (Fin t)) :
    embT d t h (T ∪ U) = embT d t h T ∪ embT d t h U := by
  ext x
  simp only [embT, map_union, mem_union]
  tauto

lemma embT_inter {d t : ℕ} (h : d + t ≤ n) (T U : Finset (Fin t)) :
    embT d t h (T ∩ U) = embT d t h T ∩ embT d t h U := by
  simp only [embT, map_inter]
  rw [union_inter_distrib_left]

lemma embT_injective {d t : ℕ} (h : d + t ≤ n) : Function.Injective (embT d t h) := by
  intro T U hTU
  ext i
  have : shiftT d t h i ∈ embT d t h T ↔ shiftT d t h i ∈ embT d t h U := by rw [hTU]
  simpa [embT, seg] using this

lemma seg_subset_embT {d t : ℕ} (h : d + t ≤ n) (T : Finset (Fin t)) :
    seg n d ⊆ embT d t h T :=
  subset_union_left

lemma embT_subset_seg {d t : ℕ} (h : d + t ≤ n) (T : Finset (Fin t)) :
    embT d t h T ⊆ seg n (d + t) := by
  intro x hx
  rcases mem_union.1 hx with hx | hx
  · exact seg_mono (by omega) hx
  · obtain ⟨i, -, rfl⟩ := mem_map.1 hx
    have := i.isLt
    simp only [seg, mem_filter, mem_univ, true_and, shiftT_apply]
    omega

lemma card_embT {d t : ℕ} (h : d + t ≤ n) (T : Finset (Fin t)) :
    #(embT d t h T) = d + #T := by
  rw [embT, card_union_of_disjoint, card_seg (by omega), card_map]
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨i, -, rfl⟩ := mem_map.1 hx'
  simp [seg] at hx

/-- A sublattice together with a chain whose members are comparable with all its members. -/
lemma latticeClosed_union_chain {L C : Finset (Finset (Fin n))} (hL : LatticeClosed L)
    (hC : IsChainF C) (h : ∀ X ∈ C, ∀ Y ∈ L, X ⊆ Y ∨ Y ⊆ X) : LatticeClosed (L ∪ C) := by
  intro A hA B hB
  rcases mem_union.1 hA with hA | hA <;> rcases mem_union.1 hB with hB | hB
  · exact ⟨mem_union_left _ (hL A hA B hB).1, mem_union_left _ (hL A hA B hB).2⟩
  · rcases h B hB A hA with h' | h'
    · rw [union_eq_left.2 h', inter_eq_right.2 h']
      exact ⟨mem_union_left _ hA, mem_union_right _ hB⟩
    · rw [union_eq_right.2 h', inter_eq_left.2 h']
      exact ⟨mem_union_right _ hB, mem_union_left _ hA⟩
  · rcases h A hA B hB with h' | h'
    · rw [union_eq_right.2 h', inter_eq_left.2 h']
      exact ⟨mem_union_left _ hB, mem_union_right _ hA⟩
    · rw [union_eq_left.2 h', inter_eq_right.2 h']
      exact ⟨mem_union_right _ hA, mem_union_left _ hB⟩
  · obtain ⟨h1, h2⟩ := hC.latticeClosed subset_rfl A hA B hB
    exact ⟨mem_union_right _ h1, mem_union_right _ h2⟩

lemma card_image_seg (s : Finset ℕ) (hs : ∀ v ∈ s, v ≤ n) : #(s.image (seg n)) = #s := by
  rw [card_image_of_injOn]
  intro v hv w hw hvw
  rw [← card_seg (n := n) (hs v hv), ← card_seg (n := n) (hs w hw)]
  exact congrArg card hvw

/-- A gadget on the levels `d, …, d + t` whose member sizes all have colour `c`, completed by the
chain of colour `c` outside these levels. -/
lemma exists_placed (g : ℕ → Bool) (ψ : Finset (Fin n) → Bool) (hψ : ∀ S, ψ S = g #S)
    (G : Gadget) (hG : G.ok = true) (d : ℕ) (hd : d + G.t ≤ n) (c : Bool)
    (hc : ∀ a ∈ G.masks, g (d + pc20 a) = c) :
    ∃ F : Finset (Finset (Fin n)), LatticeClosed F ∧ (∀ A ∈ F, ψ A = c) ∧
      G.cnt + #((range (n + 1)).filter fun v => g v = c ∧ (v < d ∨ d + G.t < v)) ≤ #F := by
  simp only [Gadget.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hG
  obtain ⟨⟨⟨⟨ht, hcl⟩, hnd⟩, hcnt⟩, hms⟩ := hG
  simp only [closedB, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hcl
  have hlt : ∀ a ∈ G.masks, a < 2 ^ G.t := fun a ha => (hms a ha).1
  set P : Finset (Finset (Fin n)) :=
    G.masks.toFinset.image fun a => embT d G.t hd (toSetT G.t a) with hP
  set s := (range (n + 1)).filter fun v => g v = c ∧ (v < d ∨ d + G.t < v) with hs
  set C := s.image (seg n) with hC
  have hPl : LatticeClosed P := by
    intro A hA B hB
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hB
    rw [List.mem_toFinset] at ha hb
    obtain ⟨h1, h2⟩ := hcl a ha b hb
    refine ⟨mem_image.2 ⟨_, List.mem_toFinset.2 h1, ?_⟩, mem_image.2 ⟨_, List.mem_toFinset.2 h2, ?_⟩⟩
    · rw [toSetT_or, embT_union]
    · rw [toSetT_and, embT_inter]
  have hPcard : #P = G.cnt := by
    rw [hP, card_image_of_injOn, List.toFinset_card_of_nodup hnd, hcnt]
    intro a ha b hb hab
    exact toSetT_injOn G.t (hlt a (List.mem_toFinset.1 ha)) (hlt b (List.mem_toFinset.1 hb))
      (embT_injective hd hab)
  have hPsize : ∀ Y ∈ P, seg n d ⊆ Y ∧ Y ⊆ seg n (d + G.t) ∧ d ≤ #Y ∧ #Y ≤ d + G.t := by
    intro Y hY
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hY
    have ha' := List.mem_toFinset.1 ha
    refine ⟨seg_subset_embT hd _, embT_subset_seg hd _, ?_, ?_⟩
    · rw [card_embT]
      omega
    · rw [card_embT, card_toSetT (by omega) (hlt a ha')]
      have := pc20_le (by omega : G.t ≤ 20) (hlt a ha')
      omega
  have hCs : ∀ X ∈ C, ∃ v ∈ s, X = seg n v := fun X hX => by
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hX
    exact ⟨v, hv, rfl⟩
  have hsv : ∀ v ∈ s, v ≤ n ∧ g v = c ∧ (v < d ∨ d + G.t < v) := fun v hv => by
    simp only [hs, mem_filter, mem_range] at hv
    exact ⟨by omega, hv.2⟩
  refine ⟨P ∪ C, latticeClosed_union_chain hPl (isChainF_image_seg s) ?_, ?_, ?_⟩
  · intro X hX Y hY
    obtain ⟨v, hv, rfl⟩ := hCs X hX
    obtain ⟨-, -, hvd⟩ := hsv v hv
    obtain ⟨h1, h2, -, -⟩ := hPsize Y hY
    rcases hvd with hvd | hvd
    · exact Or.inl ((seg_mono hvd.le).trans h1)
    · exact Or.inr (h2.trans (seg_mono hvd.le))
  · intro A hA
    rcases mem_union.1 hA with hA | hA
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
      have ha' := List.mem_toFinset.1 ha
      rw [hψ, card_embT, card_toSetT (by omega) (hlt a ha')]
      exact hc a ha'
    · obtain ⟨v, hv, rfl⟩ := hCs A hA
      obtain ⟨hvn, hgv, -⟩ := hsv v hv
      rw [hψ, card_seg hvn, hgv]
  · have hdisj : Disjoint P C := disjoint_left.2 fun Y hY hY' => by
      obtain ⟨v, hv, rfl⟩ := hCs Y hY'
      obtain ⟨hvn, -, hvd⟩ := hsv v hv
      obtain ⟨-, -, h3, h4⟩ := hPsize _ hY
      rw [card_seg hvn] at h3 h4
      omega
    rw [card_union_of_disjoint hdisj, hPcard, hC, card_image_seg s fun v hv => (hsv v hv).1]

/-! ### Reading the gains off the prefix -/

lemma testBit_cmask {g : ℕ → Bool} {w L : ℕ} (hg : Extends g w L) (c : Bool) {v : ℕ}
    (hv : v < L) : (cmask w L c).testBit v = decide (g v = c) := by
  cases c <;> simp [cmask, Nat.testBit_xor, hv, hg v hv]

/-- The number of levels of colour `c` among `d, …, d + t` inside the prefix. -/
lemma pc20_window {g : ℕ → Bool} {w L : ℕ} (hg : Extends g w L) (hL : L ≤ 20) (c : Bool)
    {d t : ℕ} (hdt : d + t + 1 ≤ L) :
    pc20 ((cmask w L c >>> d) &&& (2 ^ (t + 1) - 1)) =
      #((range 20).filter fun v => g v = c ∧ d ≤ v ∧ v ≤ d + t) := by
  rw [pc20, ← card_filter_range_countP]
  have hbit : ∀ i, ((cmask w L c >>> d) &&& (2 ^ (t + 1) - 1)).testBit i =
      decide (i ≤ t ∧ g (d + i) = c) := by
    intro i
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    by_cases hi : i ≤ t
    · rw [testBit_cmask hg c (by omega)]
      simp [hi, Nat.lt_succ_iff]
    · simp [hi, Nat.lt_succ_iff]
  refine card_bij (fun i _ => d + i) ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_range, hbit, decide_eq_true_eq] at hi ⊢
    exact ⟨by omega, hi.2.2, by omega, by omega⟩
  · intro i _ j _ h
    omega
  · intro v hv
    simp only [mem_filter, mem_range] at hv
    refine ⟨v - d, ?_, by omega⟩
    simp only [mem_filter, mem_range, hbit, decide_eq_true_eq]
    refine ⟨by omega, by omega, ?_⟩
    rw [show d + (v - d) = v by omega]
    exact hv.2.1

/-- For each colour, a sublattice beating the chain of that colour by the gain of the gadget named
at the leaf. -/
lemma exists_gain (g : ℕ → Bool) (ψ : Finset (Fin 19) → Bool) (hψ : ∀ S, ψ S = g #S)
    {w L : ℕ} (hg : Extends g w L) (hL : L ≤ 20) (j d : ℕ) (c : Bool) :
    ∃ F : Finset (Finset (Fin 19)), LatticeClosed F ∧ (∀ A ∈ F, ψ A = c) ∧
      #((range 20).filter fun v => g v = c) + resGain gadgets j d w L c ≤ #F := by
  -- the chain of colour `c`
  have hchain : ∃ F : Finset (Finset (Fin 19)), LatticeClosed F ∧ (∀ A ∈ F, ψ A = c) ∧
      #((range 20).filter fun v => g v = c) ≤ #F := by
    refine ⟨((range 20).filter fun v => g v = c).image (seg 19),
      (isChainF_image_seg _).latticeClosed subset_rfl, fun A hA => ?_, ?_⟩
    · obtain ⟨v, hv, rfl⟩ := mem_image.1 hA
      simp only [mem_filter, mem_range] at hv
      rw [hψ, card_seg (by omega), hv.2]
    · rw [card_image_seg]
      intro v hv
      simp only [mem_filter, mem_range] at hv
      omega
  by_cases h0 : resGain gadgets j d w L c = 0
  · rw [h0, Nat.add_zero]
    exact hchain
  obtain ⟨hj, G, hget, hgain⟩ : j ≠ 0 ∧ ∃ G, gadgets.get j = some G ∧
      gain G d w L c = resGain gadgets j d w L c := by
    unfold resGain at h0 ⊢
    split_ifs at h0 ⊢ with hj
    · exact absurd rfl h0
    · cases hget : gadgets.get j with
      | none => simp [hget] at h0
      | some G => exact ⟨hj, G, rfl, by simp⟩
  have hok : G.ok = true := by
    have key : ∀ (T : GTree) (i : ℕ) (G : Gadget), T.allOk = true → T.get i = some G →
        G.ok = true := by
      intro T
      induction T with
      | nil => intro i G _ h; simp [GTree.get] at h
      | leaf G' => intro i G hT h; simp only [GTree.get, Option.some.injEq] at h; subst h; exact hT
      | node l r ihl ihr =>
        intro i G hT h
        simp only [GTree.allOk, Bool.and_eq_true] at hT
        simp only [GTree.get] at h
        split_ifs at h
        · exact ihl _ _ hT.1 h
        · exact ihr _ _ hT.2 h
    exact key gadgets j G gadgets_ok hget
  rw [← hgain] at h0 ⊢
  unfold gain at h0 ⊢
  split_ifs at h0 ⊢ with hfit
  · obtain ⟨hdt, hlev⟩ := hfit
    have hGt : G.t ≤ 19 := by
      simp only [Gadget.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.1.1.1.1
    have hms : ∀ a ∈ G.masks, a < 2 ^ G.t ∧ G.lm.testBit (pc20 a) = true := by
      simp only [Gadget.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
      exact hok.2
    have hc : ∀ a ∈ G.masks, g (d + pc20 a) = c := by
      intro a ha
      have hp := pc20_le (by omega : G.t ≤ 20) (hms a ha).1
      have hb : ((G.lm <<< d) &&& cmask w L c).testBit (d + pc20 a) = true := by
        rw [hlev, Nat.testBit_shiftLeft]
        simp [(hms a ha).2]
      rw [Nat.testBit_and, testBit_cmask hg c (by omega)] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hb.2
    obtain ⟨F, hF, hFc, hFcard⟩ := exists_placed g ψ hψ G hok d (by omega) c hc
    refine ⟨F, hF, hFc, ?_⟩
    rw [pc20_window hg hL c hdt] at h0 ⊢
    have hsplit := card_filter_add_card_filter_not (s := (range 20).filter fun v => g v = c)
      (fun v => d ≤ v ∧ v ≤ d + G.t)
    rw [filter_filter, filter_filter] at hsplit
    have e1 : ((range 20).filter fun v => g v = c ∧ ¬(d ≤ v ∧ v ≤ d + G.t)) =
        (range (19 + 1)).filter fun v => g v = c ∧ (v < d ∨ d + G.t < v) := by
      refine filter_congr fun v _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
    rw [e1] at hsplit
    omega
  · exact absurd rfl h0

/-! ### The size colourings of `2^{[19]}` -/

lemma splits_card19_of_false (ψ : Finset (Fin 19) → Bool) (h0 : ψ ∅ = false)
    (hcard : ∀ S T : Finset (Fin 19), #S = #T → ψ S = ψ T) : Splits ψ 22 := by
  set g : ℕ → Bool := fun v => ψ (seg 19 v) with hgdef
  have hS : ∀ S : Finset (Fin 19), #S ≤ 19 := fun S => by simpa using card_le_univ S
  have hψ : ∀ S, ψ S = g #S := fun S => hcard _ _ (card_seg (hS S)).symm
  have hg0 : Extends g 0 1 := by
    intro i hi
    have : i = 0 := by omega
    subst this
    have : seg 19 0 = ∅ := by simp [seg]
    simp [hgdef, this, h0]
  obtain ⟨x, w, L, -, hL, hg, hleaf⟩ :=
    walk_sound gadgets 20 0 1 tree20 [] tree20_ok (by norm_num) (by norm_num) g hg0
  simp only [leafOK, decide_eq_true_eq] at hleaf
  obtain ⟨R, hR, hRc, hRcard⟩ := exists_gain g ψ hψ hg hL (x % 1024) ((x >>> 10) % 32) true
  obtain ⟨B, hB, hBc, hBcard⟩ := exists_gain g ψ hψ hg hL ((x >>> 15) % 1024)
    ((x >>> 25) % 32) false
  have htot := card_filter_add_card_filter_not (s := range 20) (fun v => g v = true)
  have e2 : ((range 20).filter fun v => ¬g v = true) = (range 20).filter fun v => g v = false :=
    filter_congr fun v _ => by simp
  rw [card_range, e2] at htot
  exact ⟨R, B, hR, hB, hRc, hBc, by omega⟩

/-- **Size colourings of `2^{[19]}`.** Every colouring of the subsets of `[19]` that depends only
on the size of the set has a red and a blue sublattice with `22` members in total. -/
theorem splits_card19 (ψ : Finset (Fin 19) → Bool)
    (hcard : ∀ S T : Finset (Fin 19), #S = #T → ψ S = ψ T) : Splits ψ 22 := by
  by_cases h0 : ψ ∅ = false
  · exact splits_card19_of_false ψ h0 hcard
  · apply Splits.of_not
    apply splits_card19_of_false
    · simpa using h0
    · intro S T hST
      simp [hcard S T hST]

end Erdos1183.W20
