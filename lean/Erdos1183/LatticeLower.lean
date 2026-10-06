import Erdos1183.Basic
import Erdos1183.LatticeCerts

/-!
# A lower bound for `f(n)` above `⌈(n+1)/2⌉`

The levels `0, 1, …, n` of the chain `∅ ⊂ {0} ⊂ {0, 1} ⊂ ⋯ ⊂ [n]` are cut into windows of
twelve consecutive levels. Each window is replaced by a copy of the cube `2^{[11]}` sitting
above an initial segment, and in that cube the colouring has a red sublattice and a blue
sublattice with `13` members in total (`splits_window`). There are two cases.

* If the colour of a set in the cube is not a function of its size, two sets `S, T` of the
  same size differing in one point have different colours. A maximal chain from `∅` to
  `S ∩ T`, followed by `S` or by `T`, followed by a maximal chain from `S ∪ T` to the top,
  gives `11` sets shared by both colours and one extra set for each colour.
* If the colour depends only on the size, an explicit sublattice from `LatticeCerts` beats the
  chain in one colour, and the chain supplies the other colour.

Stacking the windows and finishing with the remaining levels of the chain gives a red and a
blue sublattice with `n + 1 + ⌊(n+1)/12⌋` members in total, so
`f(n) ≥ ⌈(n + 1 + ⌊(n+1)/12⌋)/2⌉` (`smallF_ge_window`). In particular `f(n) > ⌈(n+1)/2⌉` for
every odd `n ≥ 11` and every `n ≥ 23`.
-/

open Finset

namespace Erdos1183

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Chains and stacked sublattices -/

/-- Every two members of `𝓒` are comparable. -/
def IsChainF {m : ℕ} (𝓒 : Finset (Finset (Fin m))) : Prop :=
  ∀ A ∈ 𝓒, ∀ B ∈ 𝓒, A ⊆ B ∨ B ⊆ A

lemma IsChainF.latticeClosed {m : ℕ} {𝓒 𝓖 : Finset (Finset (Fin m))} (h : IsChainF 𝓒)
    (hs : 𝓖 ⊆ 𝓒) : LatticeClosed 𝓖 := by
  intro A hA B hB
  rcases h A (hs hA) B (hs hB) with h | h
  · rw [union_eq_right.2 h, inter_eq_left.2 h]
    exact ⟨hB, hA⟩
  · rw [union_eq_left.2 h, inter_eq_right.2 h]
    exact ⟨hA, hB⟩

lemma IsChainF.insert {m : ℕ} {𝓒 : Finset (Finset (Fin m))} {X : Finset (Fin m)}
    (h : IsChainF 𝓒) (hX : ∀ A ∈ 𝓒, A ⊆ X ∨ X ⊆ A) : IsChainF (insert X 𝓒) := by
  intro A hA B hB
  rcases mem_insert.1 hA with hA' | hA' <;> rcases mem_insert.1 hB with hB' | hB'
  · subst hA' hB'
    exact Or.inl subset_rfl
  · subst hA'
    exact (hX B hB').symm
  · subst hB'
    exact hX A hA'
  · exact h A hA' B hB'

lemma IsChainF.union {m : ℕ} {L U : Finset (Finset (Fin m))} (hL : IsChainF L)
    (hU : IsChainF U) (h : ∀ A ∈ L, ∀ B ∈ U, A ⊆ B) : IsChainF (L ∪ U) := by
  intro A hA B hB
  rcases mem_union.1 hA with hA | hA <;> rcases mem_union.1 hB with hB | hB
  · exact hL A hA B hB
  · exact Or.inl (h A hA B hB)
  · exact Or.inr (h B hB A hA)
  · exact hU A hA B hB

lemma isChainF_image_seg (s : Finset ℕ) : IsChainF (s.image (seg n)) := by
  intro A hA B hB
  obtain ⟨i, -, rfl⟩ := mem_image.1 hA
  obtain ⟨j, -, rfl⟩ := mem_image.1 hB
  rcases le_total i j with h | h
  · exact Or.inl (seg_mono h)
  · exact Or.inr (seg_mono h)

/-- Two sublattices, one entirely below the other, together form a sublattice. -/
lemma latticeClosed_union {m : ℕ} {L U : Finset (Finset (Fin m))} (hL : LatticeClosed L)
    (hU : LatticeClosed U) (h : ∀ A ∈ L, ∀ B ∈ U, A ⊆ B) : LatticeClosed (L ∪ U) := by
  intro A hA B hB
  rcases mem_union.1 hA with hA | hA <;> rcases mem_union.1 hB with hB | hB
  · exact ⟨mem_union_left _ (hL A hA B hB).1, mem_union_left _ (hL A hA B hB).2⟩
  · have h' := h A hA B hB
    rw [union_eq_right.2 h', inter_eq_left.2 h']
    exact ⟨mem_union_right _ hB, mem_union_left _ hA⟩
  · have h' := h B hB A hA
    rw [union_eq_left.2 h', inter_eq_right.2 h']
    exact ⟨mem_union_right _ hA, mem_union_left _ hB⟩
  · exact ⟨mem_union_right _ (hU A hA B hB).1, mem_union_right _ (hU A hA B hB).2⟩

lemma disjoint_of_card_lt {m : ℕ} {L U : Finset (Finset (Fin m))}
    (h : ∀ A ∈ L, ∀ B ∈ U, #A < #B) : Disjoint L U :=
  disjoint_left.2 fun A hA hA' => lt_irrefl _ (h A hA A hA')

lemma card_seg {i : ℕ} (h : i ≤ n) : #(seg n i) = i := by
  have : (seg n i).map Fin.valEmbedding = range i := by
    ext x
    simp only [seg, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  calc #(seg n i) = #((seg n i).map Fin.valEmbedding) := (card_map _).symm
    _ = i := by rw [this, card_range]

lemma card_filter_true_add_false {m : ℕ} (χ : Finset (Fin m) → Bool)
    (𝓒 : Finset (Finset (Fin m))) :
    #(𝓒.filter (χ · = true)) + #(𝓒.filter (χ · = false)) = #𝓒 := by
  rw [← card_filter_add_card_filter_not (s := 𝓒) (fun A => χ A = true)]
  congr 2
  exact filter_congr fun A _ => by simp

/-- A red and a blue sublattice of `2^{[m]}` (under `ψ`) with at least `k` members in total. -/
def Splits {m : ℕ} (ψ : Finset (Fin m) → Bool) (k : ℕ) : Prop :=
  ∃ R B : Finset (Finset (Fin m)), LatticeClosed R ∧ LatticeClosed B ∧
    (∀ A ∈ R, ψ A = true) ∧ (∀ A ∈ B, ψ A = false) ∧ k ≤ #R + #B

lemma splits_of_colour {m k : ℕ} {ψ : Finset (Fin m) → Bool} (c : Bool)
    {F G : Finset (Finset (Fin m))} (hF : LatticeClosed F) (hG : LatticeClosed G)
    (hFc : ∀ A ∈ F, ψ A = c) (hGc : ∀ A ∈ G, ψ A = !c) (h : k ≤ #F + #G) : Splits ψ k := by
  cases c
  · exact ⟨G, F, hG, hF, hGc, hFc, by omega⟩
  · exact ⟨F, G, hF, hG, hFc, hGc, h⟩

lemma Splits.of_not {m k : ℕ} {ψ : Finset (Fin m) → Bool} (h : Splits (fun A => !ψ A) k) :
    Splits ψ k := by
  obtain ⟨R, B, hR, hB, hRc, hBc, hk⟩ := h
  refine ⟨B, R, hB, hR, fun A hA => ?_, fun A hA => ?_, by omega⟩
  · simpa using hBc A hA
  · simpa using hRc A hA

/-! ### Windows whose colouring is not a function of the size -/

/-- A maximal chain of subsets of `s`. -/
lemma exists_chain {m : ℕ} (s : Finset (Fin m)) :
    ∃ 𝓒 : Finset (Finset (Fin m)), IsChainF 𝓒 ∧ (∀ A ∈ 𝓒, A ⊆ s) ∧ #𝓒 = #s + 1 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨{∅}, by simp [IsChainF], by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨𝓒, hc, hs, hcard⟩ := ih
    have hn : insert a s ∉ 𝓒 := fun h => ha (hs _ h (mem_insert_self a s))
    refine ⟨insert (insert a s) 𝓒, hc.insert fun A hA => Or.inl ((hs A hA).trans
      (subset_insert a s)), fun A hA => ?_, ?_⟩
    · rcases mem_insert.1 hA with rfl | hA
      · exact subset_rfl
      · exact (hs A hA).trans (subset_insert a s)
    · rw [card_insert_of_notMem hn, card_insert_of_notMem ha, hcard]

/-- A maximal chain of supersets of `D`. -/
lemma exists_chain_above {m : ℕ} (D : Finset (Fin m)) :
    ∃ 𝓒 : Finset (Finset (Fin m)), IsChainF 𝓒 ∧ (∀ A ∈ 𝓒, D ⊆ A) ∧ #𝓒 + #D = m + 1 := by
  obtain ⟨𝓒, hc, hs, hcard⟩ := exists_chain (univ \ D)
  refine ⟨𝓒.image (D ∪ ·), ?_, fun A hA => ?_, ?_⟩
  · intro A hA B hB
    obtain ⟨A', hA', rfl⟩ := mem_image.1 hA
    obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
    rcases hc A' hA' B' hB' with h | h
    · exact Or.inl (union_subset_union subset_rfl h)
    · exact Or.inr (union_subset_union subset_rfl h)
  · obtain ⟨A', -, rfl⟩ := mem_image.1 hA
    exact subset_union_left
  · have hdis : ∀ A ∈ 𝓒, ∀ x ∈ A, x ∉ D := fun A hA x hx => (mem_sdiff.1 (hs A hA hx)).2
    rw [card_image_of_injOn, hcard, card_univ_sdiff, Fintype.card_fin]
    · have := card_le_univ D
      rw [Fintype.card_fin] at this
      omega
    · intro A hA B hB hAB
      have hAB' : D ∪ A = D ∪ B := hAB
      ext x
      constructor
      · intro hx
        have : x ∈ D ∪ B := hAB' ▸ mem_union_right D hx
        exact (mem_union.1 this).resolve_left (hdis A hA x hx)
      · intro hx
        have : x ∈ D ∪ A := hAB' ▸ mem_union_right D hx
        exact (mem_union.1 this).resolve_left (hdis B hB x hx)

/-- If two sets of the same size have different colours, then so do two sets of the same size
that differ in a single point. -/
lemma exists_adjacent {m : ℕ} (ψ : Finset (Fin m) → Bool) :
    ∀ d, ∀ S T : Finset (Fin m), #(S \ T) = d + 1 → #S = #T → ψ S ≠ ψ T →
      ∃ S T : Finset (Fin m), #S = #T ∧ #(S ∩ T) + 1 = #S ∧ ψ S ≠ ψ T := by
  intro d
  induction d with
  | zero =>
    intro S T hd hST hψ
    exact ⟨S, T, hST, by have := card_sdiff_add_card_inter S T; omega, hψ⟩
  | succ d ih =>
    intro S T hd hST hψ
    have h1 := card_sdiff_add_card_inter S T
    have h2 := card_sdiff_add_card_inter T S
    rw [inter_comm] at h2
    obtain ⟨a, ha⟩ : (S \ T).Nonempty := card_pos.1 (by omega)
    obtain ⟨b, hb⟩ : (T \ S).Nonempty := card_pos.1 (by omega)
    rw [mem_sdiff] at ha hb
    have hbU : b ∉ S.erase a := fun h => hb.2 (mem_of_mem_erase h)
    have hSpos : 0 < #S := card_pos.2 ⟨a, ha.1⟩
    have hUcard : #(insert b (S.erase a)) = #S := by
      rw [card_insert_of_notMem hbU, card_erase_of_mem ha.1]
      omega
    by_cases hU : ψ S = ψ (insert b (S.erase a))
    · have hUT : insert b (S.erase a) \ T = (S \ T).erase a := by
        ext x
        simp only [mem_sdiff, mem_insert, mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hxa, hxS⟩, hxT⟩
          · exact absurd hb.1 hxT
          · exact ⟨hxa, hxS, hxT⟩
        · rintro ⟨hxa, hxS, hxT⟩
          exact ⟨Or.inr ⟨hxa, hxS⟩, hxT⟩
      refine ih _ T ?_ (hUcard.trans hST) (by rw [← hU]; exact hψ)
      rw [hUT, card_erase_of_mem (mem_sdiff.2 ha), hd]
      rfl
    · refine ⟨S, insert b (S.erase a), hUcard.symm, ?_, hU⟩
      have hSU : S ∩ insert b (S.erase a) = S.erase a := by
        ext x
        simp only [mem_inter, mem_insert, mem_erase]
        constructor
        · rintro ⟨hxS, rfl | ⟨hxa, -⟩⟩
          · exact absurd hxS hb.2
          · exact ⟨hxa, hxS⟩
        · rintro ⟨hxa, hxS⟩
          exact ⟨hxS, Or.inr ⟨hxa, hxS⟩⟩
      rw [hSU, card_erase_of_mem ha.1]
      omega

/-- Two sets of the same size, differing in one point and coloured differently, give a red and
a blue sublattice with `m + 2` members in total: a maximal chain through `S ∩ T` and `S ∪ T`
is shared, and `S` and `T` are added to one colour each. -/
lemma splits_of_adjacent {m : ℕ} (ψ : Finset (Fin m) → Bool) {S T : Finset (Fin m)}
    (hST : #S = #T) (hC : #(S ∩ T) + 1 = #S) (hS : ψ S = true) (hT : ψ T = false) :
    Splits ψ (m + 2) := by
  have hD : #(S ∪ T) = #S + 1 := by
    have := card_union_add_card_inter S T
    omega
  obtain ⟨L, hLc, hLs, hLcard⟩ := exists_chain (S ∩ T)
  obtain ⟨H, hHc, hHs, hHcard⟩ := exists_chain_above (S ∪ T)
  have hLH : ∀ A ∈ L, ∀ B ∈ H, A ⊆ B := fun A hA B hB =>
    (hLs A hA).trans (inter_subset_union.trans (hHs B hB))
  have hdisj : Disjoint L H := disjoint_left.2 fun A hA hA' => by
    have h1 := card_le_card (hLs A hA)
    have h2 := card_le_card (hHs A hA')
    omega
  have hK : IsChainF (L ∪ H) := hLc.union hHc hLH
  have hKcard : #(L ∪ H) = m := by
    rw [card_union_of_disjoint hdisj]
    omega
  have hmid : ∀ X, S ∩ T ⊆ X → X ⊆ S ∪ T → #X = #S → X ∉ L ∪ H := by
    intro X h1 h2 hX hmem
    rcases mem_union.1 hmem with h | h
    · have := card_le_card (hLs X h)
      omega
    · have := card_le_card (hHs X h)
      omega
  have hins : ∀ X, S ∩ T ⊆ X → X ⊆ S ∪ T → IsChainF (insert X (L ∪ H)) := by
    intro X h1 h2
    refine hK.insert fun A hA => ?_
    rcases mem_union.1 hA with hA | hA
    · exact Or.inl ((hLs A hA).trans h1)
    · exact Or.inr (h2.trans (hHs A hA))
  have hSn := hmid S inter_subset_left subset_union_left rfl
  have hTn := hmid T inter_subset_right subset_union_right hST.symm
  refine ⟨(insert S (L ∪ H)).filter (ψ · = true), (insert T (L ∪ H)).filter (ψ · = false),
    (hins S inter_subset_left subset_union_left).latticeClosed (filter_subset _ _),
    (hins T inter_subset_right subset_union_right).latticeClosed (filter_subset _ _),
    fun A hA => (mem_filter.1 hA).2, fun A hA => (mem_filter.1 hA).2, ?_⟩
  simp only [filter_insert, hS, hT, ↓reduceIte]
  rw [card_insert_of_notMem (fun h => hSn (mem_of_mem_filter _ h)),
    card_insert_of_notMem (fun h => hTn (mem_of_mem_filter _ h))]
  have := card_filter_true_add_false ψ (L ∪ H)
  omega

/-! ### Windows whose colouring is a function of the size -/

/-- The bits `0, …, 10` of `m`, as a subset of `[11]`. -/
def toSet (m : ℕ) : Finset (Fin 11) := univ.filter fun i => m.testBit i.val

lemma toSet_or (a b : ℕ) : toSet (a ||| b) = toSet a ∪ toSet b := by
  ext i
  simp [toSet, Nat.testBit_or]

lemma toSet_and (a b : ℕ) : toSet (a &&& b) = toSet a ∩ toSet b := by
  ext i
  simp [toSet, Nat.testBit_and]

lemma toSet_injOn : Set.InjOn toSet {m | m < 2048} := by
  intro a ha b hb h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · have : (⟨i, hi⟩ : Fin 11) ∈ toSet a ↔ (⟨i, hi⟩ : Fin 11) ∈ toSet b := by rw [h]
    simp only [toSet, mem_filter, mem_univ, true_and] at this
    exact Bool.eq_iff_iff.2 this
  · have h2 : 2048 ≤ 2 ^ i :=
      calc 2048 = 2 ^ 11 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have ha' : a < 2 ^ i := lt_of_lt_of_le ha h2
    have hb' : b < 2 ^ i := lt_of_lt_of_le hb h2
    rw [Nat.testBit_lt_two_pow ha', Nat.testBit_lt_two_pow hb']

lemma card_filter_range_countP (P : ℕ → Bool) (k : ℕ) :
    #((range k).filter fun i => P i = true) = (List.range k).countP P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [range_add_one, filter_insert, List.range_succ, List.countP_append, ← ih]
    by_cases h : P k = true
    · simp only [h, ↓reduceIte]
      rw [card_insert_of_notMem (by simp)]
      simp [h]
    · simp [h]

lemma card_toSet (m : ℕ) : #(toSet m) = pc m := by
  have : (toSet m).map Fin.valEmbedding = (range 11).filter fun i => m.testBit i = true := by
    ext x
    simp only [toSet, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.isLt, ha⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  rw [pc, ← card_filter_range_countP, ← this, card_map]

lemma pc_le (m : ℕ) : pc m ≤ 11 :=
  List.countP_le_length.trans (by simp)

/-- A colouring of `2^{[11]}` that depends only on the size of a set, with `∅` blue. -/
lemma splits_card (ψ : Finset (Fin 11) → Bool) (h0 : ψ ∅ = false)
    (hcard : ∀ S T : Finset (Fin 11), #S = #T → ψ S = ψ T) : Splits ψ 13 := by
  set g : ℕ → Bool := fun v => ψ (seg 11 v) with hg
  have hS11 : ∀ S : Finset (Fin 11), #S ≤ 11 := fun S => by
    simpa using card_le_univ S
  have hψ : ∀ S, ψ S = g #S := fun S => hcard _ _ (card_seg (hS11 S)).symm
  have hg0 : g 0 = false := by
    have : seg 11 0 = ∅ := by simp [seg]
    simp [hg, this, h0]
  have hcov := cover_ok (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (g 8) (g 9) (g 10) (g 11)
  set b : List Bool := [false, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9, g 10, g 11]
    with hb
  have hbg : ∀ v ≤ 11, b.getD v false = g v := by
    intro v hv
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨
          v = 10 ∨ v = 11 := by omega
    all_goals simp [hb, hg0]
  obtain ⟨p, hp, hpb⟩ := List.any_eq_true.1 hcov
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hpb
  obtain ⟨hall, hlt⟩ := hpb
  set c := b.getD (p.2.headD 0) false with hc
  have hok := List.all_eq_true.1 certs_ok p hp
  simp only [certOK, closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at hok
  obtain ⟨⟨hcl, hnd⟩, hms⟩ := hok
  -- the certificate family, of colour `c`
  set F := p.1.toFinset.image toSet with hF
  have hFl : LatticeClosed F := by
    intro A hA B hB
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
    obtain ⟨a', ha', rfl⟩ := mem_image.1 hB
    rw [List.mem_toFinset] at ha ha'
    obtain ⟨h1, h2⟩ := hcl a ha a' ha'
    exact ⟨mem_image.2 ⟨_, List.mem_toFinset.2 h1, toSet_or a a'⟩,
      mem_image.2 ⟨_, List.mem_toFinset.2 h2, toSet_and a a'⟩⟩
  have hFc : ∀ A ∈ F, ψ A = c := by
    intro A hA
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hA
    rw [List.mem_toFinset] at ha
    rw [hψ, card_toSet, ← hbg _ (pc_le a)]
    exact hall _ (hms a ha).2
  have hFcard : #F = p.1.length := by
    rw [hF, card_image_of_injOn, List.toFinset_card_of_nodup hnd]
    intro a ha a' ha' h
    exact toSet_injOn (hms a (List.mem_toFinset.1 ha)).1 (hms a' (List.mem_toFinset.1 ha')).1 h
  -- the levels of the other colour, as a chain
  set G := ((range 12).filter fun v => g v = !c).image (seg 11) with hG
  have hGl : LatticeClosed G := (isChainF_image_seg _).latticeClosed subset_rfl
  have hGc : ∀ A ∈ G, ψ A = !c := by
    intro A hA
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hA
    exact (mem_filter.1 hv).2
  have hGcard : #G = #((range 12).filter fun v => g v = !c) := by
    rw [hG, card_image_of_injOn]
    intro v hv w hw h
    have hv' := mem_range.1 (mem_filter.1 hv).1
    have hw' := mem_range.1 (mem_filter.1 hw).1
    rw [← card_seg (n := 11) (by omega : v ≤ 11), ← card_seg (n := 11) (by omega : w ≤ 11)]
    exact congrArg card h
  have hsplit := card_filter_add_card_filter_not (s := range 12) (fun v => g v = c)
  have hnot : ∀ x y : Bool, ¬x = y ↔ x = !y := by decide
  rw [card_range, filter_congr fun v _ => hnot (g v) c] at hsplit
  have hcount : #((range 12).filter fun v => g v = c) =
      (List.range 12).countP (fun v => b.getD v false == c) := by
    rw [← card_filter_range_countP]
    congr 1
    refine filter_congr fun v hv => ?_
    rw [hbg v (by simpa [Nat.lt_succ_iff] using hv), beq_iff_eq]
  exact splits_of_colour c hFl hGl hFc hGc (by omega)

/-- Every colouring of `2^{[11]}` has a red and a blue sublattice with `13` members in
total. -/
theorem splits_window (ψ : Finset (Fin 11) → Bool) : Splits ψ 13 := by
  by_cases h : ∃ S T : Finset (Fin 11), #S = #T ∧ ψ S ≠ ψ T
  · obtain ⟨S, T, hST, hψ⟩ := h
    have hpos : 0 < #(S \ T) := by
      rw [card_pos, nonempty_iff_ne_empty]
      intro he
      exact hψ (congrArg ψ (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.1 he) hST.ge))
    obtain ⟨S, T, hST, hC, hψ⟩ := exists_adjacent ψ (#(S \ T) - 1) S T (by omega) hST hψ
    cases hS : ψ S <;> cases hT : ψ T
    · exact absurd (hS.trans hT.symm) hψ
    · exact splits_of_adjacent ψ hST.symm (by rw [inter_comm]; omega) hT hS
    · exact splits_of_adjacent ψ hST hC hS hT
    · exact absurd (hS.trans hT.symm) hψ
  · simp only [not_exists, not_and, ne_eq, not_not] at h
    by_cases h0 : ψ ∅ = false
    · exact splits_card ψ h0 h
    · apply Splits.of_not
      apply splits_card
      · simpa using h0
      · intro S T hST
        simp [h S T hST]

/-! ### Placing the windows -/

/-- The coordinate shift `i ↦ a + i` from `[11]` into `[n]`. -/
def shift (a : ℕ) (h : a + 11 ≤ n) : Fin 11 ↪ Fin n :=
  ⟨fun i => ⟨a + i.val, by omega⟩, fun i j hij => by
    simp only [Fin.mk.injEq] at hij
    exact Fin.ext (by omega)⟩

/-- The cube `2^{[11]}` placed above the initial segment `seg n a`. -/
def emb (a : ℕ) (h : a + 11 ≤ n) (T : Finset (Fin 11)) : Finset (Fin n) :=
  seg n a ∪ T.map (shift a h)

@[simp] lemma shift_apply {a : ℕ} (h : a + 11 ≤ n) (i : Fin 11) :
    (shift a h i).val = a + i.val := rfl

lemma emb_union {a : ℕ} (h : a + 11 ≤ n) (T U : Finset (Fin 11)) :
    emb a h (T ∪ U) = emb a h T ∪ emb a h U := by
  ext x
  simp only [emb, map_union, mem_union]
  tauto

lemma emb_inter {a : ℕ} (h : a + 11 ≤ n) (T U : Finset (Fin 11)) :
    emb a h (T ∩ U) = emb a h T ∩ emb a h U := by
  simp only [emb, map_inter]
  rw [union_inter_distrib_left]

lemma emb_injective {a : ℕ} (h : a + 11 ≤ n) : Function.Injective (emb a h) := by
  intro T U hTU
  ext i
  have : shift a h i ∈ emb a h T ↔ shift a h i ∈ emb a h U := by rw [hTU]
  simpa [emb, seg] using this

lemma seg_subset_emb {a : ℕ} (h : a + 11 ≤ n) (T : Finset (Fin 11)) : seg n a ⊆ emb a h T :=
  subset_union_left

lemma emb_subset_seg {a : ℕ} (h : a + 11 ≤ n) (T : Finset (Fin 11)) :
    emb a h T ⊆ seg n (a + 11) := by
  intro x hx
  rcases mem_union.1 hx with hx | hx
  · exact seg_mono (by omega) hx
  · obtain ⟨i, -, rfl⟩ := mem_map.1 hx
    have := i.isLt
    simp only [seg, mem_filter, mem_univ, true_and, shift_apply]
    omega

lemma latticeClosed_image_emb {a : ℕ} (h : a + 11 ≤ n) {R : Finset (Finset (Fin 11))}
    (hR : LatticeClosed R) : LatticeClosed (R.image (emb a h)) := by
  intro A hA B hB
  obtain ⟨A', hA', rfl⟩ := mem_image.1 hA
  obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
  exact ⟨mem_image.2 ⟨_, (hR A' hA' B' hB').1, emb_union h A' B'⟩,
    mem_image.2 ⟨_, (hR A' hA' B' hB').2, emb_inter h A' B'⟩⟩

/-- The first `t` windows: a red and a blue sublattice with `13 t` members in total, all of
them inside `seg n (12 t)` and of size below `12 t`. -/
lemma windows (χ : Colouring n) : ∀ t, 12 * t ≤ n + 1 →
    ∃ R B : Finset (Finset (Fin n)), LatticeClosed R ∧ LatticeClosed B ∧
      (∀ A ∈ R, χ A = true) ∧ (∀ A ∈ B, χ A = false) ∧ 13 * t ≤ #R + #B ∧
      ∀ X ∈ R ∪ B, X ⊆ seg n (12 * t) ∧ #X < 12 * t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨∅, ∅, by simp [LatticeClosed], by simp [LatticeClosed], by simp, by simp, by simp,
      by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨R, B, hR, hB, hRc, hBc, hcard, hX⟩ := ih (by omega)
    have h : 12 * t + 11 ≤ n := by omega
    obtain ⟨R₁, B₁, hR₁, hB₁, hR₁c, hB₁c, h13⟩ :=
      splits_window (fun T => χ (emb (12 * t) h T))
    have hlow : ∀ X ∈ R ∪ B, ∀ T, X ⊆ emb (12 * t) h T ∧ #X < #(emb (12 * t) h T) := by
      intro X hX' T
      obtain ⟨h1, h2⟩ := hX X hX'
      refine ⟨h1.trans (seg_subset_emb h T), ?_⟩
      have := card_le_card (seg_subset_emb h T)
      rw [card_seg (by omega)] at this
      omega
    have hhigh : ∀ T, emb (12 * t) h T ⊆ seg n (12 * (t + 1)) ∧
        #(emb (12 * t) h T) < 12 * (t + 1) := by
      intro T
      have := card_le_card (emb_subset_seg h T)
      rw [card_seg h] at this
      exact ⟨(emb_subset_seg h T).trans (seg_mono (by omega)), by omega⟩
    have hRd : Disjoint R (R₁.image (emb (12 * t) h)) := disjoint_of_card_lt fun X hX Y hY => by
      obtain ⟨T, -, rfl⟩ := mem_image.1 hY
      exact (hlow X (mem_union_left _ hX) T).2
    have hBd : Disjoint B (B₁.image (emb (12 * t) h)) := disjoint_of_card_lt fun X hX Y hY => by
      obtain ⟨T, -, rfl⟩ := mem_image.1 hY
      exact (hlow X (mem_union_right _ hX) T).2
    refine ⟨R ∪ R₁.image (emb (12 * t) h), B ∪ B₁.image (emb (12 * t) h), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine latticeClosed_union hR (latticeClosed_image_emb h hR₁) fun X hX Y hY => ?_
      obtain ⟨T, -, rfl⟩ := mem_image.1 hY
      exact (hlow X (mem_union_left _ hX) T).1
    · refine latticeClosed_union hB (latticeClosed_image_emb h hB₁) fun X hX Y hY => ?_
      obtain ⟨T, -, rfl⟩ := mem_image.1 hY
      exact (hlow X (mem_union_right _ hX) T).1
    · intro A hA
      rcases mem_union.1 hA with hA | hA
      · exact hRc A hA
      · obtain ⟨T, hT, rfl⟩ := mem_image.1 hA
        exact hR₁c T hT
    · intro A hA
      rcases mem_union.1 hA with hA | hA
      · exact hBc A hA
      · obtain ⟨T, hT, rfl⟩ := mem_image.1 hA
        exact hB₁c T hT
    · rw [card_union_of_disjoint hRd, card_union_of_disjoint hBd,
        card_image_of_injective _ (emb_injective h), card_image_of_injective _ (emb_injective h)]
      omega
    · intro X hX'
      rcases mem_union.1 hX' with hX' | hX' <;> rcases mem_union.1 hX' with hX' | hX'
      · obtain ⟨h1, h2⟩ := hX X (mem_union_left _ hX')
        exact ⟨h1.trans (seg_mono (by omega)), by omega⟩
      · obtain ⟨T, -, rfl⟩ := mem_image.1 hX'
        exact hhigh T
      · obtain ⟨h1, h2⟩ := hX X (mem_union_right _ hX')
        exact ⟨h1.trans (seg_mono (by omega)), by omega⟩
      · obtain ⟨T, -, rfl⟩ := mem_image.1 hX'
        exact hhigh T

/-- **The window bound.** Every 2-colouring of the subsets of `[n]` has a monochromatic
sublattice with at least `⌈(n + 1 + ⌊(n+1)/12⌋)/2⌉` members. -/
theorem smallF_ge_window : (n + 2 + (n + 1) / 12) / 2 ≤ smallF n := by
  rw [le_smallF_iff]
  intro χ
  set q := (n + 1) / 12 with hq
  have hq12 : 12 * q ≤ n + 1 := by omega
  obtain ⟨R, B, hR, hB, hRc, hBc, hcard, hX⟩ := windows χ q hq12
  set C := (Icc (12 * q) n).image (seg n) with hC
  have hCc : IsChainF C := isChainF_image_seg _
  have hCcard : #C = n + 1 - 12 * q := by
    rw [hC, card_image_of_injOn, Nat.card_Icc]
    intro i hi j hj hij
    have hi' := (mem_Icc.1 (mem_coe.1 hi)).2
    have hj' := (mem_Icc.1 (mem_coe.1 hj)).2
    rw [← card_seg (n := n) hi', ← card_seg (n := n) hj']
    exact congrArg card hij
  have hXC : ∀ X ∈ R ∪ B, ∀ Y ∈ C, X ⊆ Y ∧ #X < #Y := by
    intro X hX' Y hY
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hY
    rw [mem_Icc] at hi
    obtain ⟨h1, h2⟩ := hX X hX'
    exact ⟨h1.trans (seg_mono hi.1), by rw [card_seg hi.2]; omega⟩
  have hR' : LatticeClosed (R ∪ C.filter (χ · = true)) :=
    latticeClosed_union hR (hCc.latticeClosed (filter_subset _ _)) fun X hX Y hY =>
      (hXC X (mem_union_left _ hX) Y (mem_of_mem_filter _ hY)).1
  have hB' : LatticeClosed (B ∪ C.filter (χ · = false)) :=
    latticeClosed_union hB (hCc.latticeClosed (filter_subset _ _)) fun X hX Y hY =>
      (hXC X (mem_union_right _ hX) Y (mem_of_mem_filter _ hY)).1
  have hRd : Disjoint R (C.filter (χ · = true)) := disjoint_of_card_lt fun X hX Y hY =>
    (hXC X (mem_union_left _ hX) Y (mem_of_mem_filter _ hY)).2
  have hBd : Disjoint B (C.filter (χ · = false)) := disjoint_of_card_lt fun X hX Y hY =>
    (hXC X (mem_union_right _ hX) Y (mem_of_mem_filter _ hY)).2
  have htot : n + 1 + q ≤ #(R ∪ C.filter (χ · = true)) + #(B ∪ C.filter (χ · = false)) := by
    rw [card_union_of_disjoint hRd, card_union_of_disjoint hBd]
    have := card_filter_true_add_false χ C
    omega
  by_cases hbig : (n + 2 + q) / 2 ≤ #(R ∪ C.filter (χ · = true))
  · refine ⟨_, hR', fun A hA A' hA' => ?_, hbig⟩
    have h1 : χ A = true := by
      rcases mem_union.1 hA with h | h
      · exact hRc A h
      · exact (mem_filter.1 h).2
    have h2 : χ A' = true := by
      rcases mem_union.1 hA' with h | h
      · exact hRc A' h
      · exact (mem_filter.1 h).2
    rw [h1, h2]
  · refine ⟨_, hB', fun A hA A' hA' => ?_, by omega⟩
    have h1 : χ A = false := by
      rcases mem_union.1 hA with h | h
      · exact hBc A h
      · exact (mem_filter.1 h).2
    have h2 : χ A' = false := by
      rcases mem_union.1 hA' with h | h
      · exact hBc A' h
      · exact (mem_filter.1 h).2
    rw [h1, h2]

/-- For every odd `n ≥ 11` and every `n ≥ 23`, `f(n)` exceeds the chain bound `⌈(n+1)/2⌉`. -/
theorem half_lt_smallF (h : (11 ≤ n ∧ n % 2 = 1) ∨ 23 ≤ n) : (n + 2) / 2 < smallF n := by
  have := smallF_ge_window (n := n)
  omega

end Erdos1183
