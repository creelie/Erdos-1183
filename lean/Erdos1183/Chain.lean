import Erdos1183.Cube
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Sort

/-!
# Block chains

Fix sizes `b : Fin m → Fin M` (block `k` has `b k + 1` elements). The blocks sit in a grid
`Fin m × Fin M` inside `Fin n`: block `k` is `{(k, c) : c ≤ b k}`. For a level `j` and a set
`A` of earlier block indices, `chainLab b j A` is the hole-cube labelling whose top is the union
of blocks `0, …, j` and whose generators are the blocks in `A`.
-/

open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

section Chain

variable {n m M : ℕ}

/-- The grid `Fin m × Fin M` placed in the first `m M` positions of `Fin n`. -/
def grid (h : m * M ≤ n) : Fin m × Fin M ↪ Fin n :=
  (finProdFinEquiv (m := m) (n := M)).toEmbedding.trans (Fin.castLEEmb h)

/-- The block-chain labelling on the grid. -/
def gridLab (b : Fin m → Fin M) (j : Fin m) (A : Finset (Fin m)) (q : Fin m × Fin M) :
    Fin m ⊕ Bool :=
  if q.2 ≤ b q.1 ∧ q.1 ≤ j then (if q.1 ∈ A then Sum.inl q.1 else Sum.inr true)
  else Sum.inr false

/-- The block-chain labelling on `Fin n`. -/
noncomputable def chainLab (h : m * M ≤ n) (b : Fin m → Fin M) (j : Fin m)
    (A : Finset (Fin m)) (p : Fin n) : Fin m ⊕ Bool :=
  if hp : ∃ q, grid h q = p then gridLab b j A hp.choose else Sum.inr false

variable (h : m * M ≤ n) (b : Fin m → Fin M) (j : Fin m) (A : Finset (Fin m))

lemma chainLab_grid (q : Fin m × Fin M) : chainLab h b j A (grid h q) = gridLab b j A q := by
  have hp : ∃ q', grid h q' = grid h q := ⟨q, rfl⟩
  simp only [chainLab, hp, dite_true]
  rw [(grid h).injective hp.choose_spec]

lemma chainLab_of_not (p : Fin n) (hp : ¬ ∃ q, grid h q = p) :
    chainLab h b j A p = Sum.inr false := by
  simp [chainLab, hp]

lemma card_chainLab (ℓ : Fin m ⊕ Bool) (hℓ : ℓ ≠ Sum.inr false) :
    #(univ.filter fun p => chainLab h b j A p = ℓ) =
      #(univ.filter fun q => gridLab b j A q = ℓ) := by
  rw [← card_map (grid h)]
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_map]
  constructor
  · intro hp
    by_cases hq : ∃ q, grid h q = p
    · obtain ⟨q, rfl⟩ := hq
      exact ⟨q, by rwa [chainLab_grid] at hp, rfl⟩
    · rw [chainLab_of_not h b j A p hq] at hp
      exact absurd hp.symm hℓ
  · rintro ⟨q, hq, rfl⟩
    rwa [chainLab_grid]

omit h in
lemma gridLab_eq_inl (q : Fin m × Fin M) (k : Fin m) :
    gridLab b j A q = Sum.inl k ↔ q.2 ≤ b q.1 ∧ q.1 ≤ j ∧ q.1 ∈ A ∧ q.1 = k := by
  unfold gridLab
  split_ifs with h1 h2 <;> simp_all

omit h in
lemma gridLab_eq_true (q : Fin m × Fin M) :
    gridLab b j A q = Sum.inr true ↔ q.2 ≤ b q.1 ∧ q.1 ≤ j ∧ q.1 ∉ A := by
  unfold gridLab
  split_ifs with h1 h2 <;> simp_all

omit h in
lemma card_fin_le (a : Fin M) : #(univ.filter fun c : Fin M => c ≤ a) = a.val + 1 := by
  rw [← Fin.card_Iic a]
  congr 1
  ext c
  simp

omit h in
lemma card_grid_col (k : Fin m) (a : Fin M) :
    #(univ.filter fun q : Fin m × Fin M => q.1 = k ∧ q.2 ≤ a) = a.val + 1 := by
  have hs : (univ.filter fun q : Fin m × Fin M => q.1 = k ∧ q.2 ≤ a) =
      (univ.filter fun c : Fin M => c ≤ a).map
        ⟨fun c => (k, c), fun c c' hc => by simpa using hc⟩ := by
    ext q
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨rfl, hq⟩
      exact ⟨q.2, hq, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨rfl, hc⟩
  rw [hs, card_map, card_fin_le]

omit h in
lemma card_gridLab_inl (k : Fin m) :
    #(univ.filter fun q => gridLab b j A q = Sum.inl k) =
      if k ∈ A ∧ k ≤ j then (b k).val + 1 else 0 := by
  simp_rw [gridLab_eq_inl]
  by_cases hk : k ∈ A ∧ k ≤ j
  · rw [ite_eq_left hk, ← card_grid_col k (b k)]
    congr 1
    ext q
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, -, -, rfl⟩
      exact ⟨rfl, h1⟩
    · rintro ⟨rfl, hq⟩
      exact ⟨hq, hk.2, hk.1, rfl⟩
  · rw [ite_eq_right hk, card_eq_zero]
    ext q
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨-, h2, h3, rfl⟩
    exact hk ⟨h3, h2⟩

omit h in
lemma card_gridLab_true :
    #(univ.filter fun q => gridLab b j A q = Sum.inr true) =
      ∑ k ∈ univ.filter (fun k => k ≤ j ∧ k ∉ A), ((b k).val + 1) := by
  have hset : (univ.filter fun q => gridLab b j A q = Sum.inr true) =
      (univ.filter (fun k => k ≤ j ∧ k ∉ A)).biUnion
        (fun k => univ.filter fun q : Fin m × Fin M => q.1 = k ∧ q.2 ≤ b k) := by
    ext q
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, gridLab_eq_true]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨q.1, ⟨h2, h3⟩, rfl, h1⟩
    · rintro ⟨k, ⟨hkj, hkA⟩, rfl, hq⟩
      exact ⟨hq, hkj, hkA⟩
  rw [hset, card_biUnion]
  · exact sum_congr rfl fun k _ => card_grid_col k (b k)
  · intro k _ k' _ hkk'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro q hq hq'
    simp only [mem_filter] at hq hq'
    exact hkk' (hq.2.1.symm.trans hq'.2.1)

/-- If the class sizes of the block-chain labelling match those of a pattern (generators
matched along `ι`), the two cubes are monochromatic for equally many orderings. -/
lemma Ncount_chainLab_eq {t r : ℕ} (χ : Colouring n) (π : Fin M → Bool ⊕ Fin t)
    (ι : Fin t ↪ Fin m) (hι : ∀ k, k ∈ A ↔ ∃ i, ι i = k) (hAj : ∀ a ∈ A, a ≤ j)
    (hM : M ≤ n) (hMr : M + r ≤ n)
    (hb : ∀ i, (b (ι i)).val + 1 = #(univ.filter fun q => π q = Sum.inr i))
    (hsum : ∑ k ∈ univ.filter (fun k => k ≤ j ∧ k ∉ A), ((b k).val + 1) =
      r + #(univ.filter fun q => π q = Sum.inl false)) :
    Ncount χ (chainLab h b j A) = Ncount χ (patLab (n := n) M r π) := by
  rw [← Ncount_relabel χ ι (patLab (n := n) M r π)]
  apply Ncount_eq_of_card_fiber_eq
  apply card_fiber_eq_of_ne _ _ (Sum.inr false)
  intro ℓ hℓ
  rw [card_chainLab h b j A ℓ hℓ]
  rcases ℓ with k | c
  · rw [card_gridLab_inl]
    by_cases hk : k ∈ A
    · obtain ⟨i, rfl⟩ := (hι k).1 hk
      rw [ite_eq_left ⟨hk, hAj _ hk⟩, hb i, ← card_patLab_inl hM r π i]
      congr 1
      ext p
      simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
      rcases patLab (n := n) M r π p with i' | c <;> simp [ι.injective.eq_iff]
    · rw [ite_eq_right (fun h => hk h.1), card_eq_zero]
      ext p
      simp only [mem_filter, mem_univ, true_and, Function.comp_apply, Finset.notMem_empty,
        iff_false]
      rcases patLab (n := n) M r π p with i' | c
      · simp only [Sum.map_inl, Sum.inl.injEq]
        rintro rfl
        exact hk ((hι _).2 ⟨i', rfl⟩)
      · simp
  · cases c
    · exact absurd rfl hℓ
    · rw [card_gridLab_true, hsum, ← card_patLab_true hMr π]
      congr 1
      ext p
      simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
      rcases patLab (n := n) M r π p with i' | c <;> simp

end Chain

section Slice

variable {n m M t : ℕ} (h : m * M ≤ n) (χ : Colouring n)

/-- Block sizes for which the cube of level `j` with generators `A` is monochromatic for at
least a `1/K` fraction of the orderings. -/
noncomputable def goodSizes (K : ℕ) (j : Fin m) (A : Finset (Fin m)) : Finset (Fin m → Fin M) :=
  univ.filter fun b => Fintype.card (Equiv.Perm (Fin n)) ≤ K * Ncount χ (chainLab h b j A)

omit h χ in
lemma card_piFinset_slice (s : Finset (Fin m)) (z : Fin M) :
    #(Fintype.piFinset fun k : Fin m => if k ∈ s then ({z} : Finset (Fin M)) else univ) =
      M ^ (m - #s) := by
  rw [Fintype.card_piFinset]
  have hk : ∀ k, #(if k ∈ s then ({z} : Finset (Fin M)) else univ) =
      if k ∈ sᶜ then M else 1 := by
    intro k
    by_cases hk : k ∈ s <;> simp [hk]
  simp_rw [hk]
  rw [prod_ite_mem, univ_inter, prod_const, card_compl, Fintype.card_fin]

/-- **Slice counting.** Suppose that for every `r` some proper pattern of the window `Fin M`
is monochromatic for at least a `1/D` fraction of the orderings. For a level `j` and a set `A`
of `t ≥ 1` earlier generators, at least `M^{m-t-1}` block-size vectors are then good: one for
every choice of the sizes of the blocks outside `A ∪ {j}`. -/
lemma card_goodSizes (D : ℕ) (hmn : m * M < n) (ht : 1 ≤ t)
    (hgood : ∀ r, ∃ π : Fin M → Bool ⊕ Fin t, (∀ i, ∃ q, π q = Sum.inr i) ∧
      Fintype.card (Equiv.Perm (Fin n)) ≤ D * Ncount χ (patLab (n := n) M r π))
    (j : Fin m) (A : Finset (Fin m)) (hA : #A = t) (hAj : ∀ a ∈ A, a < j) :
    M ^ (m - (t + 1)) ≤ #(goodSizes h χ (D) j A) := by
  have hm : 1 ≤ m := j.pos
  have hM0 : 0 < M := by
    obtain ⟨π, hπ, -⟩ := hgood 0
    obtain ⟨q, -⟩ := hπ ⟨0, ht⟩
    exact q.pos
  have hMn : M ≤ n := le_trans (Nat.le_mul_of_pos_left M hm) h
  set z : Fin M := ⟨0, hM0⟩
  have hjA : j ∉ A := fun hj => lt_irrefl j (hAj j hj)
  -- the generators, indexed by `Fin t`
  set ι : Fin t ↪ Fin m := (A.orderEmbOfFin hA).toEmbedding
  have hι : ∀ k, k ∈ A ↔ ∃ i, ι i = k := by
    intro k
    have hr := A.range_orderEmbOfFin hA
    constructor
    · intro hk
      have hk' : k ∈ Set.range (A.orderEmbOfFin hA) := by rw [hr]; exact hk
      obtain ⟨i, hi⟩ := hk'
      exact ⟨i, hi⟩
    · rintro ⟨i, rfl⟩
      exact A.orderEmbOfFin_mem hA i
  -- the pattern chosen for given sizes below `j`
  let R : (Fin m → Fin M) → ℕ := fun b₀ =>
    ∑ k ∈ univ.filter (fun k => k < j ∧ k ∉ A), ((b₀ k).val + 1)
  let π : (Fin m → Fin M) → Fin M → Bool ⊕ Fin t := fun b₀ => (hgood (R b₀ + 1)).choose
  have hπ : ∀ b₀, (∀ i, ∃ q, π b₀ q = Sum.inr i) ∧ Fintype.card (Equiv.Perm (Fin n)) ≤
      D * Ncount χ (patLab (n := n) M (R b₀ + 1) (π b₀)) :=
    fun b₀ => (hgood (R b₀ + 1)).choose_spec
  let idx : ∀ k, k ∈ A → Fin t := fun k hk => ((hι k).1 hk).choose
  have hidx : ∀ k hk, ι (idx k hk) = k := fun k hk => ((hι k).1 hk).choose_spec
  have hcard_inr : ∀ b₀ i, 1 ≤ #(univ.filter fun q => π b₀ q = Sum.inr i) ∧
      #(univ.filter fun q => π b₀ q = Sum.inr i) ≤ M := by
    intro b₀ i
    obtain ⟨q, hq⟩ := (hπ b₀).1 i
    refine ⟨card_pos.2 ⟨q, by simp [hq]⟩, ?_⟩
    exact (card_le_univ _).trans (by simp)
  have hcard_false : ∀ b₀, #(univ.filter fun q => π b₀ q = Sum.inl false) < M := by
    intro b₀
    obtain ⟨q, hq⟩ := (hπ b₀).1 ⟨0, ht⟩
    calc #(univ.filter fun q => π b₀ q = Sum.inl false) ≤ #(univ.erase q) := by
          apply card_le_card
          intro q' hq'
          simp only [mem_filter, mem_univ, true_and] at hq'
          refine mem_erase.2 ⟨?_, mem_univ _⟩
          rintro rfl
          rw [hq] at hq'
          exact Sum.inr_ne_inl hq'
      _ < M := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  -- the patched block sizes
  let G : (Fin m → Fin M) → Fin m → Fin M := fun b₀ k =>
    if k = j then ⟨#(univ.filter fun q => π b₀ q = Sum.inl false), hcard_false b₀⟩
    else if hk : k ∈ A then
      ⟨#(univ.filter fun q => π b₀ q = Sum.inr (idx k hk)) - 1, by
        have := hcard_inr b₀ (idx k hk); omega⟩
    else b₀ k
  have hGout : ∀ b₀ k, k ≠ j → k ∉ A → G b₀ k = b₀ k := by
    intro b₀ k hkj hkA
    simp only [G, hkj, hkA, ite_false, dite_false]
  have hR : ∀ b₀, R b₀ + M ≤ m * M := by
    intro b₀
    have h1 : R b₀ ≤ #(univ.filter (fun k : Fin m => k < j ∧ k ∉ A)) * M := by
      rw [← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun k _ => (b₀ k).isLt
    have h2 : #(univ.filter (fun k : Fin m => k < j ∧ k ∉ A)) ≤ m - 1 := by
      calc #(univ.filter (fun k : Fin m => k < j ∧ k ∉ A)) ≤ #(univ.erase j) := by
            apply card_le_card
            intro k hk
            simp only [mem_filter, mem_univ, true_and] at hk
            exact mem_erase.2 ⟨ne_of_lt hk.1, mem_univ _⟩
        _ = m - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have h3 : (m - 1) * M + M = m * M := by rw [← add_one_mul, Nat.sub_add_cancel hm]
    have h4 : #(univ.filter (fun k : Fin m => k < j ∧ k ∉ A)) * M ≤ (m - 1) * M :=
      Nat.mul_le_mul_right _ h2
    omega
  have hG : ∀ b₀, G b₀ ∈ goodSizes h χ (D) j A := by
    intro b₀
    simp only [goodSizes, mem_filter, mem_univ, true_and]
    rw [Ncount_chainLab_eq h (G b₀) j A χ (π b₀) ι hι (fun a ha => (hAj a ha).le)
      hMn (r := R b₀ + 1) ?_ ?_ ?_]
    · exact (hπ b₀).2
    · have := hR b₀
      omega
    · intro i
      have hiA : ι i ∈ A := (hι _).2 ⟨i, rfl⟩
      have hij : ι i ≠ j := fun h' => hjA (h' ▸ hiA)
      have hidx' : idx (ι i) hiA = i := ι.injective (hidx _ hiA)
      simp only [G, hij, ite_false, hiA, dite_true, hidx']
      have := hcard_inr b₀ i
      omega
    · have hset : univ.filter (fun k : Fin m => k ≤ j ∧ k ∉ A) =
          insert j (univ.filter (fun k : Fin m => k < j ∧ k ∉ A)) := by
        ext k
        simp only [mem_filter, mem_univ, true_and, mem_insert]
        constructor
        · rintro ⟨hk1, hk2⟩
          rcases lt_or_eq_of_le hk1 with hk | hk
          · exact Or.inr ⟨hk, hk2⟩
          · exact Or.inl hk
        · rintro (rfl | ⟨hk1, hk2⟩)
          · exact ⟨le_rfl, hjA⟩
          · exact ⟨hk1.le, hk2⟩
      have hj' : j ∉ univ.filter (fun k : Fin m => k < j ∧ k ∉ A) := by simp
      rw [hset, sum_insert hj']
      have hrest : ∑ k ∈ univ.filter (fun k : Fin m => k < j ∧ k ∉ A), ((G b₀ k).val + 1) =
          R b₀ := by
        refine sum_congr rfl fun k hk => ?_
        simp only [mem_filter, mem_univ, true_and] at hk
        rw [hGout b₀ k (ne_of_lt hk.1) hk.2]
      rw [hrest]
      simp only [G, ite_true]
      omega
  -- count
  set S₀ := Fintype.piFinset fun k : Fin m => if k ∈ insert j A then ({z} : Finset (Fin M)) else univ
  have hS₀ : #S₀ = M ^ (m - (t + 1)) := by
    rw [card_piFinset_slice, card_insert_of_notMem hjA, hA]
  rw [← hS₀]
  refine card_le_card_of_injOn G (fun b₀ _ => hG b₀) ?_
  intro b₀ hb₀ b₁ hb₁ hGb
  rw [mem_coe, Fintype.mem_piFinset] at hb₀ hb₁
  funext k
  by_cases hk : k ∈ insert j A
  · have h0 := hb₀ k
    have h1 := hb₁ k
    simp only [hk, ite_true, mem_singleton] at h0 h1
    rw [h0, h1]
  · have hkj : k ≠ j := fun h' => hk (mem_insert.2 (Or.inl h'))
    have hkA : k ∉ A := fun h' => hk (mem_insert.2 (Or.inr h'))
    have := congrFun hGb k
    rwa [hGout b₀ k hkj hkA, hGout b₁ k hkj hkA] at this

end Slice

end Erdos1183
