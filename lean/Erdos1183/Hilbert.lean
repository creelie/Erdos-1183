import Erdos1183.Colours

/-!
# Colourings by cardinality and Hilbert cubes

A colouring `χ(S) = g(|S|)` is invariant under all orderings of the ground set, so a cube is
monochromatic for one ordering exactly when it is monochromatic for all of them. Reading the
cubes through the sizes of their members turns the supersaturation and averaging steps into
statements about Hilbert cubes `H(u; a_1, …, a_t) = {u + ∑_{i ∈ I} a_i : I ⊆ [t]}` of integers.

* `hilbert_window`: Hilbert's lemma with an explicit window. Every `k`-colouring of the integers
  is constant on a Hilbert cube `H(u; a_1, …, a_t)` with `r ≤ u` and `u + ∑ a_i ≤ r + t^2 k^{2^t}`.
* `hilbert_cubes`: many monochromatic Hilbert cubes hang from the partial sums of one sequence
  `β_1, …, β_m` of integers in `[1, M]`.
-/

open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

section Card

variable {n : ℕ}

/-- A cardinality colouring is invariant under orderings. -/
lemma pull_card (g : ℕ → κ) (σ : Equiv.Perm (Fin n)) :
    pull (fun S : Finset (Fin n) => g #S) σ = fun S => g #S := by
  funext S
  simp [pull]

/-- For a cardinality colouring, a cube that is monochromatic for a positive proportion of the
orderings is monochromatic. -/
lemma cubeMono_of_card_le {G : Type*} [Fintype G] [DecidableEq G] (g : ℕ → κ)
    (lab : Fin n → G ⊕ Bool) (D : ℕ)
    (h : Fintype.card (Equiv.Perm (Fin n)) ≤ D * Ncount (fun S : Finset (Fin n) => g #S) lab) :
    CubeMono (fun S : Finset (Fin n) => g #S) lab := by
  have hpos : 0 < Ncount (fun S : Finset (Fin n) => g #S) lab := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    rcases Nat.eq_zero_or_pos (Ncount (fun S : Finset (Fin n) => g #S) lab) with h0 | h0
    · rw [h0, mul_zero] at h
      omega
    · exact h0
  obtain ⟨σ, hσ⟩ := card_pos.1 hpos
  have := (mem_filter.1 hσ).2
  rwa [pull_card] at this

/-- The size of a member of a hole cube. -/
lemma card_cubeSet {G : Type*} [Fintype G] [DecidableEq G] (lab : Fin n → G ⊕ Bool)
    (x : G → Bool) :
    #(cubeSet lab x) = #(univ.filter fun p => lab p = Sum.inr true) +
      ∑ i ∈ univ.filter (fun i => x i = false), #(univ.filter fun p => lab p = Sum.inl i) := by
  have hset : cubeSet lab x = (univ.filter fun p => lab p = Sum.inr true) ∪
      (univ.filter fun i => x i = false).biUnion fun i => univ.filter fun p => lab p = Sum.inl i := by
    ext p
    simp only [mem_cubeSet, mem_union, mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · rintro (h | ⟨i, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, h2, h1⟩
    · rintro (h | ⟨i, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, h2, h1⟩
  rw [hset, card_union_of_disjoint, card_biUnion]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [disjoint_left]
    intro p hp hp'
    simp only [mem_filter, mem_univ, true_and] at hp hp'
    rw [hp] at hp'
    exact hij (Sum.inl_injective hp')
  · rw [disjoint_left]
    intro p hp hp'
    simp only [mem_filter, mem_univ, true_and, mem_biUnion] at hp hp'
    obtain ⟨i, -, hi⟩ := hp'
    rw [hp] at hi
    exact Sum.inr_ne_inl hi

end Card

/-- **Hilbert's lemma with an explicit window.** For `k ≥ 2` colours, `t ≥ 1` and `r ≥ 0`,
every colouring `g` of the integers is constant on a Hilbert cube `{u + ∑_{i ∈ I} a_i}` with
`r ≤ u`, all `a_i ≥ 1` and `u + ∑ a_i ≤ r + t^2 k^{2^t}`. -/
theorem hilbert_window (hk : 2 ≤ Fintype.card κ) (t : ℕ) (ht : 1 ≤ t) (r : ℕ) (g : ℕ → κ) :
    ∃ (u : ℕ) (a : Fin t → ℕ), r ≤ u ∧ (∀ i, 1 ≤ a i) ∧
      u + ∑ i, a i ≤ r + t ^ 2 * Fintype.card κ ^ 2 ^ t ∧
      ∀ I : Finset (Fin t), g (u + ∑ i ∈ I, a i) = g u := by
  set k := Fintype.card κ with hkdef
  set M := boxM k t with hMdef
  set n := M + r with hn
  set χ : Finset (Fin n) → κ := fun S => g #S with hχ
  obtain ⟨π, hπ, hcnt⟩ := exists_good_pattern (n := n) hk t ht r χ
  set lab := patLab (n := n) M r π with hlab
  have hmono : CubeMono χ lab := cubeMono_of_card_le g lab _ hcnt
  set u := #(univ.filter fun p => lab p = Sum.inr true) with hu
  set a : Fin t → ℕ := fun i => #(univ.filter fun p => lab p = Sum.inl i) with ha
  have hsize : ∀ x : Fin t → Bool,
      #(cubeSet lab x) = u + ∑ i ∈ univ.filter (fun i => x i = false), a i :=
    fun x => card_cubeSet lab x
  refine ⟨u, a, ?_, ?_, ?_, ?_⟩
  · rw [hu, hlab, card_patLab_true (by omega)]
    omega
  · intro i
    rw [ha]
    simp only
    rw [hlab, card_patLab_inl (by omega)]
    obtain ⟨q, hq⟩ := hπ i
    exact card_pos.2 ⟨q, by simp [hq]⟩
  · have h := hsize fun _ => false
    have hall : ∑ i ∈ univ.filter (fun i : Fin t => (fun _ : Fin t => false) i = false), a i =
        ∑ i, a i := by
      congr 1
      ext i
      simp
    rw [hall] at h
    rw [← h, ← boxM_eq_k]
    exact (card_le_univ _).trans (by simp [n, hMdef]; omega)
  · have hI : ∀ I : Finset (Fin t), univ.filter (fun i => decide (i ∉ I) = false) = I := by
      intro I
      ext i
      simp
    have key : ∀ I : Finset (Fin t), g (u + ∑ i ∈ I, a i) = g #(cubeSet lab fun _ => false) := by
      intro I
      have h1 := hmono fun i => decide (i ∉ I)
      simp only [hχ] at h1
      rw [hsize, hI] at h1
      exact h1
    intro I
    rw [key I, ← key ∅, sum_empty, add_zero]

/-- The pairs `(j, A)` of the chain construction: `s ≤ j < m` and `A` a `t`-subset of
`{0, …, s-1}`, where `s = ⌊m/2⌋`. -/
def hilbertPairs (m t : ℕ) : Finset (Fin m × Finset (Fin m)) :=
  (univ.filter fun j : Fin m => m / 2 ≤ j.val) ×ˢ
    powersetCard t (univ.filter fun k : Fin m => k.val < m / 2)

lemma card_blocks {n m M : ℕ} (h : m * M ≤ n) (b : Fin m → Fin M) (σ : Equiv.Perm (Fin n))
    (K : Finset (Fin m)) : #(blocks h b σ K) = ∑ k ∈ K, ((b k).val + 1) := by
  simp only [blocks, card_map]
  rw [card_filter, Fintype.sum_prod_type]
  have hk : ∀ k : Fin m, (∑ c : Fin M, if k ∈ K ∧ c ≤ b k then 1 else 0) =
      if k ∈ K then (b k).val + 1 else 0 := by
    intro k
    by_cases hkK : k ∈ K
    · simp only [hkK, true_and, ite_true]
      rw [← card_filter, card_fin_le]
    · simp [hkK]
  simp_rw [hk]
  rw [sum_ite_mem, univ_inter]

/-- **Monochromatic Hilbert cubes along one sequence.** Let `k ≥ 2`, `t ≥ 1`,
`M = t^2 k^{2^t}`, `n ≥ 4 M (t + 1)`, `m = ⌊(n-1)/M⌋` and `s = ⌊m/2⌋`. For every colouring `g`
of the integers there are `β_0, …, β_{m-1} ∈ [1, M]` with `∑ β_i < n` and a colour `c` such
that for at least `n^{t+1} / (k t^t (4 M^2)^{t+1})` of the pairs `(j, A)` with `s ≤ j < m` and
`A` a `t`-subset of `{0, …, s-1}`, the colouring `g` takes the value `c` at every point
`∑_{i ≤ j, i ∉ B} β_i`, `B ⊆ A`, of the Hilbert cube attached to `(j, A)`. -/
theorem hilbert_cubes (hk : 2 ≤ Fintype.card κ) (t : ℕ) (ht : 1 ≤ t) (n : ℕ)
    (hn : 4 * boxM (Fintype.card κ) t * (t + 1) ≤ n) (g : ℕ → κ) :
    ∃ β : Fin ((n - 1) / boxM (Fintype.card κ) t) → ℕ,
      (∀ i, 1 ≤ β i ∧ β i ≤ boxM (Fintype.card κ) t) ∧ ∑ i, β i < n ∧ ∃ c : κ,
      n ^ (t + 1) ≤ Fintype.card κ * t ^ t * (4 * boxM (Fintype.card κ) t ^ 2) ^ (t + 1) *
        #((hilbertPairs ((n - 1) / boxM (Fintype.card κ) t) t).filter fun x =>
          ∀ B ⊆ x.2, g (∑ i ∈ univ.filter (fun i => i ≤ x.1 ∧ i ∉ B), β i) = c) := by
  set k := Fintype.card κ with hkdef
  set M := boxM k t with hMdef
  have hMt : t + 1 ≤ M := succ_le_boxM_k k t hk ht
  have hM0 : 0 < M := by omega
  set m := (n - 1) / M with hm
  set s := m / 2 with hs
  set P := hilbertPairs m t with hPdef
  have hmn : m * M < n := by
    have : m * M ≤ n - 1 := Nat.div_mul_le_self (n - 1) M
    have : 1 ≤ n := by nlinarith
    omega
  have h : m * M ≤ n := hmn.le
  have hnm : n ≤ M * (m + 1) := by
    have := Nat.lt_mul_div_succ (n - 1) hM0
    rw [← hm] at this
    omega
  have hs1 : 2 * t + 1 ≤ s := by
    have h1 : M * (4 * (t + 1)) ≤ M * (2 * s + 2) := by
      calc M * (4 * (t + 1)) = 4 * M * (t + 1) := by ring
        _ ≤ n := hn
        _ ≤ M * (m + 1) := hnm
        _ ≤ M * (2 * s + 2) := Nat.mul_le_mul_left _ (by omega)
    have := Nat.le_of_mul_le_mul_left h1 hM0
    omega
  have hn4 : n ≤ 4 * M * s := by
    calc n ≤ M * (m + 1) := hnm
      _ ≤ M * (4 * s) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * M * s := by ring
  have hsm : s ≤ m := Nat.div_le_self _ _
  have hP : ∀ x ∈ P, ∀ y ∈ P, ∀ a ∈ y.2, a < x.1 := by
    intro x hx y hy a ha
    simp only [hPdef, hilbertPairs, mem_product, mem_filter, mem_univ, true_and,
      mem_powersetCard] at hx hy
    have := hy.2.1 ha
    simp only [mem_filter, mem_univ, true_and] at this
    exact Fin.lt_def.2 (by omega)
  have hPt : ∀ x ∈ P, #x.2 = t := by
    intro x hx
    simp only [hPdef, hilbertPairs, mem_product, mem_powersetCard] at hx
    exact hx.2.2
  -- the cardinality colouring
  set χ : Finset (Fin n) → κ := fun S => g #S with hχ
  have hgood := fun r => exists_good_pattern (n := n) hk t ht r χ
  -- for each pair, many block-size vectors make its cube monochromatic
  have hslice : ∀ x ∈ P, M ^ (m - (t + 1)) ≤ #(univ.filter fun b : Fin m → Fin M =>
      Fintype.card Unit ≤ 1 * #(univ.filter fun _ : Unit => CubeMono χ (chainLab h b x.1 x.2))) := by
    intro x hx
    refine (card_goodSizes h χ (k ^ 2 ^ t) hmn ht hgood x.1 x.2 (hPt x hx) (hP x hx x hx)).trans
      (card_le_card fun b hb => ?_)
    simp only [goodSizes, mem_filter, mem_univ, true_and] at hb ⊢
    have := cubeMono_of_card_le g _ _ hb
    rw [← hχ] at this
    simp [this]
  have : Nonempty (Fin m → Fin M) := ⟨fun _ => ⟨0, hM0⟩⟩
  obtain ⟨b, -, hb⟩ := exists_le_mul_card_filter P
    (fun x b (_ : Unit) => CubeMono χ (chainLab h b x.1 x.2)) 1 (M ^ (m - (t + 1))) hslice
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, one_mul] at hb
  set S := P.filter fun x => CubeMono χ (chainLab h b x.1 x.2) with hS
  have hm1 : t + 1 ≤ m := by omega
  have hPS : #P ≤ M ^ (t + 1) * #S := by
    have hsplit : M ^ m = M ^ (m - (t + 1)) * M ^ (t + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hm1]
    rw [hsplit] at hb
    have hpos : 0 < M ^ (m - (t + 1)) := pow_pos hM0 _
    have key : #P * M ^ (m - (t + 1)) ≤ (M ^ (t + 1) * #S) * M ^ (m - (t + 1)) := by
      calc #P * M ^ (m - (t + 1)) ≤ M ^ (m - (t + 1)) * M ^ (t + 1) * #S := hb
        _ = (M ^ (t + 1) * #S) * M ^ (m - (t + 1)) := by ring
    exact Nat.le_of_mul_le_mul_right key hpos
  -- the majority colour
  set col : Fin m × Finset (Fin m) → κ := fun x => χ (blocks h b 1 (lev x.1 ∅)) with hcol
  obtain ⟨c, hc⟩ : ∃ c : κ, #S ≤ k * #(S.filter fun x => col x = c) := by
    by_cases hS0 : S = ∅
    · rw [hS0, card_empty]
      exact ⟨g 0, Nat.zero_le _⟩
    · obtain ⟨x, -⟩ := nonempty_iff_ne_empty.2 hS0
      have hsum : ∑ c : κ, #S ≤ ∑ c : κ, k * #(S.filter fun x => col x = c) := by
        rw [← mul_sum, ← card_eq_sum_card_fiberwise (fun y _ => mem_univ (col y)), sum_const,
          card_univ, smul_eq_mul]
      obtain ⟨c, -, hc⟩ := exists_le_of_sum_le ⟨col x, mem_univ _⟩ hsum
      exact ⟨c, hc⟩
  set β : Fin m → ℕ := fun i => (b i).val + 1 with hβ
  refine ⟨β, fun i => ⟨by simp [hβ], by simp only [hβ]; have := (b i).isLt; omega⟩, ?_, c, ?_⟩
  · calc ∑ i, β i ≤ ∑ _i : Fin m, M := sum_le_sum fun i _ => by
          simp only [hβ]; have := (b i).isLt; omega
      _ = m * M := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      _ < n := hmn
  · -- the monochromatic cubes of colour `c` give monochromatic Hilbert cubes
    have hsub : S.filter (fun x => col x = c) ⊆ P.filter fun x =>
        ∀ B ⊆ x.2, g (∑ i ∈ univ.filter (fun i => i ≤ x.1 ∧ i ∉ B), β i) = c := by
      intro x hx
      simp only [hS, mem_filter] at hx
      obtain ⟨⟨hxP, hxm⟩, hxc⟩ := hx
      refine mem_filter.2 ⟨hxP, fun B hB => ?_⟩
      have hmono : CubeMono (pull χ 1) (chainLab h b x.1 x.2) := by
        rw [hχ, pull_card]; exact hxm
      have h1 := colour_lev h b 1 χ x.1 x.2 hmono B hB
      rw [← hxc]
      simp only [hcol]
      rw [← h1]
      simp only [hχ, card_blocks, hβ, lev]
    have hcount : #P ≤ M ^ (t + 1) * (k * #(P.filter fun x =>
        ∀ B ⊆ x.2, g (∑ i ∈ univ.filter (fun i => i ≤ x.1 ∧ i ∉ B), β i) = c)) :=
      hPS.trans (Nat.mul_le_mul_left _ (hc.trans (Nat.mul_le_mul_left _ (card_le_card hsub))))
    have hcardP : #P = (m - s) * s.choose t := by
      rw [hPdef, hilbertPairs, card_product, card_powersetCard, card_filter_le_val,
        card_filter_lt_val m (m / 2) (Nat.div_le_self _ _)]
    have hch := pow_le_pow_mul_choose t s (by omega)
    have hsms : s ≤ m - s := by omega
    have h1 : s ^ (t + 1) ≤ t ^ t * #P := by
      calc s ^ (t + 1) = s * s ^ t := by ring
        _ ≤ (m - s) * (t ^ t * s.choose t) := Nat.mul_le_mul hsms hch
        _ = t ^ t * #P := by rw [hcardP]; ring
    calc n ^ (t + 1) ≤ (4 * M * s) ^ (t + 1) := Nat.pow_le_pow_left hn4 _
      _ = (4 * M) ^ (t + 1) * s ^ (t + 1) := by ring
      _ ≤ (4 * M) ^ (t + 1) * (t ^ t * (M ^ (t + 1) * (k * #(P.filter fun x =>
          ∀ B ⊆ x.2, g (∑ i ∈ univ.filter (fun i => i ≤ x.1 ∧ i ∉ B), β i) = c)))) :=
          Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ hcount))
      _ = k * t ^ t * (4 * M ^ 2) ^ (t + 1) * #(P.filter fun x =>
          ∀ B ⊆ x.2, g (∑ i ∈ univ.filter (fun i => i ≤ x.1 ∧ i ∉ B), β i) = c) := by ring

end Erdos1183
