import Erdos1183.Chain

/-!
# The lower bound `F(n) ≥ c_t n^{t+1}`

* `exists_le_mul_card_filter`: an averaging (double counting) argument over block sizes and
  orderings.
* `exists_family`: monochromatic block-chain cubes of one ordering give a monochromatic
  union-closed family of at least half their number.
* `card_le_bigF`: the combination, `#P ≤ 2 (t+2)^M M^{t+1} F(n)`.
-/

open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

/-! ### Double counting -/

/-- If, for every `x ∈ P`, at least `D` choices of `b` make `Mono x b σ` hold for at least a
`1/K` fraction of the `σ`, then some pair `(b, σ)` works for at least
`#P · D / (K · #B)` of the `x ∈ P`. -/
lemma exists_le_mul_card_filter {X B S : Type*} [Fintype B] [Fintype S] [Nonempty B]
    [Nonempty S] (P : Finset X) (Mono : X → B → S → Prop) (K D : ℕ)
    (hP : ∀ x ∈ P, D ≤ #(univ.filter fun b =>
      Fintype.card S ≤ K * #(univ.filter fun σ => Mono x b σ))) :
    ∃ b σ, #P * D ≤ K * Fintype.card B * #(P.filter fun x => Mono x b σ) := by
  set N : X → B → ℕ := fun x b => #(univ.filter fun σ => Mono x b σ) with hN
  -- each `x ∈ P` contributes at least `D · #S / K`
  have h1 : ∀ x ∈ P, D * Fintype.card S ≤ K * ∑ b, N x b := by
    intro x hx
    set good := univ.filter fun b => Fintype.card S ≤ K * N x b
    calc D * Fintype.card S ≤ #good * Fintype.card S := Nat.mul_le_mul_right _ (hP x hx)
      _ = ∑ _b ∈ good, Fintype.card S := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ b ∈ good, K * N x b := sum_le_sum fun b hb => (mem_filter.1 hb).2
      _ ≤ ∑ b, K * N x b := sum_le_sum_of_subset (subset_univ _)
      _ = K * ∑ b, N x b := by rw [mul_sum]
  -- swapping the order of summation
  have h2 : ∑ p : B × S, #(P.filter fun x => Mono x p.1 p.2) = ∑ x ∈ P, ∑ b, N x b := by
    rw [Fintype.sum_prod_type]
    simp only [card_filter, hN]
    calc ∑ b, ∑ σ, ∑ x ∈ P, (if Mono x b σ then 1 else 0)
        = ∑ b, ∑ x ∈ P, ∑ σ, (if Mono x b σ then 1 else 0) :=
          sum_congr rfl fun b _ => sum_comm
      _ = ∑ x ∈ P, ∑ b, ∑ σ, (if Mono x b σ then 1 else 0) := sum_comm
  have h3 : ∑ _p : B × S, #P * D ≤
      ∑ p : B × S, K * Fintype.card B * #(P.filter fun x => Mono x p.1 p.2) := by
    calc ∑ _p : B × S, #P * D = Fintype.card B * Fintype.card S * (#P * D) := by
          rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]
      _ = Fintype.card B * ∑ _x ∈ P, D * Fintype.card S := by
          rw [sum_const, smul_eq_mul]; ring
      _ ≤ Fintype.card B * ∑ x ∈ P, K * ∑ b, N x b :=
          Nat.mul_le_mul_left _ (sum_le_sum h1)
      _ = K * Fintype.card B * ∑ x ∈ P, ∑ b, N x b := by
          simp only [mul_sum]
          exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ = ∑ p : B × S, K * Fintype.card B * #(P.filter fun x => Mono x p.1 p.2) := by
          rw [← h2, mul_sum]
  obtain ⟨p, -, hp⟩ := exists_le_of_sum_le univ_nonempty h3
  exact ⟨p.1, p.2, hp⟩

/-! ### From monochromatic cubes to a union-closed family -/

section Family

variable {n m M : ℕ} (h : m * M ≤ n) (b : Fin m → Fin M) (σ : Equiv.Perm (Fin n))

/-- The levels: blocks `k ≤ j` with the blocks in `B` removed. -/
def lev (j : Fin m) (B : Finset (Fin m)) : Finset (Fin m) :=
  univ.filter fun k => k ≤ j ∧ k ∉ B

/-- The union of the blocks in `K`, moved by the ordering `σ`. -/
def blocks (K : Finset (Fin m)) : Finset (Fin n) :=
  ((univ.filter fun q : Fin m × Fin M => q.1 ∈ K ∧ q.2 ≤ b q.1).map (grid h)).map
    σ.toEmbedding

lemma blocks_union (K K' : Finset (Fin m)) :
    blocks h b σ (K ∪ K') = blocks h b σ K ∪ blocks h b σ K' := by
  simp only [blocks, ← map_union, ← filter_or]
  congr 2
  ext q
  simp only [mem_filter, mem_univ, true_and, mem_union]
  tauto

lemma mem_blocks (K : Finset (Fin m)) (k : Fin m) :
    σ (grid h (k, b k)) ∈ blocks h b σ K ↔ k ∈ K := by
  simp only [blocks, mem_map_equiv, Equiv.symm_apply_apply, mem_map' (grid h), mem_filter,
    mem_univ, true_and, le_rfl, and_true]

lemma blocks_injective : Function.Injective (blocks h b σ) := by
  intro K K' hK
  ext k
  rw [← mem_blocks h b σ K, ← mem_blocks h b σ K', hK]

lemma cubeSet_chainLab (j : Fin m) (A : Finset (Fin m)) (x : Fin m → Bool) :
    (cubeSet (chainLab h b j A) x).map σ.toEmbedding =
      blocks h b σ (univ.filter fun k => k ≤ j ∧ (k ∉ A ∨ x k = false)) := by
  simp only [blocks]
  congr 1
  ext p
  rw [mem_cubeSet]
  simp only [mem_map, mem_filter, mem_univ, true_and]
  by_cases hp : ∃ q, grid h q = p
  · obtain ⟨q, rfl⟩ := hp
    rw [chainLab_grid, gridLab_eq_true]
    simp only [gridLab_eq_inl]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨i, ⟨h1, h2, h3, rfl⟩, h4⟩)
      · exact ⟨q, ⟨⟨h2, Or.inl h3⟩, h1⟩, rfl⟩
      · exact ⟨q, ⟨⟨h2, Or.inr h4⟩, h1⟩, rfl⟩
    · rintro ⟨q', ⟨⟨h2, h3⟩, h1⟩, hq'⟩
      obtain rfl := (grid h).injective hq'
      rcases h3 with h3 | h3
      · exact Or.inl ⟨h1, h2, h3⟩
      · by_cases hA : q'.1 ∈ A
        · exact Or.inr ⟨q'.1, ⟨h1, h2, hA, rfl⟩, h3⟩
        · exact Or.inl ⟨h1, h2, hA⟩
  · rw [chainLab_of_not h b j A p hp]
    simp only [Sum.inr.injEq, Bool.false_eq_true, reduceCtorEq, false_and, exists_false,
      or_self, false_iff, not_exists, not_and]
    intro q _ hq
    exact hp ⟨q, hq⟩

/-- A monochromatic block-chain cube gives all its members `lev j B` (`B ⊆ A`) one colour. -/
lemma colour_lev (χ : Colouring n) (j : Fin m) (A : Finset (Fin m))
    (hmono : CubeMono (pull χ σ) (chainLab h b j A)) (B : Finset (Fin m)) (hB : B ⊆ A) :
    χ (blocks h b σ (lev j B)) = χ (blocks h b σ (lev j ∅)) := by
  have key := hmono fun k => decide (k ∈ B)
  simp only [pull, cubeSet_chainLab] at key
  convert key using 3
  · ext k
    simp only [lev, mem_filter, mem_univ, true_and, decide_eq_false_iff_not]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr h2⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, fun h' => h2 (hB h')⟩
      · exact ⟨h1, h2⟩
  · ext k
    simp [lev]

omit h b σ in
lemma lev_union (j j' : Fin m) (B B' : Finset (Fin m)) (hjj : j ≤ j') (hB' : ∀ a ∈ B', a ≤ j) :
    lev j B ∪ lev j' B' = lev j' (B ∩ B') := by
  ext k
  simp only [lev, mem_union, mem_filter, mem_univ, true_and, mem_inter, not_and_or]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1.trans hjj, Or.inl h2⟩
    · exact ⟨h1, Or.inr h2⟩
  · rintro ⟨h1, h2 | h2⟩
    · by_cases hk : k ∈ B'
      · exact Or.inl ⟨hB' k hk, h2⟩
      · exact Or.inr ⟨h1, hk⟩
    · exact Or.inr ⟨h1, h2⟩

/-- **The family.** The monochromatic cubes of one ordering and one block-size vector give a
monochromatic union-closed family of at least half their number. -/
lemma exists_family (χ : Colouring n) (P : Finset (Fin m × Finset (Fin m)))
    (hP : ∀ x ∈ P, ∀ y ∈ P, ∀ a ∈ y.2, a < x.1) :
    ∃ 𝓕, UnionClosed 𝓕 ∧ Monochromatic χ 𝓕 ∧
      #(P.filter fun x => CubeMono (pull χ σ) (chainLab h b x.1 x.2)) ≤ 2 * #𝓕 := by
  set S := P.filter fun x => CubeMono (pull χ σ) (chainLab h b x.1 x.2)
  set col : Fin m × Finset (Fin m) → Bool := fun x => χ (blocks h b σ (lev x.1 ∅))
  -- the majority colour
  obtain ⟨c, hc⟩ : ∃ c : Bool, #S ≤ 2 * #(S.filter fun x => col x = c) := by
    have hsplit := card_filter_add_card_filter_not (s := S) (fun x => col x = true)
    by_cases h' : #(S.filter fun x => ¬ col x = true) ≤ #(S.filter fun x => col x = true)
    · exact ⟨true, by omega⟩
    · refine ⟨false, ?_⟩
      simp only [Bool.not_eq_true] at hsplit h'
      omega
  set Sc := S.filter fun x => col x = c
  have hSc : ∀ x ∈ Sc, x ∈ P ∧ CubeMono (pull χ σ) (chainLab h b x.1 x.2) ∧ col x = c := by
    intro x hx
    simp only [Sc, S, mem_filter] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  refine ⟨Sc.biUnion fun x => x.2.powerset.image fun B => blocks h b σ (lev x.1 B), ?_, ?_, ?_⟩
  · -- union-closed
    intro U hU V hV
    simp only [mem_biUnion, mem_image, mem_powerset] at hU hV ⊢
    obtain ⟨x, hx, B, hB, rfl⟩ := hU
    obtain ⟨y, hy, B', hB', rfl⟩ := hV
    rw [← blocks_union]
    rcases le_total x.1 y.1 with hxy | hyx
    · refine ⟨y, hy, B ∩ B', inter_subset_right.trans hB', ?_⟩
      rw [lev_union _ _ _ _ hxy fun a ha => (hP x (hSc x hx).1 y (hSc y hy).1 a (hB' ha)).le]
    · refine ⟨x, hx, B ∩ B', inter_subset_left.trans hB, ?_⟩
      rw [union_comm, lev_union _ _ _ _ hyx fun a ha =>
        (hP y (hSc y hy).1 x (hSc x hx).1 a (hB ha)).le, inter_comm]
  · -- monochromatic
    have hcol : ∀ U ∈ Sc.biUnion fun x => x.2.powerset.image fun B => blocks h b σ (lev x.1 B),
        χ U = c := by
      intro U hU
      simp only [mem_biUnion, mem_image, mem_powerset] at hU
      obtain ⟨x, hx, B, hB, rfl⟩ := hU
      rw [colour_lev h b σ χ x.1 x.2 (hSc x hx).2.1 B hB]
      exact (hSc x hx).2.2
    intro U hU V hV
    rw [hcol U hU, hcol V hV]
  · -- size
    refine hc.trans (Nat.mul_le_mul_left _ ?_)
    refine card_le_card_of_injOn (fun x => blocks h b σ (lev x.1 x.2)) ?_ ?_
    · intro x hx
      simp only [coe_biUnion, mem_coe, coe_image, coe_powerset, Set.mem_iUnion, Set.mem_image,
        Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
      exact ⟨x, hx, x.2, subset_rfl, rfl⟩
    · intro x hx y hy hxy
      have hxP := (hSc x hx).1
      have hyP := (hSc y hy).1
      have hl : lev x.1 x.2 = lev y.1 y.2 := blocks_injective h b σ hxy
      have hmem : ∀ z ∈ P, ∀ k, k ∈ lev z.1 z.2 ↔ k ≤ z.1 ∧ k ∉ z.2 := by
        intro z _ k
        simp [lev]
      have hx1 : x.1 ∈ lev y.1 y.2 := by
        rw [← hl, hmem x hxP]
        exact ⟨le_rfl, fun h' => lt_irrefl _ (hP x hxP x hxP _ h')⟩
      have hy1 : y.1 ∈ lev x.1 x.2 := by
        rw [hl, hmem y hyP]
        exact ⟨le_rfl, fun h' => lt_irrefl _ (hP y hyP y hyP _ h')⟩
      rw [hmem y hyP] at hx1
      rw [hmem x hxP] at hy1
      have h1 : x.1 = y.1 := le_antisymm hx1.1 hy1.1
      refine Prod.ext h1 ?_
      ext a
      have hax : a ∈ x.2 ↔ a ≤ x.1 ∧ a ∉ lev x.1 x.2 := by
        rw [hmem x hxP]
        constructor
        · intro ha
          exact ⟨(hP x hxP x hxP a ha).le, fun h' => h'.2 ha⟩
        · rintro ⟨h2, h3⟩
          by_contra h4
          exact h3 ⟨h2, h4⟩
      have hay : a ∈ y.2 ↔ a ≤ y.1 ∧ a ∉ lev y.1 y.2 := by
        rw [hmem y hyP]
        constructor
        · intro ha
          exact ⟨(hP y hyP y hyP a ha).le, fun h' => h'.2 ha⟩
        · rintro ⟨h2, h3⟩
          by_contra h4
          exact h3 ⟨h2, h4⟩
      rw [hax, hay, hl, h1]

end Family

/-! ### The bound -/

section Bound

variable {n m t M : ℕ}

/-- **Combination.** If `P` is a set of (level, generators) pairs with all generators below all
levels, then `#P ≤ 2 (t+2)^M M^{t+1} F(n)`. -/
theorem card_le_bigF (ht : 1 ≤ t)
    (hgood : ∀ r (χ : Colouring n), ∃ π : Fin M → Bool ⊕ Fin t, (∀ i, ∃ q, π q = Sum.inr i) ∧
      Fintype.card (Equiv.Perm (Fin n)) ≤ (t + 2) ^ M * Ncount χ (patLab (n := n) M r π))
    (hmn : m * M < n) (P : Finset (Fin m × Finset (Fin m)))
    (hP : ∀ x ∈ P, ∀ y ∈ P, ∀ a ∈ y.2, a < x.1) (hPt : ∀ x ∈ P, #x.2 = t) :
    #P ≤ 2 * (t + 2) ^ M * M ^ (t + 1) * bigF n := by
  rcases P.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have h : m * M ≤ n := hmn.le
  have hm : t + 1 ≤ m := by
    have hj : x₀.1 ∉ x₀.2 := fun h' => lt_irrefl _ (hP x₀ hx₀ x₀ hx₀ _ h')
    have := card_le_univ (insert x₀.1 x₀.2)
    rw [card_insert_of_notMem hj, hPt x₀ hx₀, Fintype.card_fin] at this
    exact this
  have hM0 : 0 < M := by
    obtain ⟨π, hπ, -⟩ := hgood 0 (fun _ => true)
    obtain ⟨q, -⟩ := hπ ⟨0, ht⟩
    exact q.pos
  -- a colouring attaining `F(n)`
  obtain ⟨χ, hχ⟩ := (bigF_le_iff (n := n) (bigF n)).1 le_rfl
  have : Nonempty (Fin m → Fin M) := ⟨fun _ => ⟨0, hM0⟩⟩
  obtain ⟨b, σ, hbσ⟩ := exists_le_mul_card_filter P
    (fun x b σ => CubeMono (pull χ σ) (chainLab h b x.1 x.2)) ((t + 2) ^ M) (M ^ (m - (t + 1)))
    (fun x hx => card_goodSizes h χ hmn ht (fun r => hgood r χ) x.1 x.2 (hPt x hx)
      (hP x hx x hx))
  obtain ⟨𝓕, hU, hMono, h𝓕⟩ := exists_family h b σ χ P hP
  have h𝓕' := hχ 𝓕 hU hMono
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hbσ
  have hsplit : M ^ m = M ^ (m - (t + 1)) * M ^ (t + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  have hpos : 0 < M ^ (m - (t + 1)) := pow_pos hM0 _
  have key : #P * M ^ (m - (t + 1)) ≤
      (2 * (t + 2) ^ M * M ^ (t + 1) * bigF n) * M ^ (m - (t + 1)) := by
    calc #P * M ^ (m - (t + 1))
        ≤ (t + 2) ^ M * M ^ m *
          #(P.filter fun x => CubeMono (pull χ σ) (chainLab h b x.1 x.2)) := hbσ
      _ ≤ (t + 2) ^ M * M ^ m * (2 * bigF n) :=
          Nat.mul_le_mul_left _ (h𝓕.trans (Nat.mul_le_mul_left _ h𝓕'))
      _ = (2 * (t + 2) ^ M * M ^ (t + 1) * bigF n) * M ^ (m - (t + 1)) := by
          rw [hsplit]; ring
  exact Nat.le_of_mul_le_mul_right key hpos

lemma card_filter_le_val (m s : ℕ) :
    #(univ.filter fun j : Fin m => s ≤ j.val) = m - s := by
  rw [← card_Ico_fin (n := m) s m le_rfl]
  congr 1
  ext j
  simp

lemma card_filter_lt_val (m s : ℕ) (hs : s ≤ m) :
    #(univ.filter fun k : Fin m => k.val < s) = s := by
  have := card_Ico_fin (n := m) 0 s hs
  simp only [zero_le, true_and, Nat.sub_zero] at this
  exact this

/-- **Polynomial lower bound.** For every `t ≥ 1` there are `M > 0` and `K > 0` such that
`(s + 1 - t)^{t+1} ≤ K F(n)` for all `n ≥ 1`, where `s = ⌊⌊(n-1)/M⌋/2⌋`. -/
theorem pow_le_mul_bigF (t : ℕ) (ht : 1 ≤ t) : ∃ M > 0, ∃ K > 0, ∀ n, 1 ≤ n →
    ((n - 1) / M / 2 + 1 - t) ^ (t + 1) ≤ K * bigF n := by
  obtain ⟨M, hM⟩ := exists_good_pattern t
  have hM0 : 0 < M := by
    obtain ⟨π, hπ, -⟩ := hM 0 0 (fun _ => true)
    obtain ⟨q, -⟩ := hπ ⟨0, ht⟩
    exact q.pos
  refine ⟨M, hM0, t.factorial * (2 * (t + 2) ^ M * M ^ (t + 1)), by positivity, fun n hn => ?_⟩
  set m := (n - 1) / M with hm
  set s := m / 2 with hs
  have hmn : m * M < n := by
    have : m * M ≤ n - 1 := Nat.div_mul_le_self (n - 1) M
    omega
  have hsm : s ≤ m := Nat.div_le_self _ _
  set P : Finset (Fin m × Finset (Fin m)) := (univ.filter fun j : Fin m => s ≤ j.val) ×ˢ
    powersetCard t (univ.filter fun k : Fin m => k.val < s)
  have hP : ∀ x ∈ P, ∀ y ∈ P, ∀ a ∈ y.2, a < x.1 := by
    intro x hx y hy a ha
    simp only [P, mem_product, mem_filter, mem_univ, true_and, mem_powersetCard] at hx hy
    have := hy.2.1 ha
    simp only [mem_filter, mem_univ, true_and] at this
    exact Fin.lt_def.2 (by omega)
  have hPt : ∀ x ∈ P, #x.2 = t := by
    intro x hx
    simp only [P, mem_product, mem_powersetCard] at hx
    exact hx.2.2
  have hbound := card_le_bigF ht (fun r χ => hM n r χ) hmn P hP hPt
  have hcardP : #P = (m - s) * s.choose t := by
    simp only [P, card_product, card_powersetCard, card_filter_le_val,
      card_filter_lt_val m s hsm]
  have hdesc : (s + 1 - t) ^ t ≤ t.factorial * s.choose t := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.pow_sub_le_descFactorial s t
  have hms : s + 1 - t ≤ m - s := by omega
  calc (s + 1 - t) ^ (t + 1) = (s + 1 - t) * (s + 1 - t) ^ t := by ring
    _ ≤ (m - s) * (t.factorial * s.choose t) := Nat.mul_le_mul hms hdesc
    _ = t.factorial * #P := by rw [hcardP]; ring
    _ ≤ t.factorial * (2 * (t + 2) ^ M * M ^ (t + 1) * bigF n) := Nat.mul_le_mul_left _ hbound
    _ = t.factorial * (2 * (t + 2) ^ M * M ^ (t + 1)) * bigF n := by ring

end Bound

end Erdos1183
