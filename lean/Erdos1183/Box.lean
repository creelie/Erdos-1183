import Erdos1183.Cube
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The box inequality and supersaturation

For `x x' : Fin t → G` and `ω : Fin t → Bool`, the point `boxPt x x' ω` takes the coordinate
`x' i` where `ω i = true` and `x i` elsewhere. The box inequality (`box_ineq`) says that for
`f ≥ 0`, the average over `x, x'` of `∏_ω f (boxPt x x' ω)` is at least `(E f)^(2^t)`.

Applied to the colour classes of the colouring `x ↦ χ (σ (S x ∪ R))` of a grid of `t` chains
of length `L`, it shows that for `k ≥ 2` colours a proportion `k^{-2^t}` of the orderings makes
some fixed cube monochromatic (`exists_good_pattern`), with `L = t k^{2^t}`.
-/

open Finset

namespace Erdos1183

open scoped Classical

set_option linter.unusedSectionVars false

section BoxIneq

variable {G : Type*} [Fintype G]

/-- The vertex of the box spanned by `x` and `x'` selected by `ω`. -/
def boxPt {t : ℕ} (x x' : Fin t → G) (ω : Fin t → Bool) : Fin t → G :=
  fun i => if ω i then x' i else x i

/-- The sum over all pairs `(x, x')` of the product of `f` over the vertices of their box. -/
noncomputable def boxSum {t : ℕ} (f : (Fin t → G) → ℝ) : ℝ :=
  ∑ p : (Fin t → G) × (Fin t → G), ∏ ω : Fin t → Bool, f (boxPt p.1 p.2 ω)

lemma boxPt_false {t : ℕ} (x x' : Fin t → G) : boxPt x x' (fun _ => false) = x := by
  funext i
  simp [boxPt]

lemma boxPt_cons {t : ℕ} (a a' : G) (y y' : Fin t → G) (b : Bool) (ω : Fin t → Bool) :
    boxPt (Fin.cons a y : Fin (t + 1) → G) (Fin.cons a' y') (Fin.cons b ω) =
      Fin.cons (if b then a' else a) (boxPt y y' ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [boxPt]

lemma consEquiv_eq {α : Type*} {t : ℕ} (p : α × (Fin t → α)) :
    (Fin.consEquiv fun _ : Fin (t + 1) => α) p = Fin.cons p.1 p.2 := rfl

lemma prod_box_cons {t : ℕ} (f : (Fin (t + 1) → G) → ℝ) (a a' : G) (y y' : Fin t → G) :
    ∏ ω : Fin (t + 1) → Bool, f (boxPt (Fin.cons a y) (Fin.cons a' y') ω) =
      (∏ ω : Fin t → Bool, f (Fin.cons a' (boxPt y y' ω))) *
        ∏ ω : Fin t → Bool, f (Fin.cons a (boxPt y y' ω)) := by
  rw [← (Fin.consEquiv fun _ : Fin (t + 1) => Bool).prod_comp, Fintype.prod_prod_type,
    Fintype.prod_bool]
  simp only [consEquiv_eq, boxPt_cons]
  simp

/-- Splitting off the first coordinate turns the box sum into a sum of squares. -/
lemma boxSum_succ {t : ℕ} (f : (Fin (t + 1) → G) → ℝ) :
    boxSum f = ∑ p : (Fin t → G) × (Fin t → G),
      (∑ a : G, ∏ ω : Fin t → Bool, f (Fin.cons a (boxPt p.1 p.2 ω))) ^ 2 := by
  have h1 : boxSum f = ∑ q : (G × (Fin t → G)) × (G × (Fin t → G)),
      (∏ ω : Fin t → Bool, f (Fin.cons q.2.1 (boxPt q.1.2 q.2.2 ω))) *
        ∏ ω : Fin t → Bool, f (Fin.cons q.1.1 (boxPt q.1.2 q.2.2 ω)) := by
    unfold boxSum
    rw [← ((Fin.consEquiv fun _ : Fin (t + 1) => G).prodCongr
      (Fin.consEquiv fun _ : Fin (t + 1) => G)).sum_comp]
    refine sum_congr rfl fun q _ => ?_
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, consEquiv_eq]
    exact prod_box_cons f _ _ _ _
  rw [h1]
  have h2 : ∀ p : (Fin t → G) × (Fin t → G),
      (∑ a : G, ∏ ω : Fin t → Bool, f (Fin.cons a (boxPt p.1 p.2 ω))) ^ 2 =
        ∑ aa : G × G, (∏ ω : Fin t → Bool, f (Fin.cons aa.2 (boxPt p.1 p.2 ω))) *
          ∏ ω : Fin t → Bool, f (Fin.cons aa.1 (boxPt p.1 p.2 ω)) := by
    intro p
    rw [sq, sum_mul_sum, Fintype.sum_prod_type]
    exact sum_congr rfl fun a _ => sum_congr rfl fun a' _ => mul_comm _ _
  simp_rw [h2]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun q => ((q.1.2, q.2.2), (q.1.1, q.2.1))
      invFun := fun r => ((r.2.1, r.1.1), (r.2.2, r.1.2))
      left_inv := fun q => rfl
      right_inv := fun r => rfl } _ _ fun q => rfl

variable [Nonempty G]

/-- **Box inequality.** For `f ≥ 0` on `G^t`, with `N = |G|`,
`N^{2t} (∑ f / N^t)^{2^t} ≤ ∑_{x, x'} ∏_ω f (boxPt x x' ω)`. -/
theorem box_ineq : ∀ (t : ℕ) (f : (Fin t → G) → ℝ), (∀ x, 0 ≤ f x) →
    (Fintype.card G : ℝ) ^ (2 * t) * ((∑ x, f x) / (Fintype.card G : ℝ) ^ t) ^ 2 ^ t ≤
      boxSum f := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  intro t
  induction t with
  | zero =>
    intro f _
    have hx : ∀ p : (Fin 0 → G) × (Fin 0 → G), ∏ ω : Fin 0 → Bool, f (boxPt p.1 p.2 ω) =
        f default := fun p => by
      rw [Fintype.prod_unique]
      congr 1
      exact Subsingleton.elim _ _
    unfold boxSum
    simp only [hx, mul_zero, pow_zero, one_mul, div_one, pow_one, Fintype.sum_unique]
    simp
  | succ t ih =>
    intro f hf
    set N : ℝ := (Fintype.card G : ℝ) with hNdef
    set H : (Fin t → G) × (Fin t → G) → G → ℝ :=
      fun p a => ∏ ω : Fin t → Bool, f (Fin.cons a (boxPt p.1 p.2 ω)) with hH
    set Z : (Fin t → G) × (Fin t → G) → ℝ := fun p => ∑ a, H p a with hZ
    set S : G → ℝ := fun a => ∑ y : Fin t → G, f (Fin.cons a y) with hS
    have hH0 : ∀ p a, 0 ≤ H p a := fun p a => prod_nonneg fun ω _ => hf _
    have hZ0 : ∀ p, 0 ≤ Z p := fun p => sum_nonneg fun a _ => hH0 p a
    have hS0 : ∀ a, 0 ≤ S a := fun a => sum_nonneg fun y _ => hf _
    -- the total of `f`, split by the first coordinate
    have hsumf : ∑ x, f x = ∑ a, S a := by
      rw [← (Fin.consEquiv fun _ : Fin (t + 1) => G).sum_comp, Fintype.sum_prod_type]
      rfl
    -- the sum of `Z` is a sum of box sums, one for each first coordinate
    have hsumZ : ∑ p, Z p = ∑ a, boxSum fun y => f (Fin.cons a y) := by
      simp only [hZ, hH, boxSum]
      rw [sum_comm]
    -- the induction hypothesis and Jensen's inequality
    have hK : 2 ^ t = (2 ^ t - 1) + 1 := (Nat.succ_pred_eq_of_pos (by positivity)).symm
    have hjensen : N * ((∑ a, S a / N ^ t) / N) ^ 2 ^ t ≤ ∑ a, (S a / N ^ t) ^ 2 ^ t := by
      have h := pow_sum_div_card_le_sum_pow (s := univ) (f := fun a => S a / N ^ t)
        (fun a _ => div_nonneg (hS0 a) (by positivity)) (2 ^ t - 1)
      rw [← hK, card_univ, ← hNdef] at h
      have hNK : N ^ 2 ^ t = N ^ (2 ^ t - 1) * N := by rw [← pow_succ, ← hK]
      calc N * ((∑ a, S a / N ^ t) / N) ^ 2 ^ t
          = (∑ a, S a / N ^ t) ^ 2 ^ t / N ^ (2 ^ t - 1) := by
            rw [div_pow, hNK]
            field_simp
        _ ≤ _ := h
    have hlow : N ^ (2 * t) * (N * ((∑ x, f x) / N ^ (t + 1)) ^ 2 ^ t) ≤ ∑ p, Z p := by
      rw [hsumZ]
      have hmean : (∑ x, f x) / N ^ (t + 1) = (∑ a, S a / N ^ t) / N := by
        rw [hsumf, ← sum_div, div_div, pow_succ]
      rw [hmean]
      calc N ^ (2 * t) * (N * ((∑ a, S a / N ^ t) / N) ^ 2 ^ t)
          ≤ N ^ (2 * t) * ∑ a, (S a / N ^ t) ^ 2 ^ t :=
            mul_le_mul_of_nonneg_left hjensen (by positivity)
        _ = ∑ a, N ^ (2 * t) * (S a / N ^ t) ^ 2 ^ t := by rw [mul_sum]
        _ ≤ ∑ a, boxSum fun y => f (Fin.cons a y) :=
            sum_le_sum fun a _ => ih _ fun y => hf _
    -- Cauchy–Schwarz over the pairs `(y, y')`
    have hcs : (∑ p, Z p) ^ 2 ≤ N ^ (2 * t) * ∑ p, Z p ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := univ) (f := Z)
      rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at h
      convert h using 2
      push_cast
      ring
    rw [boxSum_succ]
    have hA : 0 ≤ N ^ (2 * t) * (N * ((∑ x, f x) / N ^ (t + 1)) ^ 2 ^ t) := by
      have : 0 ≤ ∑ x, f x := sum_nonneg fun x _ => hf x
      positivity
    have hsq := pow_le_pow_left₀ hA hlow 2
    have hpos : 0 < N ^ (2 * t) := by positivity
    rw [← mul_le_mul_iff_of_pos_left hpos]
    calc N ^ (2 * t) * (N ^ (2 * (t + 1)) * ((∑ x, f x) / N ^ (t + 1)) ^ 2 ^ (t + 1))
        = (N ^ (2 * t) * (N * ((∑ x, f x) / N ^ (t + 1)) ^ 2 ^ t)) ^ 2 := by ring
      _ ≤ (∑ p, Z p) ^ 2 := hsq
      _ ≤ N ^ (2 * t) * ∑ p, Z p ^ 2 := hcs

/-- **Monochromatic boxes.** For every `g : G^t → κ` with `k` colours, at least
`N^{2t} / k^{2^t - 1}` pairs `(x, x')` have a box on which `g` is constant. -/
theorem card_mono_boxes {κ : Type*} [Fintype κ] [DecidableEq κ] (t : ℕ)
    (g : (Fin t → G) → κ) :
    (Fintype.card G : ℝ) ^ (2 * t) ≤ (Fintype.card κ : ℝ) ^ (2 ^ t - 1) *
      (#(univ.filter fun p : (Fin t → G) × (Fin t → G) =>
        ∀ ω, g (boxPt p.1 p.2 ω) = g p.1) : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have : Nonempty κ := ⟨g fun _ => Classical.arbitrary G⟩
  have hk : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card G : ℝ) with hNdef
  set k : ℝ := (Fintype.card κ : ℝ) with hkdef
  set u : κ → (Fin t → G) → ℝ := fun c x => if g x = c then 1 else 0 with hu
  have hu0 : ∀ c x, 0 ≤ u c x := fun c x => by simp only [hu]; split_ifs <;> norm_num
  -- the box sums of the colour classes count the pairs whose box has that colour
  have hpt : ∀ p : (Fin t → G) × (Fin t → G),
      ∑ c, (∏ ω, u c (boxPt p.1 p.2 ω)) ≤
        if (∀ ω, g (boxPt p.1 p.2 ω) = g p.1) then (1 : ℝ) else 0 := by
    intro p
    simp only [hu, Fintype.prod_boole]
    by_cases hm : ∀ ω, g (boxPt p.1 p.2 ω) = g p.1
    · rw [ite_eq_left hm, Finset.sum_boole]
      have hsub : (univ.filter fun c => ∀ ω, g (boxPt p.1 p.2 ω) = c) ⊆ {g p.1} := by
        intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        have h0 := hc fun _ => false
        rw [boxPt_false] at h0
        simp [h0]
      have := card_le_card hsub
      rw [card_singleton] at this
      exact_mod_cast this
    · rw [ite_eq_right hm]
      refine le_of_eq (sum_eq_zero fun c _ => ite_eq_right fun hc => hm fun ω => ?_)
      rw [hc ω, ← hc fun _ => false, boxPt_false]
  have hbox : ∑ c, boxSum (u c) ≤ (#(univ.filter fun p : (Fin t → G) × (Fin t → G) =>
      ∀ ω, g (boxPt p.1 p.2 ω) = g p.1) : ℝ) := by
    rw [card_filter, Nat.cast_sum]
    simp only [boxSum]
    rw [sum_comm]
    refine sum_le_sum fun p _ => (hpt p).trans ?_
    split_ifs <;> simp
  -- the densities of the colour classes sum to one
  set μ : κ → ℝ := fun c => (∑ x, u c x) / N ^ t with hμ
  have hμ0 : ∀ c, 0 ≤ μ c := fun c => div_nonneg (sum_nonneg fun x _ => hu0 c x) (by positivity)
  have hμ1 : ∑ c, μ c = 1 := by
    have h1 : ∑ c, ∑ x, u c x = N ^ t := by
      rw [sum_comm]
      simp only [hu, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, hNdef]
    rw [hμ, ← sum_div, h1, div_self (by positivity)]
  -- the power mean inequality `∑ μ_c^K ≥ k^{1-K}`
  have hK : 2 ^ t = (2 ^ t - 1) + 1 := (Nat.succ_pred_eq_of_pos (by positivity)).symm
  have hpm : 1 ≤ k ^ (2 ^ t - 1) * ∑ c, μ c ^ 2 ^ t := by
    have h := pow_sum_div_card_le_sum_pow (s := univ) (f := μ) (fun c _ => hμ0 c) (2 ^ t - 1)
    rw [← hK, hμ1, one_pow, card_univ, ← hkdef] at h
    have hkK : (0 : ℝ) < k ^ (2 ^ t - 1) := by positivity
    rw [div_le_iff₀ hkK] at h
    linarith
  calc N ^ (2 * t) ≤ N ^ (2 * t) * (k ^ (2 ^ t - 1) * ∑ c, μ c ^ 2 ^ t) :=
        le_mul_of_one_le_right (by positivity) hpm
    _ = k ^ (2 ^ t - 1) * ∑ c, N ^ (2 * t) * μ c ^ 2 ^ t := by
        rw [← mul_assoc, mul_comm (N ^ (2 * t)), mul_assoc, mul_sum]
    _ ≤ k ^ (2 ^ t - 1) * ∑ c, boxSum (u c) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun c _ => box_ineq t (u c) (hu0 c)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hbox (by positivity)

lemma card_fiber (t : ℕ) (ht : 1 ≤ t) (i : Fin t) (c : G) :
    #(univ.filter fun x' : Fin t → G => c = x' i) = Fintype.card G ^ (t - 1) := by
  have hs : (univ.filter fun x' : Fin t → G => c = x' i) =
      Fintype.piFinset fun k => if k = i then ({c} : Finset G) else univ := by
    ext x'
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h k
      by_cases hk : k = i
      · subst hk; simp [h]
      · simp [hk]
    · intro h
      have := h i
      simp only [ite_true, mem_singleton] at this
      exact this.symm
  rw [hs, Fintype.card_piFinset]
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Fin.prod_univ_succAbove _ i]
  simp [Fin.succAbove_ne]

/-- Pairs agreeing in some coordinate are few. -/
lemma card_degenerate (t : ℕ) (ht : 1 ≤ t) :
    #(univ.filter fun p : (Fin t → G) × (Fin t → G) => ∃ i, p.1 i = p.2 i) ≤
      t * Fintype.card G ^ (2 * t - 1) := by
  set N := Fintype.card G
  have hi : ∀ i : Fin t,
      #(univ.filter fun p : (Fin t → G) × (Fin t → G) => p.1 i = p.2 i) = N ^ (2 * t - 1) := by
    intro i
    rw [card_filter, Fintype.sum_prod_type]
    simp_rw [← card_filter, card_fiber t ht i]
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul, ← pow_add]
    congr 1
    omega
  have hU : (univ.filter fun p : (Fin t → G) × (Fin t → G) => ∃ i, p.1 i = p.2 i) =
      (univ : Finset (Fin t)).biUnion fun i => univ.filter fun p => p.1 i = p.2 i := by
    ext p
    simp
  rw [hU]
  calc _ ≤ ∑ i : Fin t, #(univ.filter fun p : (Fin t → G) × (Fin t → G) => p.1 i = p.2 i) :=
        card_biUnion_le
    _ = t * N ^ (2 * t - 1) := by simp [hi]

end BoxIneq

/-! ### Supersaturation -/

section Supersat

/-- The length `L = t k^{2^t}` of each of the `t` chains, for `k` colours. -/
def boxL (k t : ℕ) : ℕ := t * k ^ 2 ^ t

/-- The window `M = t L = t^2 k^{2^t}`. -/
def boxM (k t : ℕ) : ℕ := t * boxL k t

/-- Position `q` of the window is point `k` of chain `i`. -/
def boxPos (k t : ℕ) : Fin (boxM k t) ≃ Fin t × Fin (boxL k t) := finProdFinEquiv.symm

/-- The positions removed from the top at the grid point `x`: point `k` of chain `i` is
removed when `k ≥ x i`, so that the set kept on chain `i` is its first `x i` points. -/
def boxW (k t : ℕ) (x : Fin t → Fin (boxL k t + 1)) : Fin (boxM k t) → Bool :=
  fun q => decide ((x (boxPos k t q).1).val ≤ ((boxPos k t q).2).val)

/-- The cube pattern of the box with corners `lo ≤ hi`: on chain `i`, points below `lo i` form
part of the base, points from `lo i` to `hi i` form generator `i`, and the rest are unused. -/
def boxPat (k t : ℕ) (lo hi : Fin t → Fin (boxL k t + 1)) : Fin (boxM k t) → Bool ⊕ Fin t :=
  fun q => if ((boxPos k t q).2).val < (lo (boxPos k t q).1).val then Sum.inl false
    else if ((boxPos k t q).2).val < (hi (boxPos k t q).1).val then Sum.inr (boxPos k t q).1
    else Sum.inl true

lemma boxPat_elim (k t : ℕ) (lo hi : Fin t → Fin (boxL k t + 1)) (hlh : ∀ i, lo i ≤ hi i)
    (y : Fin t → Bool) :
    (fun q => (boxPat k t lo hi q).elim id y) = boxW k t fun i => if y i then lo i else hi i := by
  funext q
  have h := hlh (boxPos k t q).1
  rw [Fin.le_def] at h
  simp only [boxPat, boxW]
  by_cases hy : y (boxPos k t q).1 = true <;>
    by_cases h1 : ((boxPos k t q).2).val < (lo (boxPos k t q).1).val <;>
    by_cases h2 : ((boxPos k t q).2).val < (hi (boxPos k t q).1).val <;>
    simp [h1, h2, hy] <;> omega

lemma boxPat_proper (k t : ℕ) (lo hi : Fin t → Fin (boxL k t + 1)) (hlh : ∀ i, lo i < hi i)
    (i : Fin t) : ∃ q, boxPat k t lo hi q = Sum.inr i := by
  have h := hlh i
  rw [Fin.lt_def] at h
  have hk : (lo i).val < boxL k t := by have := (hi i).isLt; omega
  refine ⟨(boxPos k t).symm (i, ⟨(lo i).val, hk⟩), ?_⟩
  simp only [boxPat, Equiv.apply_symm_apply, lt_irrefl, ite_false, h, ite_true]

lemma ite_minmax {α : Type*} [LinearOrder α] (a b c : α) (hc : c = a ∨ c = b) :
    (if c = min a b then min a b else max a b) = c := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
    split_ifs with h'
    · exact h'.symm
    · exact (hc.resolve_left h').symm
  · rw [min_eq_right h, max_eq_left h]
    split_ifs with h'
    · exact h'.symm
    · exact (hc.resolve_right h').symm

lemma ite_snd {α : Type*} [DecidableEq α] (a b c : α) (hc : c = a ∨ c = b) :
    (if c = b then b else a) = c := by
  split_ifs with h
  · exact h.symm
  · exact (hc.resolve_right h).symm

lemma boxPt_mem {G : Type*} {t : ℕ} (x x' : Fin t → G) (ω : Fin t → Bool) (i : Fin t) :
    boxPt x x' ω i = x i ∨ boxPt x x' ω i = x' i := by
  simp only [boxPt]
  split_ifs <;> simp

variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The colour of the grid point `x`, for the ordering `σ`. -/
def boxCol (k t r : ℕ) (χ : Finset (Fin n) → κ) (σ : Equiv.Perm (Fin n))
    (x : Fin t → Fin (boxL k t + 1)) : κ :=
  pull χ σ (topMinus (boxM k t) r (boxW k t x))

/-- The pattern of the box spanned by a pair of grid points. -/
def pairPat (k t : ℕ) (p : (Fin t → Fin (boxL k t + 1)) × (Fin t → Fin (boxL k t + 1))) :
    Fin (boxM k t) → Bool ⊕ Fin t :=
  boxPat k t (fun i => min (p.1 i) (p.2 i)) (fun i => max (p.1 i) (p.2 i))

/-- A box is monochromatic exactly when the hole cube of its pattern is. -/
lemma mono_iff_cubeMono (k t r : ℕ) (χ : Finset (Fin n) → κ) (σ : Equiv.Perm (Fin n))
    (p : (Fin t → Fin (boxL k t + 1)) × (Fin t → Fin (boxL k t + 1))) :
    (∀ ω, boxCol k t r χ σ (boxPt p.1 p.2 ω) = boxCol k t r χ σ p.1) ↔
      CubeMono (pull χ σ) (patLab (n := n) (boxM k t) r (pairPat k t p)) := by
  set lo : Fin t → Fin (boxL k t + 1) := fun i => min (p.1 i) (p.2 i)
  set hi : Fin t → Fin (boxL k t + 1) := fun i => max (p.1 i) (p.2 i)
  set z : (Fin t → Bool) → Fin t → Fin (boxL k t + 1) := fun y i => if y i then lo i else hi i
  have hlh : ∀ i, lo i ≤ hi i := fun i => min_le_max
  have hcube : ∀ y, pull χ σ (cubeSet (patLab (n := n) (boxM k t) r (pairPat k t p)) y) =
      boxCol k t r χ σ (z y) := by
    intro y
    rw [cubeSet_patLab, pairPat, boxPat_elim k t lo hi hlh y]
    rfl
  -- every vertex of the box is some `z y`, and conversely
  have hvert : ∀ ω, ∃ y, boxPt p.1 p.2 ω = z y := by
    intro ω
    refine ⟨fun i => decide (boxPt p.1 p.2 ω i = lo i), ?_⟩
    funext i
    simp only [z, decide_eq_true_eq]
    exact (ite_minmax _ _ _ (boxPt_mem p.1 p.2 ω i)).symm
  have hz : ∀ y, ∃ ω, z y = boxPt p.1 p.2 ω := by
    intro y
    refine ⟨fun i => decide (z y i = p.2 i), ?_⟩
    funext i
    simp only [boxPt, decide_eq_true_eq]
    refine (ite_snd _ _ _ ?_).symm
    simp only [z]
    split_ifs
    · exact min_choice _ _
    · exact max_choice _ _
  constructor
  · intro h y
    rw [hcube, hcube]
    obtain ⟨ω, hω⟩ := hz y
    obtain ⟨ω', hω'⟩ := hz fun _ => false
    rw [hω, hω', h ω, h ω']
  · intro h ω
    obtain ⟨y, hy⟩ := hvert ω
    obtain ⟨y', hy'⟩ := hvert fun _ => false
    rw [boxPt_false] at hy'
    rw [hy, hy', ← hcube, ← hcube, h y, h y']

/-- **Supersaturation.** For every colouring with `k ≥ 2` colours and every `r`, some proper
pattern on the window `Fin (boxM k t)` makes its hole cube monochromatic for at least a
`k^{-2^t}` fraction of the orderings. -/
theorem exists_good_pattern (hk : 2 ≤ Fintype.card κ) (t : ℕ) (ht : 1 ≤ t) (r : ℕ)
    (χ : Finset (Fin n) → κ) :
    ∃ π : Fin (boxM (Fintype.card κ) t) → Bool ⊕ Fin t, (∀ i, ∃ q, π q = Sum.inr i) ∧
      Fintype.card (Equiv.Perm (Fin n)) ≤
        Fintype.card κ ^ 2 ^ t * Ncount χ (patLab (n := n) (boxM (Fintype.card κ) t) r π) := by
  set k := Fintype.card κ with hkdef
  set K := k ^ 2 ^ t with hK
  set a := k ^ (2 ^ t - 1) with ha
  have hKa : K = a * k := by
    rw [hK, ha, ← pow_succ]
    congr 1
    have : 0 < 2 ^ t := by positivity
    omega
  set N := boxL k t + 1 with hN
  set D := (univ : Finset ((Fin t → Fin N) × (Fin t → Fin N))).filter
    fun p => ∀ i, p.1 i ≠ p.2 i with hD
  set cnt : (Fin t → Fin N) × (Fin t → Fin N) → ℕ :=
    fun p => Ncount χ (patLab (n := n) (boxM k t) r (pairPat k t p)) with hcnt
  -- for each ordering, many pairs of `D` give a monochromatic cube
  have hσ : ∀ σ : Equiv.Perm (Fin n), N ^ (2 * t) ≤ K *
      #(D.filter fun p => CubeMono (pull χ σ) (patLab (n := n) (boxM k t) r (pairPat k t p))) := by
    intro σ
    set mono := #(univ.filter fun p : (Fin t → Fin N) × (Fin t → Fin N) =>
        ∀ ω, boxCol k t r χ σ (boxPt p.1 p.2 ω) = boxCol k t r χ σ p.1) with hmono
    set good := #(D.filter fun p =>
      CubeMono (pull χ σ) (patLab (n := n) (boxM k t) r (pairPat k t p))) with hgood
    set deg := #(univ.filter fun p : (Fin t → Fin N) × (Fin t → Fin N) => ∃ i, p.1 i = p.2 i)
      with hdeg
    have h1 : N ^ (2 * t) ≤ a * mono := by
      have h := card_mono_boxes t (boxCol k t r χ σ)
      simp only [Fintype.card_fin] at h
      exact_mod_cast h
    have h2 : mono ≤ good + deg := by
      refine (card_le_card ?_).trans (card_union_le _ _)
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [mem_union, hD, mem_filter, mem_univ, true_and]
      by_cases hdg : ∃ i, p.1 i = p.2 i
      · exact Or.inr hdg
      · push Not at hdg
        exact Or.inl ⟨hdg, (mono_iff_cubeMono k t r χ σ p).1 hp⟩
    have h3 : deg ≤ t * N ^ (2 * t - 1) := by
      have h := card_degenerate (G := Fin N) t ht
      rw [Fintype.card_fin] at h
      convert h using 2
      ext p
      simp
    -- `(k - 1) N ≥ t K`, so the degenerate pairs cost at most a factor `1 - 1/k`
    have h4 : K * (t * N ^ (2 * t - 1)) + N ^ (2 * t) ≤ k * N ^ (2 * t) := by
      have hpow : N ^ (2 * t) = N * N ^ (2 * t - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hKt : K * t + N ≤ k * N := by
        have hN' : N = t * K + 1 := by rw [hN, boxL, hK]
        rw [hN']
        nlinarith
      rw [hpow]
      nlinarith
    have h5 : k * N ^ (2 * t) ≤ K * good + K * deg := by
      calc k * N ^ (2 * t) ≤ k * (a * mono) := Nat.mul_le_mul_left _ h1
        _ ≤ k * (a * (good + deg)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
        _ = K * good + K * deg := by rw [hKa]; ring
    have h6 : K * deg ≤ K * (t * N ^ (2 * t - 1)) := Nat.mul_le_mul_left _ h3
    omega
  -- summing over the orderings
  have hsum : ∑ σ : Equiv.Perm (Fin n),
      #(D.filter fun p => CubeMono (pull χ σ) (patLab (n := n) (boxM k t) r (pairPat k t p))) =
        ∑ p ∈ D, cnt p := by
    simp only [card_filter, hcnt, Ncount]
    exact sum_comm
  have htot : Fintype.card (Equiv.Perm (Fin n)) * N ^ (2 * t) ≤ K * ∑ p ∈ D, cnt p := by
    rw [← hsum, mul_sum]
    calc Fintype.card (Equiv.Perm (Fin n)) * N ^ (2 * t)
        = ∑ _σ : Equiv.Perm (Fin n), N ^ (2 * t) := by rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ _ := sum_le_sum fun σ _ => hσ σ
  have hpos : 0 < Fintype.card (Equiv.Perm (Fin n)) * N ^ (2 * t) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    positivity
  have hDne : D.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, sum_empty, mul_zero] at htot
    omega
  obtain ⟨p₀, hp₀, hmax⟩ := exists_max_image D cnt hDne
  have hDcard : #D ≤ N ^ (2 * t) := by
    calc #D ≤ #(univ : Finset ((Fin t → Fin N) × (Fin t → Fin N))) :=
          card_le_card (filter_subset _ _)
      _ = N ^ (2 * t) := by
          rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, ← pow_add]
          congr 1
          omega
  refine ⟨pairPat k t p₀, ?_, ?_⟩
  · have hp := (mem_filter.1 hp₀).2
    exact boxPat_proper k t _ _ fun i => min_lt_max.2 (hp i)
  · have key : Fintype.card (Equiv.Perm (Fin n)) * N ^ (2 * t) ≤ (K * cnt p₀) * N ^ (2 * t) := by
      calc Fintype.card (Equiv.Perm (Fin n)) * N ^ (2 * t) ≤ K * ∑ p ∈ D, cnt p := htot
        _ ≤ K * ∑ _p ∈ D, cnt p₀ := Nat.mul_le_mul_left _ (sum_le_sum hmax)
        _ = K * (#D * cnt p₀) := by rw [sum_const, smul_eq_mul]
        _ ≤ K * (N ^ (2 * t) * cnt p₀) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDcard)
        _ = (K * cnt p₀) * N ^ (2 * t) := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- The two-colour case: a `2^{-2^t}` fraction of the orderings, with `M = t^2 2^{2^t}`. -/
theorem exists_good_pattern_two (t : ℕ) (ht : 1 ≤ t) (r : ℕ) (χ : Colouring n) :
    ∃ π : Fin (boxM 2 t) → Bool ⊕ Fin t, (∀ i, ∃ q, π q = Sum.inr i) ∧
      Fintype.card (Equiv.Perm (Fin n)) ≤
        2 ^ 2 ^ t * Ncount χ (patLab (n := n) (boxM 2 t) r π) := by
  have h := exists_good_pattern (κ := Bool) (by simp) t ht r χ
  simp only [Fintype.card_bool] at h
  exact h

end Supersat

end Erdos1183
