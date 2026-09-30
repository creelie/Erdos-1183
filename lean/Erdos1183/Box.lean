import Erdos1183.Cube
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The box inequality and supersaturation

For `x x' : Fin t → G` and `ω : Fin t → Bool`, the point `boxPt x x' ω` takes the coordinate
`x' i` where `ω i = true` and `x i` elsewhere. The box inequality (`box_ineq`) says that for
`f ≥ 0`, the average over `x, x'` of `∏_ω f (boxPt x x' ω)` is at least `(E f)^(2^t)`.

Applied to the colouring `x ↦ χ (σ (S x ∪ R))` of a grid of `t` chains of length `L`, it shows
that a proportion `2^{-2^t}` of the orderings makes some fixed cube monochromatic
(`exists_good_pattern`), with `L = t 2^{2^t}`.
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

/-- **Monochromatic boxes.** For every `g : G^t → Bool`, at least `2 N^{2t} / 2^{2^t}` pairs
`(x, x')` have a box on which `g` is constant. -/
theorem card_mono_boxes (t : ℕ) (g : (Fin t → G) → Bool) :
    2 * (Fintype.card G : ℝ) ^ (2 * t) ≤ 2 ^ 2 ^ t *
      (#(univ.filter fun p : (Fin t → G) × (Fin t → G) =>
        ∀ ω, g (boxPt p.1 p.2 ω) = g p.1) : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card G : ℝ) with hNdef
  set u : (Fin t → G) → ℝ := fun x => if g x = true then 1 else 0 with hu
  set v : (Fin t → G) → ℝ := fun x => if g x = false then 1 else 0 with hv
  have hu0 : ∀ x, 0 ≤ u x := fun x => by simp only [hu]; split_ifs <;> norm_num
  have hv0 : ∀ x, 0 ≤ v x := fun x => by simp only [hv]; split_ifs <;> norm_num
  have huv : ∀ x, u x + v x = 1 := fun x => by
    simp only [hu, hv]; cases g x <;> norm_num
  -- the two box sums count the pairs whose box is all `true`, respectively all `false`
  have hpt : ∀ p : (Fin t → G) × (Fin t → G),
      (∏ ω, u (boxPt p.1 p.2 ω)) + (∏ ω, v (boxPt p.1 p.2 ω)) ≤
        if (∀ ω, g (boxPt p.1 p.2 ω) = g p.1) then (1 : ℝ) else 0 := by
    intro p
    simp only [hu, hv, Fintype.prod_boole]
    have hAC : (∀ ω, g (boxPt p.1 p.2 ω) = true) → ∀ ω, g (boxPt p.1 p.2 ω) = g p.1 :=
      fun h ω => by rw [h ω, ← boxPt_false p.1 p.2, h]
    have hBC : (∀ ω, g (boxPt p.1 p.2 ω) = false) → ∀ ω, g (boxPt p.1 p.2 ω) = g p.1 :=
      fun h ω => by rw [h ω, ← boxPt_false p.1 p.2, h]
    have hAB : ¬ ((∀ ω, g (boxPt p.1 p.2 ω) = true) ∧ ∀ ω, g (boxPt p.1 p.2 ω) = false) :=
      fun h => by
        have h1 := h.1 fun _ => false
        rw [h.2 fun _ => false] at h1
        exact Bool.false_ne_true h1
    by_cases hA : ∀ ω, g (boxPt p.1 p.2 ω) = true
    · have hB : ¬ ∀ ω, g (boxPt p.1 p.2 ω) = false := fun hB => hAB ⟨hA, hB⟩
      rw [ite_eq_left hA, ite_eq_right hB, ite_eq_left (hAC hA)]
      norm_num
    · by_cases hB : ∀ ω, g (boxPt p.1 p.2 ω) = false
      · rw [ite_eq_right hA, ite_eq_left hB, ite_eq_left (hBC hB)]
        norm_num
      · rw [ite_eq_right hA, ite_eq_right hB]
        split_ifs <;> norm_num
  have hbox : boxSum u + boxSum v ≤ (#(univ.filter fun p : (Fin t → G) × (Fin t → G) =>
      ∀ ω, g (boxPt p.1 p.2 ω) = g p.1) : ℝ) := by
    rw [card_filter, Nat.cast_sum, boxSum, boxSum, ← sum_add_distrib]
    refine sum_le_sum fun p _ => (hpt p).trans ?_
    split_ifs <;> simp
  set μ : ℝ := (∑ x, u x) / N ^ t with hμ
  have hμv : (∑ x, v x) / N ^ t = 1 - μ := by
    have : ∑ x, v x = N ^ t - ∑ x, u x := by
      have h := sum_add_distrib (s := (univ : Finset (Fin t → G))) (f := u) (g := v)
      simp only [huv, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
        mul_one, Nat.cast_pow] at h
      rw [← hNdef] at h
      linarith
    rw [this, hμ, sub_div, div_self (by positivity)]
  have hμ0 : 0 ≤ μ := div_nonneg (sum_nonneg fun x _ => hu0 x) (by positivity)
  have hμ1 : 0 ≤ 1 - μ := by
    rw [← hμv]; exact div_nonneg (sum_nonneg fun x _ => hv0 x) (by positivity)
  have hbu := box_ineq t u hu0
  have hbv := box_ineq t v hv0
  rw [← hNdef, ← hμ] at hbu
  rw [← hNdef, hμv] at hbv
  -- `μ^K + (1 - μ)^K ≥ 2^{1-K}` by convexity
  have hK : 2 ^ t = (2 ^ t - 1) + 1 := (Nat.succ_pred_eq_of_pos (by positivity)).symm
  have hconv : 2 ≤ 2 ^ 2 ^ t * (μ ^ 2 ^ t + (1 - μ) ^ 2 ^ t) := by
    have h := pow_sum_div_card_le_sum_pow (s := univ)
      (f := fun b : Bool => if b then μ else 1 - μ)
      (fun b _ => by cases b <;> simp [hμ0, hμ1]) (2 ^ t - 1)
    rw [← hK] at h
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, add_sub_cancel,
      one_pow, card_univ, Fintype.card_bool, Nat.cast_ofNat] at h
    have h2 : (0 : ℝ) < 2 ^ (2 ^ t - 1) := by positivity
    rw [div_le_iff₀ h2] at h
    have h3 : (2 : ℝ) ^ 2 ^ t = 2 * 2 ^ (2 ^ t - 1) := by
      rw [← pow_succ', ← hK]
    rw [h3]
    nlinarith
  have hNt : 0 < N ^ (2 * t) := by positivity
  calc 2 * N ^ (2 * t) ≤ N ^ (2 * t) * (2 ^ 2 ^ t * (μ ^ 2 ^ t + (1 - μ) ^ 2 ^ t)) := by
        nlinarith
    _ = 2 ^ 2 ^ t * (N ^ (2 * t) * μ ^ 2 ^ t + N ^ (2 * t) * (1 - μ) ^ 2 ^ t) := by ring
    _ ≤ 2 ^ 2 ^ t * (boxSum u + boxSum v) := by gcongr
    _ ≤ _ := by gcongr

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

/-- The length `L = t 2^{2^t}` of each of the `t` chains. -/
def boxL (t : ℕ) : ℕ := t * 2 ^ 2 ^ t

/-- The window `M = t L = t^2 2^{2^t}`. -/
def boxM (t : ℕ) : ℕ := t * boxL t

/-- Position `q` of the window is point `k` of chain `i`. -/
def boxPos (t : ℕ) : Fin (boxM t) ≃ Fin t × Fin (boxL t) := finProdFinEquiv.symm

/-- The positions removed from the top at the grid point `x`: point `k` of chain `i` is
removed when `k ≥ x i`, so that the set kept on chain `i` is its first `x i` points. -/
def boxW (t : ℕ) (x : Fin t → Fin (boxL t + 1)) : Fin (boxM t) → Bool :=
  fun q => decide ((x (boxPos t q).1).val ≤ ((boxPos t q).2).val)

/-- The cube pattern of the box with corners `lo ≤ hi`: on chain `i`, points below `lo i` form
part of the base, points from `lo i` to `hi i` form generator `i`, and the rest are unused. -/
def boxPat (t : ℕ) (lo hi : Fin t → Fin (boxL t + 1)) : Fin (boxM t) → Bool ⊕ Fin t :=
  fun q => if ((boxPos t q).2).val < (lo (boxPos t q).1).val then Sum.inl false
    else if ((boxPos t q).2).val < (hi (boxPos t q).1).val then Sum.inr (boxPos t q).1
    else Sum.inl true

lemma boxPat_elim (t : ℕ) (lo hi : Fin t → Fin (boxL t + 1)) (hlh : ∀ i, lo i ≤ hi i)
    (y : Fin t → Bool) :
    (fun q => (boxPat t lo hi q).elim id y) = boxW t fun i => if y i then lo i else hi i := by
  funext q
  have h := hlh (boxPos t q).1
  rw [Fin.le_def] at h
  simp only [boxPat, boxW]
  by_cases hy : y (boxPos t q).1 = true <;>
    by_cases h1 : ((boxPos t q).2).val < (lo (boxPos t q).1).val <;>
    by_cases h2 : ((boxPos t q).2).val < (hi (boxPos t q).1).val <;>
    simp [h1, h2, hy] <;> omega

lemma boxPat_proper (t : ℕ) (lo hi : Fin t → Fin (boxL t + 1)) (hlh : ∀ i, lo i < hi i)
    (i : Fin t) : ∃ q, boxPat t lo hi q = Sum.inr i := by
  have h := hlh i
  rw [Fin.lt_def] at h
  have hk : (lo i).val < boxL t := by have := (hi i).isLt; omega
  refine ⟨(boxPos t).symm (i, ⟨(lo i).val, hk⟩), ?_⟩
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

variable {n : ℕ}

/-- The colour of the grid point `x`, for the ordering `σ`. -/
def boxCol (t r : ℕ) (χ : Colouring n) (σ : Equiv.Perm (Fin n)) (x : Fin t → Fin (boxL t + 1)) :
    Bool :=
  pull χ σ (topMinus (boxM t) r (boxW t x))

/-- The pattern of the box spanned by a pair of grid points. -/
def pairPat (t : ℕ) (p : (Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1))) :
    Fin (boxM t) → Bool ⊕ Fin t :=
  boxPat t (fun i => min (p.1 i) (p.2 i)) (fun i => max (p.1 i) (p.2 i))

/-- A box is monochromatic exactly when the hole cube of its pattern is. -/
lemma mono_iff_cubeMono (t r : ℕ) (χ : Colouring n) (σ : Equiv.Perm (Fin n))
    (p : (Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1))) :
    (∀ ω, boxCol t r χ σ (boxPt p.1 p.2 ω) = boxCol t r χ σ p.1) ↔
      CubeMono (pull χ σ) (patLab (n := n) (boxM t) r (pairPat t p)) := by
  set lo : Fin t → Fin (boxL t + 1) := fun i => min (p.1 i) (p.2 i)
  set hi : Fin t → Fin (boxL t + 1) := fun i => max (p.1 i) (p.2 i)
  set z : (Fin t → Bool) → Fin t → Fin (boxL t + 1) := fun y i => if y i then lo i else hi i
  have hlh : ∀ i, lo i ≤ hi i := fun i => min_le_max
  have hcube : ∀ y, pull χ σ (cubeSet (patLab (n := n) (boxM t) r (pairPat t p)) y) =
      boxCol t r χ σ (z y) := by
    intro y
    rw [cubeSet_patLab, pairPat, boxPat_elim t lo hi hlh y]
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

/-- **Supersaturation.** For every colouring and every `r`, some proper pattern on the window
`Fin (boxM t)` makes its hole cube monochromatic for at least a `2^{-2^t}` fraction of the
orderings. -/
theorem exists_good_pattern (t : ℕ) (ht : 1 ≤ t) (r : ℕ) (χ : Colouring n) :
    ∃ π : Fin (boxM t) → Bool ⊕ Fin t, (∀ i, ∃ q, π q = Sum.inr i) ∧
      Fintype.card (Equiv.Perm (Fin n)) ≤
        2 ^ 2 ^ t * Ncount χ (patLab (n := n) (boxM t) r π) := by
  set K := 2 ^ 2 ^ t with hK
  set D := (univ : Finset ((Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1)))).filter
    fun p => ∀ i, p.1 i ≠ p.2 i with hD
  set cnt : (Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1)) → ℕ :=
    fun p => Ncount χ (patLab (n := n) (boxM t) r (pairPat t p)) with hcnt
  -- for each ordering, many pairs of `D` give a monochromatic cube
  have hσ : ∀ σ : Equiv.Perm (Fin n), (boxL t + 1) ^ (2 * t) ≤ K *
      #(D.filter fun p => CubeMono (pull χ σ) (patLab (n := n) (boxM t) r (pairPat t p))) := by
    intro σ
    have h1 := card_mono_boxes t (boxCol t r χ σ)
    simp only [Fintype.card_fin] at h1
    have h1' : 2 * (boxL t + 1) ^ (2 * t) ≤ K * #(univ.filter fun p : (Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1)) =>
        ∀ ω, boxCol t r χ σ (boxPt p.1 p.2 ω) = boxCol t r χ σ p.1) := by
      rw [hK]
      exact_mod_cast h1
    have h2 : #(univ.filter fun p : (Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1)) =>
        ∀ ω, boxCol t r χ σ (boxPt p.1 p.2 ω) = boxCol t r χ σ p.1) ≤
        #(D.filter fun p => CubeMono (pull χ σ) (patLab (n := n) (boxM t) r (pairPat t p))) +
          #(univ.filter fun p : (Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1)) => ∃ i, p.1 i = p.2 i) := by
      refine (card_le_card ?_).trans (card_union_le _ _)
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [mem_union, hD, mem_filter, mem_univ, true_and]
      by_cases hdeg : ∃ i, p.1 i = p.2 i
      · exact Or.inr hdeg
      · push Not at hdeg
        exact Or.inl ⟨hdeg, (mono_iff_cubeMono t r χ σ p).1 hp⟩
    have h3 : #(univ.filter fun p : (Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1)) =>
        ∃ i, p.1 i = p.2 i) ≤ t * (boxL t + 1) ^ (2 * t - 1) := by
      have h := card_degenerate (G := Fin (boxL t + 1)) t ht
      rw [Fintype.card_fin] at h
      convert h using 2
      ext p
      simp
    have h4 : K * (t * (boxL t + 1) ^ (2 * t - 1)) ≤ (boxL t + 1) ^ (2 * t) := by
      have hpow : (boxL t + 1) ^ (2 * t) = (boxL t + 1) * (boxL t + 1) ^ (2 * t - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hKt : K * t ≤ boxL t + 1 := by
        simp only [hK, boxL]
        rw [mul_comm]
        omega
      rw [hpow, ← mul_assoc]
      exact Nat.mul_le_mul_right _ hKt
    have h5 := Nat.mul_le_mul_left K h2
    have h6 := Nat.mul_le_mul_left K h3
    rw [mul_add] at h5
    omega
  -- summing over the orderings
  have hsum : ∑ σ : Equiv.Perm (Fin n),
      #(D.filter fun p => CubeMono (pull χ σ) (patLab (n := n) (boxM t) r (pairPat t p))) =
        ∑ p ∈ D, cnt p := by
    simp only [card_filter, hcnt, Ncount]
    exact sum_comm
  have htot : Fintype.card (Equiv.Perm (Fin n)) * (boxL t + 1) ^ (2 * t) ≤ K * ∑ p ∈ D, cnt p := by
    rw [← hsum, mul_sum]
    calc Fintype.card (Equiv.Perm (Fin n)) * (boxL t + 1) ^ (2 * t)
        = ∑ _σ : Equiv.Perm (Fin n), (boxL t + 1) ^ (2 * t) := by rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ _ := sum_le_sum fun σ _ => hσ σ
  have hpos : 0 < Fintype.card (Equiv.Perm (Fin n)) * (boxL t + 1) ^ (2 * t) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    positivity
  have hDne : D.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, sum_empty, mul_zero] at htot
    omega
  obtain ⟨p₀, hp₀, hmax⟩ := exists_max_image D cnt hDne
  have hDcard : #D ≤ (boxL t + 1) ^ (2 * t) := by
    calc #D ≤ #(univ : Finset ((Fin t → Fin (boxL t + 1)) × (Fin t → Fin (boxL t + 1)))) :=
          card_le_card (filter_subset _ _)
      _ = (boxL t + 1) ^ (2 * t) := by
          rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, ← pow_add]
          congr 1
          omega
  refine ⟨pairPat t p₀, ?_, ?_⟩
  · have hp := (mem_filter.1 hp₀).2
    exact boxPat_proper t _ _ fun i => min_lt_max.2 (hp i)
  · have key : Fintype.card (Equiv.Perm (Fin n)) * (boxL t + 1) ^ (2 * t) ≤ (K * cnt p₀) * (boxL t + 1) ^ (2 * t) := by
      calc Fintype.card (Equiv.Perm (Fin n)) * (boxL t + 1) ^ (2 * t) ≤ K * ∑ p ∈ D, cnt p := htot
        _ ≤ K * ∑ _p ∈ D, cnt p₀ := Nat.mul_le_mul_left _ (sum_le_sum hmax)
        _ = K * (#D * cnt p₀) := by rw [sum_const, smul_eq_mul]
        _ ≤ K * ((boxL t + 1) ^ (2 * t) * cnt p₀) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDcard)
        _ = (K * cnt p₀) * (boxL t + 1) ^ (2 * t) := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)

end Supersat

end Erdos1183
