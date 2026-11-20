module

public import NearlyMinimax.FiniteBounds

public import NearlyMinimax.HighSmoothnessWindows
public import NearlyMinimax.CoordinatePartialBridge
public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.AnchoredGeometry

@[expose] public section

/-! Resolution-independent derivative and Hölder estimates for actual
periodic window fields. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem finite_sum_norm_le_active_count {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] (g : J → E) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j, ‖g j‖ ≤ B)
    (hcount : (Finset.univ.filter (fun j => g j ≠ 0)).card ≤ N) :
    ‖∑ j, g j‖ ≤ (N : ℝ) * B := by
  apply (norm_sum_le_support_card_mul (s := Finset.univ.filter (fun j => g j ≠ 0))
    (fun j hj => by simpa using hj) (fun j _ => hbound j)).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB

section
variable {d : ℕ}

theorem multiIndexBasis_norm (γ : Fin d → ℕ) (j : Fin (∑ r, γ r)) :
    ‖multiIndexBasis γ j‖ = 1 := by
  simp [multiIndexBasis, wordBasis, Pi.norm_single]

section
variable (F : Covariate d → ℝ)
    (hF : ContDiff ℝ ∞ F) (γ : Fin d → ℕ)
include hF

theorem multiPartial_norm_le_iterated (x : Covariate d) :
    |multiPartial F γ x| ≤ ‖iteratedFDeriv ℝ (∑ r, γ r) F x‖ := by
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x)]
  have hh := (iteratedFDeriv ℝ (∑ r, γ r) F x).le_opNorm (multiIndexBasis γ)
  simpa only [Real.norm_eq_abs, multiIndexBasis_norm, Finset.prod_const_one, mul_one] using hh

theorem multiPartial_diff_norm_le_iterated (x y : Covariate d) :
    |multiPartial F γ x - multiPartial F γ y| ≤
      ‖iteratedFDeriv ℝ (∑ r, γ r) F x - iteratedFDeriv ℝ (∑ r, γ r) F y‖ := by
  rw [multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl x (mem_univ x),
    multiPartial_eq_iteratedFDeriv univ isOpen_univ F (∑ r, γ r)
    (hF.of_le (by simp)).contDiffOn γ le_rfl y (mem_univ y)]
  have hh := (iteratedFDeriv ℝ (∑ r, γ r) F x -
    iteratedFDeriv ℝ (∑ r, γ r) F y).le_opNorm (multiIndexBasis γ)
  simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs, multiIndexBasis_norm,
    Finset.prod_const_one, mul_one] using hh

end

theorem covariate_norm_le_euclidean (x : Covariate d) : ‖x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro r
  simpa only [Real.norm_eq_abs, euclideanNorm] using abs_coordinate_le_euclideanNorm x r

/-- The actual scaled Fréchet bounds imply the manuscript's sorted mixed
partial bounds and top-order Euclidean Hölder modulus. -/
theorem mixed_bounds_of_scaled_derivatives (C : ModelConstants d)
    (F : Covariate d → ℝ) (hF : ContDiff ℝ ∞ F) (k A : ℝ)
    (hk : 1 ≤ k) (hA : 0 ≤ A)
    (hbound : ∀ q ≤ C.order + 1, ∀ x,
      ‖iteratedFDeriv ℝ q F x‖ ≤ A * k ^ ((q : ℝ) - C.smoothness)) :
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
      |multiPartial F (fun r => (γ r).val) x| ≤ A) ∧
    (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
      |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
        (2 * A) * euclideanNorm (x - y) ^ C.alpha) := by
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  constructor
  · intro γ hγ x
    apply (multiPartial_norm_le_iterated F hF _ x).trans
    apply (hbound _ (by omega) x).trans
    have hcast : ((∑ r, (γ r).val : ℕ) : ℝ) ≤ C.order := by gcongr
    have hp : k ^ (((∑ r, (γ r).val : ℕ) : ℝ) - C.smoothness) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith [C.order_lt])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hA
  · intro γ hγ x y
    have hsup (z : Covariate d) : ‖iteratedFDeriv ℝ C.order F z‖ ≤ A / k ^ C.alpha := by
      have he : (C.order : ℝ) - C.smoothness = -C.alpha := by unfold ModelConstants.alpha; ring
      simpa only [he, Real.rpow_neg hkpos.le, div_eq_mul_inv] using hbound C.order (by omega) z
    have hnext (z : Covariate d) : ‖fderiv ℝ (iteratedFDeriv ℝ C.order F) z‖ ≤ (2 * A) / k ^ C.alpha * k := by
      rw [norm_fderiv_iteratedFDeriv]
      have he : ((C.order + 1 : ℕ) : ℝ) - C.smoothness = -C.alpha + 1 := by
        unfold ModelConstants.alpha
        push_cast
        ring
      refine (hbound (C.order + 1) le_rfl z).trans ?_
      rw [he, Real.rpow_add hkpos, Real.rpow_one, Real.rpow_neg hkpos.le, div_eq_mul_inv]
      calc
        _ = (A * (k ^ C.alpha)⁻¹) * k := by ring
        _ ≤ _ := by gcongr; linarith
    have hlarge : ‖iteratedFDeriv ℝ C.order F x - iteratedFDeriv ℝ C.order F y‖ ≤
        (2 * A) / k ^ C.alpha :=
      (norm_sub_le _ _).trans (by rw [mul_div_assoc]; linarith only [hsup x, hsup y])
    have hfFinite : ContDiff ℝ (C.order + 1) F := hF.of_le (by simp)
    have hsmall := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_hz : z ∈ (univ : Set (Covariate d))) =>
        hfFinite.contDiffAt.differentiableAt_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self C.order))
      (fun z _ => hnext z) convex_univ (mem_univ y) (mem_univ x)
    have hh := le_rpow_of_scaled_uniform_and_linear hkpos (norm_nonneg _) (by positivity)
      C.alpha_pos.le C.alpha_le_one hlarge hsmall
    have heval := multiPartial_diff_norm_le_iterated F hF (fun r => (γ r).val) x y
    rw [hγ] at heval
    exact (heval.trans hh).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (covariate_norm_le_euclidean (x - y)) C.alpha_pos.le)
      (by positivity))

end

end NearlyMinimax
