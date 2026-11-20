module

public import NearlyMinimax.DyadicFit


@[expose] public section

/-! A common actual Taylor polynomial across all dyadic levels. -/

noncomputable section
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

section
variable {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) (x w z : Covariate d)

def dyadicTaylorCoefficients :
    AnchoredIndex d ℓ → ℝ := (anchoredTransport d ℓ) ^ j *ᵥ c

theorem dyadicTaylorCoefficients_succ :
    dyadicTaylorCoefficients c (j + 1) = anchoredTransport d ℓ *ᵥ dyadicTaylorCoefficients c j := by
  rw [dyadicTaylorCoefficients, pow_succ', ← Matrix.mulVec_mulVec]
  rfl

theorem dyadicTaylorCoefficients_evaluation :
    dyadicAnchoredFeature j x z ⬝ᵥ dyadicTaylorCoefficients c j = anchoredFitPolynomial x c z := by
  induction j with
  | zero =>
    simp [dyadicTaylorCoefficients, dyadicAnchoredFeature, anchoredFeature, anchoredFitPolynomial, dotProduct]
    apply Finset.sum_congr rfl
    intro γ _
    rw [show (fun i => z i - x i) = z - x by rfl]
    ring
  | succ j ih =>
    rw [dyadicTaylorCoefficients_succ, dyadicAnchoredFeature_transport_dot, ih]

theorem dyadicTaylorCoefficients_normalized_evaluation :
    anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
      anchoredFitPolynomial x c (dyadicCellAffine j x w) := by
  have he := dyadicTaylorCoefficients_evaluation c j x (dyadicCellAffine j x w)
  have hφ : dyadicAnchoredFeature (ℓ := ℓ) j x (dyadicCellAffine j x w) =
      anchoredFeature (dyadicNormalizedAnchor j x) w := by
    funext γ
    exact dyadicAnchoredFeature_affine ..
  rw [hφ] at he
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro γ _
      ring
    _ = _ := he

theorem euclideanNorm_smul (a : ℝ) (v : Covariate d) :
    euclideanNorm (a • v) = |a| * euclideanNorm v := by
  unfold euclideanNorm
  simp [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem dyadicCellAffine_euclidean_distance :
    euclideanNorm (dyadicCellAffine j x w - x) =
      (2 ^ j)⁻¹ * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
  rw [dyadicCellAffine_difference, euclideanNorm_smul, abs_of_nonneg (by positivity)]

end

/-- One actual Taylor polynomial generates a coherent coefficient family at
every level and a genuine residual bound, uniformly in the original model. -/
theorem admissible_dyadic_taylor_family {d : ℕ} {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ) {x : Covariate d}
    (hx : x ∈ unitCube d) :
    ∃ c : AnchoredIndex d C.order → ℝ, ∀ j, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          taylorErrorFactor C * C.holderBound * ((2 ^ j)⁻¹) ^ C.smoothness ∧
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          (d ^ C.order * (2 * C.holderBound) / C.order.factorial) *
            ((2 ^ j)⁻¹) ^ C.smoothness *
              euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness := by
  obtain ⟨P, hP, herr⟩ := admissible_regression_taylor hθ hx
  have hxP : eval x P = θ.regression x := by
    have h := herr x hx
    simp [euclideanNorm, Real.zero_rpow C.smoothness_pos.ne'] at h
    exact (sub_eq_zero.mp h).symm
  have hP0 : (P - MvPolynomial.C (θ.regression x)).totalDegree ≤ C.order :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le hP (by simp))
  obtain ⟨c, hc⟩ := polynomial_centered_representation hP0 (by
    rw [map_sub, eval_C, hxP, sub_self])
  refine ⟨c, ?_⟩
  intro j w hw
  have heq : dyadicRegressionDifference θ j x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
        θ.regression (dyadicCellAffine j x w) - eval (dyadicCellAffine j x w) P := by
    rw [dyadicTaylorCoefficients_normalized_evaluation,
      show anchoredFitPolynomial x c (dyadicCellAffine j x w) =
        eval (dyadicCellAffine j x w) (P - MvPolynomial.C (θ.regression x)) from (hc _).symm,
      map_sub, eval_C]
    unfold dyadicRegressionDifference
    ring
  rw [heq]
  have hy := dyadicCellAffine_mem_cube j x w hw
  have hcoef : 0 ≤ d ^ C.order * (2 * C.holderBound) / C.order.factorial :=
    div_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  constructor
  · apply (herr _ hy).trans
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by unfold euclideanNorm; positivity) (euclideanNorm_le_coordinate_radius (by positivity) (dyadicCellAffine_radius j hx hw)) C.smoothness_pos.le) hcoef).trans_eq
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)]
    unfold taylorErrorFactor
    ring
  · convert herr _ hy using 1
    rw [dyadicCellAffine_euclidean_distance, Real.mul_rpow (by positivity)
      (by unfold euclideanNorm; positivity)]
    ring

end NearlyMinimax
