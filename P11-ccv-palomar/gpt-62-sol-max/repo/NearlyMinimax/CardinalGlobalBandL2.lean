module

public import NearlyMinimax.CardinalProductDesign
public import NearlyMinimax.ExponentialSpatialKernels


@[expose] public section

/-! True full-product spatial L2 bounds for the actual interpolation bands. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

section
variable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T)
include hL hT hLT

theorem centeredCardinalBandMatrix_eq_difference
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    centeredCardinalBandMatrix i lam L T U β β' =
      (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T) -
      (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i L) := by
  exact setIntegral_sdiff (spatial_scale_domain_isClosed i L).measurableSet
    (spatial_centered_cardinal_matrix_integrable i lam T hT U β β')
    (spatial_scale_domain_mono i (lt_of_lt_of_le (by norm_num) hL) hLT)

theorem centeredCardinalBandMatrix_continuous (β β' : HighFrameIndex d D) :
    Continuous (fun U => centeredCardinalBandMatrix i lam L T U β β') := by
  simp_rw [centeredCardinalBandMatrix_eq_difference i lam hL hT hLT]
  exact (continuous_parametric_integral_of_continuous
    (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
    (spatial_scale_domain_isCompact i T hT)).sub
      (continuous_parametric_integral_of_continuous
        (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
        (spatial_scale_domain_isCompact i L hL))

theorem centeredCardinalBandMatrix_l1_square_measurable :
    Measurable (fun U : Fin n → Covariate d => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2) := by
  exact (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (centeredCardinalBandMatrix_continuous i lam hL hT hLT β β').measurable.abs))).pow_const 2

end

def cardinalBandSquareBudget (d n : ℕ) (L : ℝ) : ℝ :=
  ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) *
    L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2)

section
variable {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T)
include hd hn hL hT hLT

theorem centeredCardinalBandMatrix_joint_integrable :
    Integrable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i
        (spatialInterpolationLambda d) L T z.1 z.2) ^ 2)
      ((volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) := by
  let f : Covariate d × (SpatialScaleIndex i → Covariate d) → ℝ := fun z =>
    spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T z.1 z.2) ^ 2
  have hm : Measurable f := (centeredCardinalBandMatrix_l1_square_measurable
    (D := D) i (spatialInterpolationLambda d) hL hT hLT).comp (cardinalHeadSplit i).symm.measurable
  have hx : ∀ᵐ x ∂volume.restrict (spatialPatchBox d), x ∈ spatialPatchBox d :=
    ae_restrict_mem measurableSet_Icc
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hx.mono (fun x hx => anchored_centered_band_matrix_l1_square_integrable i
    (by unfold spatialInterpolationLambda; positivity) hT L x hx), ?_⟩
  have hmn : AEStronglyMeasurable (fun x => ∫ Y, ‖f (x, Y)‖ ∂spatialPatchDesignMeasure i d)
      (volume.restrict (spatialPatchBox d)) :=
    hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  apply (integrable_const (cardinalBandSquareBudget d n L)).mono' hmn
  filter_upwards [hx] with x hx
  have hinner : 0 ≤ ∫ Y, ‖f (x, Y)‖ ∂spatialPatchDesignMeasure i d :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hinner]
  simp only [f, Real.norm_eq_abs, abs_sq]
  apply anchored_centered_band_matrix_l1_square_integral_le <;> assumption

theorem centeredCardinalBandMatrix_full_integrable :
    Integrable (fun U => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2) (fullSpatialPatchDesign d n) := by
  have hp := (cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm
  exact (hp.integrable_comp_emb (cardinalHeadSplit i).symm.measurableEmbedding).mp
      (centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT)

theorem centeredCardinalBandMatrix_full_integral_le :
    (∫ U, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2 ∂fullSpatialPatchDesign d n) ≤
      (2 : ℝ) ^ d * cardinalBandSquareBudget d n L := by
  apply fullSpatialPatchDesign_fiber_integral_le i (centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT)
  intro x hx
  exact anchored_centered_band_matrix_l1_square_integral_le hd hn i x hx hL hT

end

def globalCardinalBandMatrix {d n D : ℕ} (lam L T : ℝ) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) : ℝ :=
  integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β'

theorem globalCardinalBandMatrix_eq_sum {d n D : ℕ} (lam : ℝ)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    globalCardinalBandMatrix lam L T U β β' = ∑ i, centeredCardinalBandMatrix i lam L T U β β' := by
  simp only [globalCardinalBandMatrix, integratedCardinalMatrix, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    (centeredCardinalBandMatrix_eq_difference i lam hL hT hLT U β β').symm)

theorem cardinal_matrix_l1_sum_le {d D : ℕ} {I : Type*} [Fintype I]
    (A : I → HighFrameIndex d D → HighFrameIndex d D → ℝ) :
    spatialMatrixL1 (fun β β' => ∑ i, A i β β') ≤ ∑ i, spatialMatrixL1 (A i) := by
  unfold spatialMatrixL1
  calc
    _ ≤ ∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D, ∑ i : I, |A i β β'| :=
      Finset.sum_le_sum (fun β _ => Finset.sum_le_sum (fun β' _ => Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ β : HighFrameIndex d D, ∑ i : I, ∑ β' : HighFrameIndex d D, |A i β β'| := by
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

section
variable {d n D : ℕ}

theorem globalCardinalBandMatrix_square_le_sum (lam : ℝ)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) (U : Fin n → Covariate d) :
    spatialMatrixL1 (globalCardinalBandMatrix (D := D) lam L T U) ^ 2 ≤
      (n : ℝ) * ∑ i, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2 := by
  have he : globalCardinalBandMatrix (D := D) lam L T U =
      fun β β' => ∑ i, centeredCardinalBandMatrix i lam L T U β β' := by
    funext β β'
    apply globalCardinalBandMatrix_eq_sum <;> assumption
  rw [he]
  have hsum := cardinal_matrix_l1_sum_le (fun i : Fin n =>
    centeredCardinalBandMatrix (D := D) i lam L T U)
  apply ((sq_le_sq₀ (spatial_matrix_l1_nonnegative _)
    (Finset.sum_nonneg (fun i _ => spatial_matrix_l1_nonnegative _))).mpr hsum).trans
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (fun i => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U))

section
variable (hd : 5 ≤ d) (hn : 2 ≤ n)
include hd hn

section
variable {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T)
include hL hT hLT

theorem globalCardinalBandMatrix_square_integrable :
    Integrable (fun U : Fin n → Covariate d =>
      spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2)
      (fullSpatialPatchDesign d n) := by
  have hi := (integrable_finsetSum Finset.univ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)).const_mul (n : ℝ)
  have hm : Measurable (fun U : Fin n → Covariate d =>
      spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2) := by
    exact (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
          (fun β' _ => (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT β β').measurable.abs))).pow_const 2
  apply hi.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    apply globalCardinalBandMatrix_square_le_sum <;> assumption)

theorem globalCardinalBandMatrix_square_integral_le :
    (∫ U, spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalBandSquareBudget d n L := by
  have hi := (integrable_finsetSum Finset.univ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)).const_mul (n : ℝ)
  have hh := integral_mono (globalCardinalBandMatrix_square_integrable (D := D) hd hn hL hT hLT)
    hi (globalCardinalBandMatrix_square_le_sum (spatialInterpolationLambda d) hL hT hLT)
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)] at hh
  apply hh.trans
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ =>
    centeredCardinalBandMatrix_full_integral_le (D := D) hd hn i hL hT hLT)
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)
  convert hm using 1 <;> simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring

end

omit hd in
private theorem globalCardinalBandMatrix_one {T : ℝ} (U : Fin n → Covariate d) :
    globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) 1 T U =
      integratedCardinalMatrix (spatialInterpolationLambda d) T U := by
  unfold globalCardinalBandMatrix
  simp [integrated_cardinal_matrix_one_eq_zero hn]

section
variable {T : ℝ} (hT : 1 ≤ T)
include hT

theorem integratedCardinalMatrix_full_square_integrable :
    Integrable (fun U => spatialMatrixL1 (integratedCardinalMatrix (D := D)
      (spatialInterpolationLambda d) T U) ^ 2) (fullSpatialPatchDesign d n) := by
  have hi := globalCardinalBandMatrix_square_integrable (D := D) hd hn (le_refl 1) hT hT
  simpa only [globalCardinalBandMatrix_one hn] using hi

theorem integratedCardinalMatrix_full_square_integral_le :
    (∫ U, spatialMatrixL1 (integratedCardinalMatrix (D := D) (spatialInterpolationLambda d) T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ d *
      ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) := by
  have hb := globalCardinalBandMatrix_square_integral_le (D := D) hd hn (le_refl 1) hT hT
  simp_rw [globalCardinalBandMatrix_one hn] at hb
  simpa only [cardinalBandSquareBudget, Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one] using hb

end

end

end

end NearlyMinimax
