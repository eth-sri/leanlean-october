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
variable {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n) (i : Fin n) (lam : ℝ) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hLT : L ≤ T)

include hL hT hLT in
theorem centeredCardinalBandMatrix_eq_difference
    (U : DesignSample d n) (β β' : HighFrameIndex d D) :
    centeredCardinalBandMatrix i lam L T U β β' =
      (∫ t, spatialCenteredCardinalMatrix lam U t β β' ∂spatialScaleMeasure i T) -
      (∫ t, spatialCenteredCardinalMatrix lam U t β β' ∂spatialScaleMeasure i L) := setIntegral_sdiff (spatial_scale_domain_isClosed i L).measurableSet
    (spatial_centered_cardinal_matrix_integrable i lam T hT U β β')
    (by intro t ht; refine ⟨ht.1, ?_⟩; exact (show spatialScaleLogSum t ≤ 2 * Real.log _ from ht.2).trans (by bound))

include hL hT hLT in
theorem centeredCardinalBandMatrix_continuous (β β' : HighFrameIndex d D) :
    Continuous (fun U => centeredCardinalBandMatrix i lam L T U β β') := by
  simp_rw [centeredCardinalBandMatrix_eq_difference i lam hL hT hLT]
  exact (continuous_parametric_integral_of_continuous
    (spatial_centered_cardinal_matrix_joint_continuous ..)
    (spatial_scale_domain_isCompact i hT)).sub
      (continuous_parametric_integral_of_continuous
        (spatial_centered_cardinal_matrix_joint_continuous ..)
        (spatial_scale_domain_isCompact i hL))

include hL hT hLT in
theorem centeredCardinalBandMatrix_l1_square_measurable :
    Measurable (fun U : DesignSample d n => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2) := (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
    (fun β' _ => (centeredCardinalBandMatrix_continuous i lam hL hT hLT β β').measurable.abs))).pow_const 2

def cardinalBandSquareBudget (d n : ℕ) (L : ℝ) : ℝ :=
  ((100 * d) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) *
    L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2)

include hd hn hL hT hLT in
theorem centeredCardinalBandMatrix_joint_integrable :
    Integrable (fun z =>
      spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D)
        (spatialInterpolationLambda d) L T z.1 z.2) ^ 2)
      ((volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) := by
  let f : Covariate d × (SpatialScaleIndex i → Covariate d) → ℝ := fun z =>
    spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D)
      (spatialInterpolationLambda d) L T z.1 z.2) ^ 2
  have hm : Measurable f := (centeredCardinalBandMatrix_l1_square_measurable i (spatialInterpolationLambda d) hL hT hLT).comp (cardinalHeadSplit i).symm.measurable
  have hx : ∀ᵐ x ∂volume.restrict (spatialPatchBox d), x ∈ spatialPatchBox d :=
    ae_restrict_mem measurableSet_Icc
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hx.mono (fun x hx => anchored_centered_band_matrix_l1_square_integrable i
    (by unfold spatialInterpolationLambda; positivity) hT L hx), ?_⟩
  apply (integrable_const (cardinalBandSquareBudget d n L)).mono' hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards [hx] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp [f, Real.norm_eq_abs, abs_sq]
  exact anchored_centered_band_matrix_l1_square_integral_le hd hn i hx hL hT

include hd hn hL hT hLT in
theorem centeredCardinalBandMatrix_full_integrable :
    Integrable (fun U => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2) (fullSpatialPatchDesign d n) := (((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm).integrable_comp_emb (cardinalHeadSplit i).symm.measurableEmbedding).mp
      (centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT)

include hd hn hL hT hLT in
theorem centeredCardinalBandMatrix_full_integral_le :
    (∫ U, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2 ∂fullSpatialPatchDesign d n) ≤
      2 ^ d * cardinalBandSquareBudget d n L := by
  rw [fullSpatialPatchDesign_split i _]
  change (∫ z,
    spatialMatrixL1 (anchoredCenteredCardinalBandMatrix
      (spatialInterpolationLambda d) L T z.1 z.2) ^ 2
      ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) ≤ _
  rw [integral_prod _ (centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT)]
  have hi := (centeredCardinalBandMatrix_joint_integrable (D := D) hd hn i hL hT hLT).integral_prod_left
  have hb : (fun x => ∫ Y, spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D)
      (spatialInterpolationLambda d) L T x Y) ^ 2 ∂spatialPatchDesignMeasure i d) ≤ᵐ[
      volume.restrict (spatialPatchBox d)] (fun _ => cardinalBandSquareBudget d n L) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact anchored_centered_band_matrix_l1_square_integral_le hd hn i hx hL hT
  apply (integral_mono_ae hi (integrable_const _) hb).trans_eq
  simp [spatialPatchBox_real_volume]

end

variable {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n) (lam : ℝ) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hLT : L ≤ T)

def globalCardinalBandMatrix (L T : ℝ) (U : DesignSample d n)
    (β β' : HighFrameIndex d D) : ℝ :=
  integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β'

include hL hT hLT in
theorem globalCardinalBandMatrix_eq_sum
    (U : DesignSample d n) (β β' : HighFrameIndex d D) :
    globalCardinalBandMatrix lam L T U β β' = ∑ i, centeredCardinalBandMatrix i lam L T U β β' := by
  simp only [globalCardinalBandMatrix, integratedCardinalMatrix, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    (centeredCardinalBandMatrix_eq_difference i lam hL hT hLT U β β').symm)

theorem cardinal_matrix_l1_sum_le {I : Type*} [Fintype I]
    (A : I → HighFrameIndex d D → HighFrameVector d D) :
    spatialMatrixL1 (fun β β' => ∑ i, A i β β') ≤ ∑ i, spatialMatrixL1 (A i) := by
  calc
    _ ≤ _ :=
      Finset.sum_le_sum (fun β _ => Finset.sum_le_sum (fun β' _ => Finset.abs_sum_le_sum_abs _ _))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

include hL hT hLT in
theorem globalCardinalBandMatrix_square_le_sum (U : DesignSample d n) :
    spatialMatrixL1 (globalCardinalBandMatrix (D := D) lam L T U) ^ 2 ≤
      n * ∑ i, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2 := by
  have he : globalCardinalBandMatrix (D := D) lam L T U =
      fun β β' => ∑ i, centeredCardinalBandMatrix i lam L T U β β' := by
    funext β β'
    solve_by_elim [globalCardinalBandMatrix_eq_sum]
  rw [he]
  have hsum := cardinal_matrix_l1_sum_le (fun i =>
    centeredCardinalBandMatrix (D := D) i lam L T U)
  apply ((sq_le_sq₀ (spatial_matrix_l1_nonnegative _)
    (Finset.sum_nonneg (fun i _ => spatial_matrix_l1_nonnegative _))).mpr hsum).trans
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ => 1) (fun i => spatialMatrixL1 (centeredCardinalBandMatrix i lam L T U))

include hd hn hL hT hLT in
theorem globalCardinalBandMatrix_square_integrable :
    Integrable (fun U =>
      spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2)
      (fullSpatialPatchDesign d n) := by
  have hi := (integrable_finsetSum Finset.univ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)).const_mul n
  apply hi.mono' ((Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _ (fun β' _ => (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT β β').measurable.abs))).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    solve_by_elim [globalCardinalBandMatrix_square_le_sum])

include hd hn hL hT hLT in
theorem globalCardinalBandMatrix_square_integral_le :
    (∫ U, spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ n ^ 2 * 2 ^ d * cardinalBandSquareBudget d n L := by
  have hi := (integrable_finsetSum Finset.univ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)).const_mul n
  have hh := integral_mono (globalCardinalBandMatrix_square_integrable hd hn hL hT hLT)
    hi (globalCardinalBandMatrix_square_le_sum _ hL hT hLT)
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable hd hn i hL hT hLT)] at hh
  apply hh.trans
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    centeredCardinalBandMatrix_full_integral_le (D := D) hd hn i hL hT hLT)
  convert (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)) using 1 <;> simp <;> ring

include hd hn hT in
theorem integratedCardinalMatrix_full_square_integrable :
    Integrable (fun U => spatialMatrixL1 (integratedCardinalMatrix (D := D)
      (spatialInterpolationLambda d) T U) ^ 2) (fullSpatialPatchDesign d n) := by
  have he (U : DesignSample d n) : globalCardinalBandMatrix (D := D)
      (spatialInterpolationLambda d) 1 T U =
      integratedCardinalMatrix (spatialInterpolationLambda d) T U := by
    unfold globalCardinalBandMatrix
    rw [integrated_cardinal_matrix_one_eq_zero hn]
    simp
  have hi := globalCardinalBandMatrix_square_integrable (D := D) hd hn (le_refl 1) hT hT
  simp_all

include hd hn hT in
theorem integratedCardinalMatrix_full_square_integral_le :
    (∫ U, spatialMatrixL1 (integratedCardinalMatrix (D := D) (spatialInterpolationLambda d) T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ n ^ 2 * 2 ^ d *
      ((100 * d) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) := by
  have he (U : DesignSample d n) : globalCardinalBandMatrix (D := D)
      (spatialInterpolationLambda d) 1 T U =
      integratedCardinalMatrix (spatialInterpolationLambda d) T U := by
    unfold globalCardinalBandMatrix
    rw [integrated_cardinal_matrix_one_eq_zero hn]
    simp
  have hb := globalCardinalBandMatrix_square_integral_le (D := D) hd hn (le_refl 1) hT hT
  simp_rw [he] at hb
  simpa only [cardinalBandSquareBudget, Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one] using hb

end NearlyMinimax
