module

public import NearlyMinimax.CardinalBandSpatial
public import NearlyMinimax.SpatialCardinalContinuity


@[expose] public section

/-! True squared coefficient norm of actual centered interpolation bands.
The estimates are derived from cardinal polynomial coefficients, Gamma
normalization, weighted Cauchy--Schwarz and Gaussian spatial decay. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {d n D : ℕ} (i : Fin n) (lam L T : ℝ) (x : Covariate d)

def centeredCardinalBandMatrix
    (U : DesignSample d n) (β β' : HighFrameIndex d D) : ℝ :=
  ∫ t in spatialScaleDomain i T \ spatialScaleDomain i L,
    spatialCenteredCardinalMatrix lam U t β β'

theorem spatial_centered_matrix_cost_integrable
    {T : ℝ} (hT : 1 ≤ T) (U : DesignSample d n) :
    Integrable (fun t => spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) lam U t))
      (spatialScaleMeasure i T) := integrable_finsetSum _ (fun β _ => integrable_finsetSum _
    (fun β' _ => (spatial_centered_cardinal_matrix_integrable i lam T hT U β β').abs))

theorem spatial_centered_band_cost_le_integral_cost
    {T : ℝ} (hT : 1 ≤ T) (U : DesignSample d n) :
    spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ≤
      ∫ t in spatialScaleDomain i T \ spatialScaleDomain i L,
        spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) lam U t) := by
  have hμ : volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L) ≤ spatialScaleMeasure i T :=
    Measure.restrict_mono_set volume Set.sdiff_subset
  have hi (β β' : HighFrameIndex d D) :=
    (spatial_centered_cardinal_matrix_integrable i lam T hT U β β').mono_measure hμ
  unfold spatialMatrixL1 centeredCardinalBandMatrix
  rw [integral_finsetSum _ (fun β _ => integrable_finsetSum _ (fun β' _ => (hi β β').abs))]
  apply Finset.sum_le_sum
  intro β hβ
  rw [integral_finsetSum _ (fun β' _ => (hi β β').abs)]
  exact Finset.sum_le_sum (fun β' _ => by
    simpa using norm_integral_le_integral_norm
      (fun t => spatialCenteredCardinalMatrix lam U t β β'))

/-- The squared actual centered band matrix is bounded by its actual
scale kernel integral; no desired norm bound is a premise. -/
theorem centered_cardinal_band_matrix_l1_square_le {lam : ℝ}
    (hlam : 0 ≤ lam) (L : ℝ) {T : ℝ} (hT : 1 ≤ T)
    {U : DesignSample d n} (hU : ∀ l r, |U l r| ≤ 2) :
    (spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U)) ^ 2 ≤
      (100 * d) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
        ∫ t in spatialScaleDomain i T \ spatialScaleDomain i L,
          spatialCardinalScale lam (spatialScaleExtend t) U i := by
  let s := spatialScaleDomain i T \ spatialScaleDomain i L
  let C : ℝ := (100 * d) ^ (2 * Fintype.card (SpatialScaleIndex i))
  have hs : s ⊆ Ici 0 := fun t ht => ht.1.1
  have hμ : volume.restrict s ≤ spatialScaleMeasure i T := Measure.restrict_mono_set volume Set.sdiff_subset
  have hh := (spatial_centered_matrix_cost_integrable (D := D) i lam hT U).mono_measure hμ
  have hw  :=
    (spatial_cardinal_weight_orthant_integrable i hlam U).mono_measure
      (Measure.restrict_mono_set volume hs)
  have hscale : Integrable (fun t => spatialCardinalScale lam (spatialScaleExtend t) U i) (volume.restrict s) := ((spatial_centered_cardinal_scale_continuous i lam U).continuousOn.integrableOn_compact (spatial_scale_domain_isCompact i hT)).mono_set Set.sdiff_subset
  have hnn : ∀ᵐ t ∂volume.restrict s, 0 ≤ spatialCardinalScale lam (spatialScaleExtend t) U i := by
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    solve_by_elim [spatial_cardinal_scale_nonnegative]
  have hwn  :=
    (spatial_cardinal_weight_orthant_nonnegative i lam U).filter_mono
      (ae_mono (Measure.restrict_mono_set volume hs))
  have hcs := integral_square_le_weight_mass_mul _ hh hw (hscale.const_mul C)
    hwn (hnn.mono (fun t ht => mul_nonneg (by positivity) ht)) (by
      filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
        (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
      solve_by_elim [spatial_centered_matrix_l1_square_le_weight_scale])
  have hmass  :=
    (integral_mono_measure (Measure.restrict_mono_set volume hs)
      (spatial_cardinal_weight_orthant_nonnegative ..)
      (spatial_cardinal_weight_orthant_integrable i hlam U)).trans
        (spatial_cardinal_weight_orthant_integral_le_one i hlam U)
  have hbound := hcs.trans (by simpa using mul_le_mul_of_nonneg_right hmass (integral_nonneg_of_ae (hnn.mono (fun t ht => mul_nonneg (by positivity) ht))))
  have hnCost : 0 ≤ ∫ t in s, spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) lam U t) :=
    integral_nonneg (fun _ => spatial_matrix_l1_nonnegative _)
  have htriangle := (sq_le_sq₀ (spatial_matrix_l1_nonnegative _) hnCost).mpr
    (spatial_centered_band_cost_le_integral_cost i lam L hT U)
  exact htriangle.trans (by simpa only [integral_const_mul] using hbound)

theorem anchored_patch_configuration_continuous :
    Continuous (anchoredPatchConfiguration (i := i) x) := by
  apply continuous_pi
  intro l
  unfold anchoredPatchConfiguration
  split_ifs <;> fun_prop

theorem anchored_centered_matrix_entry_joint_continuous (β β' : HighFrameIndex d D) :
    Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      spatialCenteredCardinalMatrix lam (anchoredPatchConfiguration x z.2) z.1 β β') := by
  have hc (γ : HighFrameIndex d D) :
      Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
        highFrameCoefficients (spatialCardinalPolynomial (anchoredPatchConfiguration x z.2) i) γ) :=
    (spatial_cardinal_polynomial_coefficients_continuous i (polynomialBoxExponent γ.val)).comp
      ((anchored_patch_configuration_continuous i x).comp continuous_snd)
  exact ((anchored_cardinal_scale_continuous_actual i lam x).mul (hc β)).mul (hc β')

def anchoredCenteredCardinalBandMatrix {i : Fin n} (lam L T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : HighFrameIndex d D → HighFrameVector d D :=
  centeredCardinalBandMatrix i lam L T (anchoredPatchConfiguration x Y)

theorem anchored_patch_configuration_in_box_ae {x : Covariate d}
    (hx : x ∈ spatialPatchBox d) :
    ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ l r, |anchoredPatchConfiguration x Y l r| ≤ 2 := by
  have hae : ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ j, Y j ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro j
    exact (Measure.tendsto_eval_ae_ae).eventually (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hae] with Y hY
  intro l r
  by_cases hl : l ≠ i
  · have hh := hY ⟨l, hl⟩
    simp only [anchoredPatchConfiguration, dite_eq_left hl]
    apply (abs_le.mpr ⟨hh.1 r, hh.2 r⟩).trans
    norm_num
  · have hli  := not_ne_iff.mp hl
    subst l
    rw [anchored_configuration_same]
    exact (abs_le.mpr ⟨hx.1 r, hx.2 r⟩).trans (by norm_num)

theorem anchored_centered_band_matrix_l1_square_measurable :
    Measurable (fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) (i := i) lam L T x Y)) ^ 2) := (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
    (fun β' _ => ((by have h := (anchored_centered_matrix_entry_joint_continuous i lam x β β').stronglyMeasurable.integral_prod_left' (μ := volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)); exact h.measurable : Measurable fun Y => anchoredCenteredCardinalBandMatrix lam L T x Y β β')).abs))).pow_const 2

theorem anchored_centered_band_matrix_l1_square_integrable
    {lam T : ℝ} (hlam : 0 ≤ lam) (hT : 1 ≤ T) (L : ℝ) {x : Covariate d} (hx : x ∈ spatialPatchBox d) :
    Integrable (fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) lam L T x Y)) ^ 2)
      (spatialPatchDesignMeasure i d) := by
  have hi := (anchored_cardinal_band_scale_joint_integrable i hlam hT L x).integral_prod_right.const_mul
    ((100 * d) ^ (2 * Fintype.card (SpatialScaleIndex i)))
  apply hi.mono' (anchored_centered_band_matrix_l1_square_measurable i lam L T x).aestronglyMeasurable
  filter_upwards [anchored_patch_configuration_in_box_ae i hx] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact centered_cardinal_band_matrix_l1_square_le i hlam L hT hY

/-- Actual fixed-head spatial L² bound for the centered cardinal band.
The constant is explicit and depends only on dimension. -/
theorem anchored_centered_band_matrix_l1_square_integral_le (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) {x : Covariate d} (hx : x ∈ spatialPatchBox d) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) :
    (∫ Y, (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T x Y)) ^ 2
      ∂spatialPatchDesignMeasure i d) ≤
      ((100 * d) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) *
        L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2) := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hi := (anchored_cardinal_band_scale_joint_integrable i hlam hT L x).integral_prod_right.const_mul
    ((100 * d) ^ (2 * Fintype.card (SpatialScaleIndex i)))
  have hdom : (fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T x Y)) ^ 2)
      ≤ᵐ[spatialPatchDesignMeasure i d]
      (fun Y => (100 * d) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
        ∫ t in spatialScaleDomain i T \ spatialScaleDomain i L,
          anchoredCardinalScale (spatialInterpolationLambda d) x t Y) := by
    filter_upwards [anchored_patch_configuration_in_box_ae i hx] with Y hY
    exact centered_cardinal_band_matrix_l1_square_le i hlam L hT hY
  have hfirst := integral_mono_ae (anchored_centered_band_matrix_l1_square_integrable i hlam hT L hx) hi hdom
  rw [integral_const_mul, spatial_scale_index_card] at hfirst
  have htail := mul_le_mul_of_nonneg_left (anchored_cardinal_band_scale_spatial_integral_bound hd hn i hx hL hT)
    (by positivity : 0 ≤ (100 * (d : ℝ)) ^ (2 * (n - 1)))
  have hfull := hfirst.trans htail
  simpa only [mul_pow, ← pow_mul,  mul_assoc,  mul_left_comm] using hfull

end NearlyMinimax
