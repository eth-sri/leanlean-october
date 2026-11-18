module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import NearlyMinimax.CardinalInterpolationBias
public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.LowerSaddle

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators ENNReal Topology
namespace NearlyMinimax

-- ============================================================================
-- 1. Cardinal Band & Defect L2, Raw Cardinal Envelope, and Fine-Field Envelopes
-- ============================================================================

section CardinalAndFineEnvelopes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem centeredCardinalBandMatrix_eq_difference {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    centeredCardinalBandMatrix i lam L T U β β' =
      (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T) -
      (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i L) :=
  setIntegral_sdiff (spatial_scale_domain_isClosed i L).measurableSet
    (spatial_centered_cardinal_matrix_integrable i lam T hT U β β')
    (spatial_scale_domain_mono i (lt_of_lt_of_le (by norm_num) hL) hLT)

lemma centeredCardinalBandMatrix_l1_square_measurable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Measurable fun U : Fin n → Covariate d =>
      spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2 := by
  unfold spatialMatrixL1
  refine (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ => ?_).pow_const 2
  have hc : Continuous fun U => centeredCardinalBandMatrix i lam L T U β β' := by
    simp_rw [centeredCardinalBandMatrix_eq_difference i lam hL hT hLT]
    exact (continuous_parametric_integral_of_continuous
      (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
      (spatial_scale_domain_isCompact i T hT)).sub
        (continuous_parametric_integral_of_continuous
          (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
          (spatial_scale_domain_isCompact i L hL))
  exact hc.measurable.abs

def cardinalBandSquareBudget (d n : ℕ) (L : ℝ) : ℝ :=
  ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) *
    L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2)

lemma centeredCardinalBandMatrix_joint_integrable {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
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
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨hx.mono fun x hx => anchored_centered_band_matrix_l1_square_integrable i
      (by unfold spatialInterpolationLambda; positivity) hT L x hx, ?_⟩
  apply (integrable_const (cardinalBandSquareBudget d n L)).mono'
    hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards [hx] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simpa only [f, Real.norm_eq_abs, abs_sq, cardinalBandSquareBudget] using
    anchored_centered_band_matrix_l1_square_integral_le hd hn i x hx hL hT

lemma centeredCardinalBandMatrix_full_integrable {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2) (fullSpatialPatchDesign d n) :=
  ((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm.integrable_comp_emb
    (cardinalHeadSplit i).symm.measurableEmbedding).mp
    (centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT)

lemma centeredCardinalBandMatrix_full_integral_le {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    (∫ U, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2 ∂fullSpatialPatchDesign d n) ≤
      (2 : ℝ) ^ d * cardinalBandSquareBudget d n L := by
  have hj := centeredCardinalBandMatrix_joint_integrable (D := D) hd hn i hL hT hLT
  rw [fullSpatialPatchDesign_split i _]
  change (∫ z : Covariate d × (SpatialScaleIndex i → Covariate d),
    spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T z.1 z.2) ^ 2
      ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) ≤ _
  rw [integral_prod _ hj]
  apply (integral_mono_ae hj.integral_prod_left (integrable_const _) ?_).trans_eq
  · simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    change volume.real (spatialPatchBox d) * cardinalBandSquareBudget d n L = _
    rw [spatialPatchBox_real_volume]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact anchored_centered_band_matrix_l1_square_integral_le hd hn i x hx hL hT

def globalCardinalBandMatrix {d n D : ℕ} (lam L T : ℝ) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) : ℝ :=
  integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β'

lemma globalCardinalBandMatrix_square_le_sum {d n D : ℕ} (lam : ℝ)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) (U : Fin n → Covariate d) :
    spatialMatrixL1 (globalCardinalBandMatrix (D := D) lam L T U) ^ 2 ≤
      (n : ℝ) * ∑ i, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2 := by
  have he : globalCardinalBandMatrix (D := D) lam L T U =
      fun β β' => ∑ i, centeredCardinalBandMatrix i lam L T U β β' := by
    funext β β'
    simp only [globalCardinalBandMatrix, integratedCardinalMatrix, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      (centeredCardinalBandMatrix_eq_difference i lam hL hT hLT U β β').symm
  rw [he]
  have hsum : spatialMatrixL1 (fun β β' => ∑ i, centeredCardinalBandMatrix (D := D) i lam L T U β β') ≤
      ∑ i, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) := by
    unfold spatialMatrixL1
    calc
      _ ≤ ∑ β, ∑ β', ∑ i, |centeredCardinalBandMatrix (D := D) i lam L T U β β'| :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ β, ∑ i, ∑ β', |centeredCardinalBandMatrix (D := D) i lam L T U β β'| :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  apply ((sq_le_sq₀ (spatial_matrix_l1_nonnegative _)
    (Finset.sum_nonneg fun _ _ => spatial_matrix_l1_nonnegative _)).mpr hsum).trans
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) fun i => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U)

theorem globalCardinalBandMatrix_square_integrable {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U : Fin n → Covariate d =>
      spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2)
      (fullSpatialPatchDesign d n) := by
  have hi := (integrable_finsetSum Finset.univ fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT).const_mul (n : ℝ)
  have hm : Measurable fun U : Fin n → Covariate d =>
      spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2 := by
    unfold spatialMatrixL1 globalCardinalBandMatrix
    exact (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ =>
      (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT β β').measurable.abs).pow_const 2
  exact hi.mono' hm.aestronglyMeasurable <| Filter.Eventually.of_forall fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    exact globalCardinalBandMatrix_square_le_sum (spatialInterpolationLambda d) hL hT hLT U

theorem globalCardinalBandMatrix_square_integral_le {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    (∫ U, spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalBandSquareBudget d n L := by
  have hi := (integrable_finsetSum Finset.univ fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT).const_mul (n : ℝ)
  have hh := integral_mono (globalCardinalBandMatrix_square_integrable (D := D) hd hn hL hT hLT)
    hi (globalCardinalBandMatrix_square_le_sum (spatialInterpolationLambda d) hL hT hLT)
  rw [integral_const_mul, integral_finsetSum _ fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT] at hh
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) fun i _ =>
      centeredCardinalBandMatrix_full_integral_le (D := D) hd hn i hL hT hLT)
    (Nat.cast_nonneg n)
  convert hm using 1 <;> simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring

lemma globalCardinalBandMatrix_one_eq {d n D : ℕ} (hn : 2 ≤ n) (T : ℝ)
    (U : Fin n → Covariate d) :
    globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) 1 T U =
      integratedCardinalMatrix (spatialInterpolationLambda d) T U := by
  unfold globalCardinalBandMatrix
  rw [integrated_cardinal_matrix_one_eq_zero hn]; simp

theorem integratedCardinalMatrix_full_square_integrable {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun U => spatialMatrixL1 (integratedCardinalMatrix (D := D)
      (spatialInterpolationLambda d) T U) ^ 2) (fullSpatialPatchDesign d n) := by
  simpa only [globalCardinalBandMatrix_one_eq hn T] using
    globalCardinalBandMatrix_square_integrable (D := D) hd hn (le_refl 1) hT hT

theorem integratedCardinalMatrix_full_square_integral_le {d n D : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ U, spatialMatrixL1 (integratedCardinalMatrix (D := D) (spatialInterpolationLambda d) T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ d *
      ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) := by
  simpa only [globalCardinalBandMatrix_one_eq hn T, cardinalBandSquareBudget,
    Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one] using
    globalCardinalBandMatrix_square_integral_le (D := D) hd hn (le_refl 1) hT hT

def cardinalWeightDefect {d n : ℕ} (i : Fin n) (lam T : ℝ)
    (U : Fin n → Covariate d) : ℝ := 1 - integratedCardinalWeight lam T U i

def cardinalDefectSquareBudget (d n : ℕ) (T : ℝ) : ℝ :=
  (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
    T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2)

theorem cardinalWeightDefect_measurable {d n : ℕ} (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) : Measurable (cardinalWeightDefect (d := d) i lam T) :=
  measurable_const.sub (integrated_cardinal_weight_continuous i lam hT).measurable

theorem cardinalWeightDefect_mem_unit {d n : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) (T : ℝ) (U : Fin n → Covariate d) :
    cardinalWeightDefect i lam T U ∈ Icc (0 : ℝ) 1 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam U
  unfold cardinalWeightDefect
  constructor <;> linarith only [h.1, h.2]

theorem cardinalWeightDefect_square_integrable {d n : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun U => cardinalWeightDefect i lam T U ^ 2) (fullSpatialPatchDesign d n) := by
  apply Integrable.of_bound ((cardinalWeightDefect_measurable i lam hT).pow_const 2).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    have h := cardinalWeightDefect_mem_unit i hlam T U
    nlinarith only [h.1, h.2]

lemma cardinalWeightDefect_full_square_integral_le {d n : ℕ} (hd : 0 < d)
    (hn : 2 ≤ n) (i : Fin n) {T : ℝ} (hT : 1 ≤ T) :
    (∫ U, cardinalWeightDefect i (spatialInterpolationLambda d) T U ^ 2
      ∂fullSpatialPatchDesign d n) ≤ (2 : ℝ) ^ d * cardinalDefectSquareBudget d n T := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hj : Integrable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalDefect i (spatialInterpolationLambda d) T z.1 z.2 ^ 2)
      ((volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) :=
    (cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm.integrable_comp_of_integrable
      (cardinalWeightDefect_square_integrable i hlam hT)
  rw [fullSpatialPatchDesign_split i _]
  change (∫ z : Covariate d × (SpatialScaleIndex i → Covariate d),
    anchoredCardinalDefect i (spatialInterpolationLambda d) T z.1 z.2 ^ 2
      ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) ≤ _
  rw [integral_prod _ hj]
  apply (integral_mono_ae hj.integral_prod_left (integrable_const _) ?_).trans_eq
  · simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    change volume.real (spatialPatchBox d) * cardinalDefectSquareBudget d n T = _
    rw [spatialPatchBox_real_volume]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact anchored_cardinal_defect_square_integral_le hd hn i x hx hT

theorem cardinalWeightDefect_sum_square_integral_le {d n : ℕ} (hd : 0 < d)
    (hn : 2 ≤ n) {T : ℝ} (hT : 1 ≤ T) :
    (∫ U, (∑ i : Fin n, cardinalWeightDefect i (spatialInterpolationLambda d) T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      (n : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalDefectSquareBudget d n T := by
  simpa only [Finset.card_univ, Fintype.card_fin, ← mul_assoc] using
    finite_sum_square_integral_le (fullSpatialPatchDesign d n) Finset.univ
      (fun i => cardinalWeightDefect i (spatialInterpolationLambda d) T)
      ((2 : ℝ) ^ d * cardinalDefectSquareBudget d n T)
      (fun i _ => cardinalWeightDefect_measurable i _ hT)
      (fun i _ => cardinalWeightDefect_square_integrable i
        (by unfold spatialInterpolationLambda; positivity) hT)
      (fun i _ => cardinalWeightDefect_full_square_integral_le hd hn i hT)

def highCardinalRawNumerator {d n F : ℕ} (ad bd lam T : ℝ) (m D q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  (∫ᵛ e, highPacketObservable ad bd m n D q C c
    (fun ζ z eps => ∏ i, highCardinalDensityReset ad bd lam U p ζ z eps i)
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) e
    ∂<•highPacketSignedMeasure (cardinalSeparatedMeasure d n T) ad bd m n D q C
      (cardinalSeparatedAmplitude lam)) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

theorem highCardinalRawNumerator_eq_alias_defect {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      (∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
        g w (fun i => highFrameFeature (U i)) c y := by
  letI := cardinal_separated_measure_finite d n hT
  have hm (z : ℝ) (eps : Fin n → ℝ) (i : Fin n) :
      Measurable fun ζ => highCardinalDensityReset ad bd lam U p ζ z eps i := by
    unfold highCardinalDensityReset localDensityReset
    exact (Finset.measurable_fun_sum _ fun l _ =>
      (cardinal_separated_factor_measurable lam l (U i)).const_mul (eps l)).const_mul _ |>.const_add z
  have hb (ζ : CardinalSeparatedMark d n) (e : HighDensityMarkIndex m n D) (i : Fin n) :
      |highCardinalDensityReset ad bd lam U p ζ (densityPacketAtom ad bd m n D e).1
        (densityPacketAtom ad bd m n D e).2 i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le m n D e
    have h := localDensityReset_mem_interval ad bd haD hab n hn _ he.1 _ he.2 p
      (fun i l => cardinalSeparatedFactor lam ζ l (U i)) i (hp i)
      fun l => cardinal_separated_factor_abs_le_one lam ζ l (U i) (hU i)
    change |localDensityReset ad bd n _ _ p _ i| ≤ _
    rw [abs_of_nonneg (haD.le.trans h.1)]; exact h.2
  unfold highCardinalRawNumerator
  rw [highPacketSignedMeasure_factor_integral _ ad bd m n D q C _
    (cardinal_separated_amplitude_measurable lam) (cardinal_separated_cost_integrable lam hT) c _
    (fun z eps => Finset.measurable_fun_prod _ fun i _ => hm z eps i)
    (bd^n) (pow_nonneg (haD.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ bd (haD.trans hab).le (hb ζ e))
    _ (finePairResponseAtomBound q C c _) (finePairResponseAtomBound_le q C c _),
    high_cardinal_packet_action_exact ad bd lam haD hab hlam hT m D q hn hnm hnD C U hU p c,
    integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]; ring

def cardinalRawAliasCoefficient (n : ℕ) (bd a η : ℝ) : ℝ := η^2 * bd^n / a^2

def cardinalRawTaylorCoefficient (n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  bd^n * highResponseRemainderConstant q C a ρ * (n : ℝ)^(2*q+2) * η^(2*q+2)

theorem highCardinalRawNumerator_square_bound_of_chart {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (hq : 1 ≤ q)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y ^ 2 ≤
      2 * cardinalRawAliasCoefficient n bd a η ^ 2 * (∑ i, cardinalWeightDefect i lam T U)^2 +
      2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
        spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U)^2 := by
  have hCpos := lt_of_lt_of_le zero_lt_one hC
  have hbd : 0 ≤ bd := (haD.trans hab).le
  have hpabs (i : Fin n) : |p i| ≤ bd := by
    rw [abs_of_pos (haD.trans_le (hpD i).1)]; exact (hpD i).2
  have hMass (i : Fin n) (u : Fin 3) :
      0 ≤ ternaryMass a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c i) V u :=
    hp _ (highFrameCoefficientRegression_abs_le C η ρ hC hη hηρ U hU g w hg hw c hc i) u
  have hterm (i : Fin n) :
      |(w i)^2 * (integratedCardinalWeight lam T U i-1) *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      cardinalWeightDefect i lam T U * (1/a^2) := by
    have hd := cardinalWeightDefect_mem_unit i hlam T U
    have hw2 : (w i)^2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hw i)
    have hv := high_response_variance_term_abs_bound a V η ha g w
      (fun i => highFrameFeature (U i)) c hMass y i
    rw [abs_mul, abs_mul, abs_sq, abs_sub_comm]
    change (w i)^2 * |cardinalWeightDefect i lam T U| *
      |highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤ _
    rw [abs_of_nonneg hd.1]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hw2 hd.1) hv (abs_nonneg _)
      (by simpa only [one_mul] using hd.1)).trans_eq (by ring)
  have hAlias : |η^2 * (∏ i, p i) * ∑ i, (w i)^2 * (integratedCardinalWeight lam T U i-1) *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i| ≤
      cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) := by
    rw [abs_mul, abs_mul, abs_sq]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound p bd hbd hpabs)
      (sq_nonneg η)) ((Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum fun i _ => hterm i))
      (abs_nonneg _) (mul_nonneg (sq_nonneg η) (pow_nonneg hbd n))
    exact hh.trans_eq (by rw [← Finset.sum_mul]; unfold cardinalRawAliasCoefficient; ring)
  have hRem := high_response_defect_abs_bound q hq C a V η ρ hCpos ha hη hρ hηρ
    (integratedCardinalMatrix lam T U) g w (fun i => highFrameFeature (U i)) c y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp
  have hTaylor : |(∏ i, p i) * highResponseDefect q C a V η (integratedCardinalMatrix lam T U)
      g w (fun i => highFrameFeature (U i)) c y| ≤
      cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound p bd hbd hpabs) hRem
      (abs_nonneg _) (pow_nonneg hbd n)).trans_eq (by unfold cardinalRawTaylorCoefficient spatialMatrixL1; ring)
  have h : |highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y| ≤
      cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) +
        cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) := by
    rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q hn hnm hnD hnF
      C a V η hCpos.ne' U hU p g w hpD c y]
    exact (abs_add_le _ _).trans (add_le_add hAlias hTaylor)
  have hsum : 0 ≤ ∑ i, cardinalWeightDefect i lam T U :=
    Finset.sum_nonneg fun i _ => (cardinalWeightDefect_mem_unit i hlam T U).1
  have hA : 0 ≤ cardinalRawAliasCoefficient n bd a η := by
    unfold cardinalRawAliasCoefficient; positivity
  have hB : 0 ≤ cardinalRawTaylorCoefficient n q bd C a ρ η := by
    unfold cardinalRawTaylorCoefficient highResponseRemainderConstant
    have hDer : 0 ≤ highResponseDerivativeBudget a ρ :=
      zero_le_one.trans (highResponseDerivativeBudget_guards a ρ).1
    positivity
  have hM : 0 ≤ spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U) :=
    spatial_matrix_l1_nonnegative _
  have hh := (sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg hA hsum) (mul_nonneg hB hM))).mpr h
  rw [sq_abs] at hh
  nlinarith only [hh, sq_nonneg (cardinalRawAliasCoefficient n bd a η * (∑ i, cardinalWeightDefect i lam T U) -
    cardinalRawTaylorCoefficient n q bd C a ρ η * spatialMatrixL1 (integratedCardinalMatrix (D := F) lam T U))]

def fineFieldSubsetEnergyBase (d : ℕ) : ℝ :=
  4 * (2 : ℝ) ^ d * hyperplaneSpatialMomentConstant d ^ 2

theorem finePairTimeSubsetMoment_sum_abs_square_integral_le {d k : ℕ} [NeZero d]
    (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) (s : Finset (Finset (Fin k)))
    (hs : ∀ S ∈ s, 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, (∑ S ∈ s, |finePairTimeSubsetMoment lo hi U S|) ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      fineFieldSubsetEnergyBase d ^ k * (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2 := by
  let K : ℝ := (2 : ℝ) ^ (d * k) * hyperplaneSpatialMomentConstant d ^ (2 * k) *
    (k : ℝ) ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2
  have hC1 : 1 ≤ hyperplaneSpatialMomentConstant d := by
    unfold hyperplaneSpatialMomentConstant
    have hp : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hc := spatialExponentialConstant_nonneg d
    nlinarith only [hp, hc]
  have hC0 : 0 ≤ hyperplaneSpatialMomentConstant d := zero_le_one.trans hC1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hunif (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
      (∫ U : Fin k → Covariate d, |finePairTimeSubsetMoment lo hi U S| ^ 2
        ∂fullSpatialPatchDesign d k) ≤ K := by
    simp only [sq_abs]
    have hc : S.card ≤ k := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)
    have hv : (2 : ℝ) ^ (d * (k - S.card)) ≤ (2 : ℝ) ^ (d * k) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le _ _))
    have hconst : hyperplaneSpatialMomentConstant d ^ (2 * S.card) ≤
        hyperplaneSpatialMomentConstant d ^ (2 * k) :=
      pow_le_pow_right₀ hC1 (Nat.mul_le_mul_left 2 hc)
    have hj : (S.card : ℝ) ^ 8 ≤ (k : ℝ) ^ 8 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hc) 8
    apply (finePairTimeSubsetMoment_square_integral_le hd (hi := hi) hlo S hS).trans
    have h2 := mul_le_mul hv hconst (pow_nonneg hC0 _) (by positivity)
    have h3 := mul_le_mul h2 hj (pow_nonneg (Nat.cast_nonneg S.card) 8)
      (mul_nonneg (by positivity) (pow_nonneg hC0 _))
    have hh := mul_le_mul_of_nonneg_right h3 (sq_nonneg (lo ^ (2 - (d : ℝ))))
    convert hh using 1 <;> simp only [K, mul_pow, ← pow_mul] <;> ring
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d k) s
    (fun S U => |finePairTimeSubsetMoment lo hi U S|) K
    (fun S _ => (finePairTimeSubsetMoment_measurable lo hi S).abs)
    (fun S hS => by simpa only [sq_abs] using finePairTimeSubsetMoment_square_integrable hd hlo S (hs S hS))
    fun S hS => hunif S (hs S hS)
  have hcNat : s.card ≤ 2 ^ k := by
    simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (show s ⊆ (Finset.univ : Finset (Fin k)).powerset by intro S _; simp)
  have hc : (s.card : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcNat) 2
  apply (h.trans (mul_le_mul_of_nonneg_right hc hK)).trans_eq
  dsimp [K, fineFieldSubsetEnergyBase]
  simp only [mul_pow, pow_mul]
  rw [show (4 : ℝ) ^ k = (2 : ℝ) ^ (k * 2) by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]]
  ring

lemma fine_pair_filtered_sum_abs_bound {I : Type*} (s : Finset I) (P : I → Prop) [DecidablePred P]
    (c H : I → ℝ) (R B K : ℝ) (hB : 0 ≤ B)
    (hc : ∀ i ∈ s, |c i| ≤ B) (hR : |R| ≤ K) :
    |∑ i ∈ s, c i * (if P i then 1 else 0) * H i * R| ≤
      B*K * ∑ i ∈ s, if P i then |H i| else 0 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  by_cases hP : P i
  · simp only [if_pos hP, mul_one]
    calc _ = (|c i| * |R|) * |H i| := by rw [abs_mul, abs_mul]; ring
      _ ≤ (B*K) * |H i| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hc i hi) hR (abs_nonneg _) hB) (abs_nonneg _)
  · simp [hP]

section ChartActionEnvelopes
variable {d n F : ℕ} (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (M q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
include haD hab hn hC ha hη hρ hηρ hU hpD hc hg hw hp

theorem finePairPairAliasAction_abs_bound_of_chart :
    |finePairPairAliasAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
      finePairDensityCoefficientBudget ad bd M n *
        (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2) *
          ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
            if W.card = 2 then |finePairTimeSubsetMoment T0 N U W| else 0 :=
  fine_pair_filtered_sum_abs_bound ((Finset.univ : Finset (Fin n)).powerset) (fun W => W.card = 2)
    (fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i)
    (fun W => finePairTimeSubsetMoment T0 N U W) _ _ _
    (finePairDensityCoefficientBudget_nonneg ad bd (haD.trans hab).le M n)
    (fun W _ => finePairCountCoefficient_product_bound ad bd haD hab M p hpD W)
    (finePairDistance_response_all_count_bound q hn C a V η ρ (lt_of_lt_of_le zero_lt_one hC)
      ha hη hρ hηρ U g w c y hc hg hw
      (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp)

theorem finePairEvenFieldAction_abs_bound_of_chart :
    |finePairEvenFieldAction ad bd T0 N M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
      finePairDensityCoefficientBudget ad bd M n *
        (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2) *
          ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
            if 4 ≤ W.card ∧ Even W.card then |finePairTimeSubsetMoment T0 N U W| else 0 :=
  fine_pair_filtered_sum_abs_bound ((Finset.univ : Finset (Fin n)).powerset) (fun W => 4 ≤ W.card ∧ Even W.card)
    (fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i)
    (fun W => finePairTimeSubsetMoment T0 N U W) _ _ _
    (finePairDensityCoefficientBudget_nonneg ad bd (haD.trans hab).le M n)
    (fun W _ => finePairCountCoefficient_product_bound ad bd haD hab M p hpD W)
    (finePairDistance_response_all_count_bound q hn C a V η ρ (lt_of_lt_of_le zero_lt_one hC)
      ha hη hρ hηρ U g w c y hc hg hw
      (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp)

end ChartActionEnvelopes

theorem finite_sum_abs_square_integrable {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ) :
    Integrable (fun x => (∑ i ∈ s, |f i x|)^2) μ := by
  apply ((integrable_finsetSum s hi).const_mul (s.card : ℝ)).mono'
    ((Finset.measurable_sum s fun i hi => (hm i hi).abs).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_sq]
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : I => (1 : ℝ)) fun i => |f i x|

def finePairEvenActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2))^2 *
      fineFieldSubsetEnergyBase d ^ n * (n : ℝ)^8 * (T0 ^ (2-(d : ℝ)))^2

def cardinalRawSpatialEnergyBudget (d n q : ℕ) (bd C a ρ η T : ℝ) : ℝ :=
  2 * cardinalRawAliasCoefficient n bd a η ^ 2 *
      ((n : ℝ)^2 * (2 : ℝ)^d * cardinalDefectSquareBudget d n T) +
    2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
      ((n : ℝ)^2 * (2 : ℝ)^d *
        ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^(n-1))

end CardinalAndFineEnvelopes

-- ============================================================================
-- 2. Patch Chart Measure, Selected Score Energy, and Marked Response Selection
-- ============================================================================

section PatchAndSelection
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def highAffineChart (d k : ℕ) (z : Fin d → ℤ) (x : Covariate d) : Covariate d :=
  fun r => (k : ℝ) * x r - z r

lemma highAffineChart_measurable (d k : ℕ) (z : Fin d → ℤ) :
    Measurable (highAffineChart d k z) := by unfold highAffineChart; fun_prop

lemma highAffineChart_map_volume (d k : ℕ) (hk : 0 < k) (z : Fin d → ℤ) :
    Measure.map (highAffineChart d k z) volume =
      ENNReal.ofReal ((k : ℝ)^d)⁻¹ • (volume : Measure (Covariate d)) := by
  let f : Covariate d →ₗ[ℝ] Covariate d := (k : ℝ) • LinearMap.id
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdet : LinearMap.det f = (k : ℝ)^d := by
    simp [f, LinearMap.det_smul, LinearMap.det_id]
  have hf := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f) (by rw [hdet]; positivity)
  have heq : highAffineChart d k z = (fun x : Covariate d => (fun r => -(z r : ℝ)) + x) ∘ f := by
    funext x r; simp [highAffineChart, f]; ring
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), hf, hdet,
    Measure.map_smul _ (by fun_prop), map_add_left_eq_self]
  congr 1; rw [abs_of_nonneg (by positivity)]

lemma highPatch_lift_cube_cases (k : ℕ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (z : ℤ)
    (hz : (z : ZMod k) = j) (hclose : |(k : ℝ)*x-z| < 1) :
    z = (j.val : ℤ) ∨ z = (j.val : ℤ)+(k : ℤ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkv : (j.val : ℤ) < k := by exact_mod_cast ZMod.val_lt j
  obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have hzz : 0 ≤ z ∧ z ≤ (k : ℤ) := by
    have hh := abs_lt.mp hclose
    have hzLZ : (-1 : ℤ) < z := by exact_mod_cast (show (-1 : ℝ) < z by nlinarith [mul_nonneg hkR.le hx.1])
    have hzUZ : z < (k : ℤ)+1 := by exact_mod_cast (show (z : ℝ) < k+1 by nlinarith [mul_le_mul_of_nonneg_left hx.2 hkR.le])
    omega
  have hj0 : (0 : ℤ) ≤ j.val := Int.natCast_nonneg _
  have hkZ : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
  have hqL : 0 ≤ q := by
    by_contra h
    have : q ≤ -1 := by omega
    nlinarith
  have hqU : q ≤ 1 := by
    by_contra h
    have : 2 ≤ q := by omega
    nlinarith
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · exact Or.inl (by simpa using hq)
  · exact Or.inr (by simpa using hq)

lemma highLocalCoordinates_eq_affine_on_patch {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) {x : Covariate d} (_hx : x ∈ highTorusPatch d k j)
    (z : Fin d → ℤ) (hz : ∀ r, (z r : ZMod k)=j r)
    (hc : ∀ r, |(k : ℝ)*x r-z r| < 1) :
    highLocalCoordinates d k j x = highAffineChart d k z x := by
  funext r
  have he := highChartLift_eq_of_close k hk (j r) (x r) (z r) (hz r) (hc r)
  simp only [highLocalCoordinates, highLocalCoordinate, highRawChartCoordinate, he,
    if_pos (hc r).le, highAffineChart]

theorem highLocalCoordinates_patch_map_le {d k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (j : HighWindowLabels d k) :
    Measure.map (highLocalCoordinates d k j)
      ((cubeVolume d).restrict (highTorusPatch d k j)) ≤
      ENNReal.ofReal ((2 / (k : ℝ))^d) • volume.restrict (spatialPatchBox d) := by
  have hbox : MeasurableSet (spatialPatchBox d) := measurableSet_Icc
  let wrap (b : Fin d → Bool) : Fin d → ℤ :=
    fun r => if b r then (j r).val+(k : ℤ) else (j r).val
  apply Measure.le_iff.mpr; intro S hS
  have hcover : (highLocalCoordinates d k j ⁻¹' S ∩ highTorusPatch d k j) ∩ unitCube d ⊆
      ⋃ b : Fin d → Bool, highAffineChart d k (wrap b) ⁻¹' (S ∩ spatialPatchBox d) := by
    intro x hx
    obtain ⟨z, hz, hc⟩ := hx.1.2
    have hzcase (r : Fin d) : ∃ b : Bool,
        z r = if b then ((j r).val : ℤ)+(k : ℤ) else ((j r).val : ℤ) := by
      rcases highPatch_lift_cube_cases k hk (j r) (x r) (hx.2 r) (z r) (hz r) (hc r) with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    choose b hb using hzcase
    have hzb : z = wrap b := funext hb
    have he := highLocalCoordinates_eq_affine_on_patch hk j hx.1.2 z hz hc
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    change highAffineChart d k (wrap b) x ∈ S ∩ spatialPatchBox d
    rw [← hzb, ← he]
    refine ⟨hx.1.1, ?_⟩
    rw [he]
    exact ⟨fun r => (abs_lt.mp (hc r)).1.le, fun r => (abs_lt.mp (hc r)).2.le⟩
  rw [Measure.map_apply (highLocalCoordinates_measurable d k j) hS,
    Measure.restrict_apply ((highLocalCoordinates_measurable d k j) hS),
    cubeVolume, Measure.restrict_apply (((highLocalCoordinates_measurable d k j) hS).inter
      (highTorusPatch_measurableSet d k j)), Measure.smul_apply,
    Measure.restrict_apply hS, smul_eq_mul]
  calc
    _ ≤ volume (⋃ b : Fin d → Bool,
        highAffineChart d k (wrap b) ⁻¹' (S ∩ spatialPatchBox d)) := measure_mono hcover
    _ ≤ ∑' b : Fin d → Bool,
        volume (highAffineChart d k (wrap b) ⁻¹' (S ∩ spatialPatchBox d)) := measure_iUnion_le _
    _ = ∑ b : Fin d → Bool,
        ENNReal.ofReal (((k : ℝ)^d)⁻¹) * volume (S ∩ spatialPatchBox d) := by
      rw [tsum_fintype]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Measure.map_apply (highAffineChart_measurable d k _) (hS.inter hbox),
        highAffineChart_map_volume d k (by omega) _, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal ((2 / (k : ℝ))^d) * volume (S ∩ spatialPatchBox d) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [← mul_assoc]; congr 1
      rw [show (2 : ℝ≥0∞)^d = ENNReal.ofReal ((2 : ℝ)^d) by rw [ENNReal.ofReal_pow] <;> norm_num,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [div_pow]; ring

lemma fintype_probability_pi_restrict_withDensity {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f))
    (A : Set α) (hA : MeasurableSet A) :
    Measure.pi (fun _ : κ => (μ.withDensity f).restrict A) =
      (Measure.pi (fun _ : κ => μ.restrict A)).withDensity (fun x => ∏ i, f (x i)) := by
  let _ := hprob
  have hpi : Measure.pi (fun _ : κ => μ.withDensity f) =
      (Measure.pi (fun _ : κ => μ)).withDensity (fun x => ∏ i, f (x i)) := by
    apply Measure.pi_eq; intro s hs
    rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
    have he (x : κ → α) :
        (Set.pi Set.univ s).indicator (fun x => ∏ i, f (x i)) x =
          ∏ i, (s i).indicator f (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp [Set.indicator_of_mem, Set.mem_pi, h]
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hz : ∏ j, (s j).indicator f (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)
        rw [hz]
        apply Set.indicator_of_notMem
        simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
        exact not_forall.mpr ⟨i, hi⟩
    simp_rw [he]
    let G : κ → α → ℝ≥0∞ := fun i => (s i).indicator f
    have hG : ∀ i, Measurable (G i) := fun i => hf.indicator (hs i)
    change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi (fun _ : κ => μ)) = _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
      (iIndepFun_pi fun i => (hG i).aemeasurable) fun i => (hG i).comp (measurable_pi_apply i)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(measurePreserving_eval (fun _ : κ => μ) i).lintegral_comp (hG i)]
    change (∫⁻ b, (s i).indicator f b ∂μ) = _
    rw [lintegral_indicator (hs i), withDensity_apply f (hs i)]
  rw [← Measure.restrict_pi_pi (fun _ : κ => μ.withDensity f) (fun _ => A), hpi,
    restrict_withDensity (MeasurableSet.univ_pi fun _ => hA), Measure.restrict_pi_pi]

def selectedRawLikelihood {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ) (x : κ → α) (y : κ → Fin 3) : ℝ :=
  (∏ i, p (x i)) * ∏ i, q (x i) (y i)

def selectedConditionalScoreEnergy {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (∏ i, q (x i) (y i)) * (R x y / selectedRawLikelihood p q x y) ^ 2

def selectedRawSquareEnergy {κ α : Type*} [Fintype κ]
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (R x y) ^ 2

theorem selected_conditional_score_energy_nonneg {κ α : Type*} [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ) (hq : ∀ x y, 0 ≤ q x y)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) :
    0 ≤ selectedConditionalScoreEnergy p q R x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => hq _ _) (sq_nonneg _)

theorem normalized_selected_score_energy_integrable_bound {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (m pMinus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (p : α → ℝ) (hpMeas : Measurable p) (q : α → Fin 3 → ℝ)
    (hqMeas : ∀ y, Measurable fun x => q x y)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (hR : ∀ y, Measurable fun x => R x y)
    (hprob : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (p x / m)))
    (hp : ∀ x ∈ A, pMinus ≤ p x) (hq : ∀ x ∈ A, ∀ y, cMass ≤ q x y)
    (hRaw : Integrable (selectedRawSquareEnergy R) (Measure.pi fun _ : κ => μ.restrict A)) :
    Integrable (selectedConditionalScoreEnergy p q R)
      (Measure.pi fun _ : κ => (μ.withDensity fun z => ENNReal.ofReal (p z / m)).restrict A) ∧
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi fun _ : κ => (μ.withDensity fun z => ENNReal.ofReal (p z / m)).restrict A) ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ *
        ∫ x, selectedRawSquareEnergy R x ∂Measure.pi fun _ : κ => μ.restrict A := by
  have hm0 : 0 < m := hpMinus.trans_le hm
  have hpp (x : α) (hx : x ∈ A) : 0 < p x := hpMinus.trans_le (hp x hx)
  have hqp (x : α) (hx : x ∈ A) (y : Fin 3) : 0 < q x y := hcMass.trans_le (hq x hx y)
  let W : (κ → α) → ℝ := fun x => ∑ y : κ → Fin 3,
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
  have hWMeas : Measurable W := by
    refine Finset.measurable_sum _ fun y _ => ?_
    have hqm : Measurable fun x : κ → α => ∏ i, q (x i) (y i) :=
      Finset.measurable_prod _ fun i _ => (hqMeas (y i)).comp (measurable_pi_apply i)
    have hpm : Measurable fun x : κ → α => ∏ i, p (x i) :=
      Finset.measurable_prod _ fun i _ => hpMeas.comp (measurable_pi_apply i)
    unfold selectedRawLikelihood; fun_prop
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A), ∀ i, x i ∈ A :=
    ae_all_iff.mpr fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA)
  have hcancel : (fun x => (∏ i, ENNReal.ofReal (p (x i) / m)).toReal *
      selectedConditionalScoreEnergy p q R x) =ᵐ[Measure.pi fun _ : κ => μ.restrict A] W := by
    filter_upwards [hmem] with x hx
    rw [ENNReal.toReal_prod, show (∏ i, (ENNReal.ofReal (p (x i) / m)).toReal) = ∏ i, p (x i) / m from
      Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (div_nonneg (hpp _ (hx i)).le hm0.le)]
    unfold selectedConditionalScoreEnergy W
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hpP : (∏ i, p (x i)) ≠ 0 := ne_of_gt (Finset.prod_pos fun i _ => hpp _ (hx i))
    have hqP : (∏ i, q (x i) (y i)) ≠ 0 := ne_of_gt (Finset.prod_pos fun i _ => hqp _ (hx i) (y i))
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
    unfold selectedRawLikelihood
    field_simp [hpP, hqP, hm0.ne'] <;> ring
  have hWbound : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A),
      0 ≤ W x ∧ W x ≤ highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x := by
    filter_upwards [hmem] with x hx
    refine ⟨Finset.sum_nonneg fun y _ => ?_, ?_⟩
    · have hL : 0 < selectedRawLikelihood p q x y :=
        mul_pos (Finset.prod_pos fun i _ => hpp _ (hx i)) (Finset.prod_pos fun i _ => hqp _ (hx i) (y i))
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (pow_nonneg hm0.le _) hL.le)) (sq_nonneg _)
    · unfold W selectedRawSquareEnergy
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hprod : (pMinus ^ 2 * cMass) ^ Fintype.card κ ≤
          m ^ Fintype.card κ * selectedRawLikelihood p q x y := by
        calc
          _ = ∏ _i : κ, pMinus ^ 2 * cMass := by simp
          _ ≤ ∏ i, m * (p (x i) * q (x i) (y i)) :=
            Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => by
              have hpq := mul_le_mul (hp _ (hx i)) (hq _ (hx i) (y i)) hcMass.le (hpp _ (hx i)).le
              have hh := mul_le_mul hm hpq (mul_nonneg hpMinus.le hcMass.le) hm0.le
              nlinarith
          _ = _ := by unfold selectedRawLikelihood; simp [Finset.prod_mul_distrib]
      have hleft : 0 < (pMinus ^ 2 * cMass) ^ Fintype.card κ := by positivity
      unfold highFixedScoreDenominator; rw [inv_pow]
      exact (inv_le_inv₀ (hleft.trans_le hprod) hleft).mpr hprod
  have hJ := hRaw.const_mul (highFixedScoreDenominator pMinus cMass ^ Fintype.card κ)
  have hWI : Integrable W (Measure.pi fun _ : κ => μ.restrict A) :=
    hJ.mono' hWMeas.aestronglyMeasurable <| hWbound.mono fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hf : Measurable fun x => ENNReal.ofReal (p x / m) :=
    ENNReal.measurable_ofReal.comp (hpMeas.div_const m)
  have hfP : Measurable fun x : κ → α => ∏ i, ENNReal.ofReal (p (x i) / m) :=
    Finset.measurable_prod _ fun i _ => hf.comp (measurable_pi_apply i)
  have hlt : ∀ᵐ x : κ → α ∂Measure.pi (fun _ : κ => μ.restrict A),
      (∏ i : κ, ENNReal.ofReal (p (x i) / m)) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  rw [fintype_probability_pi_restrict_withDensity μ _ hf hprob A hA]
  refine ⟨(integrable_withDensity_iff_integrable_smul' hfP hlt).mpr (hWI.congr hcancel.symm), ?_⟩
  have he := integral_withDensity_eq_integral_toReal_smul
    (μ := Measure.pi fun _ : κ => μ.restrict A) hfP hlt (selectedConditionalScoreEnergy p q R)
  change (∫ x, selectedConditionalScoreEnergy p q R x
    ∂(Measure.pi fun _ : κ => μ.restrict A).withDensity fun x => ∏ i, ENNReal.ofReal (p (x i) / m)) =
      ∫ x, (∏ i, ENNReal.ofReal (p (x i) / m)).toReal * selectedConditionalScoreEnergy p q R x
        ∂Measure.pi fun _ : κ => μ.restrict A at he
  rw [he, integral_congr_ae hcancel]
  exact (integral_mono_ae hWI hJ (hWbound.mono fun _ hx => hx.2)).trans_eq (integral_const_mul _ _)

lemma high_marked_local_score_ratio {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    {n : ℕ} (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : Fin n → ℝ) (pReset : E → Fin n → ℝ)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      (∫ z, activation z * (∏ i, pReset z i / p i) *
        ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i) ∂π) -
      η ^ 2 * ∑ i, (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i)) := by
  have hpP : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hpd i
  have hqP : highResponseProduct a V η g w φ c y ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i _ => hp i (y i))
  unfold highMarkedLocalScore highMarkedResponseAction
  rw [sub_div, ← integral_div]
  have hfirst : (fun z => activation z * (∏ i, pReset z i) *
      highResponseProduct a V η g w φ (cReset z) y /
        ((∏ i, p i) * highResponseProduct a V η g w φ c y)) =
      fun z => activation z * (∏ i, pReset z i / p i) *
        ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i) := by
    funext z; simp only [Finset.prod_div_distrib]; unfold highResponseProduct; field_simp [hpP, hqP]
  rw [hfirst]; congr 1
  calc
    _ = η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
        highResponseProduct a V η g w φ c y) := by field_simp [hpP, hqP]
    _ = _ := by
      simp_rw [Finset.sum_div, mul_div_assoc,
        high_response_variance_ratio a V η g w φ c y _ fun i => hp i (y i)]

theorem high_marked_selected_response_energy {ι E : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace E] {n r : ℕ} (e : Fin r ↪ Fin n)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha
        fun b => (hp i b).le)) =
    ∫ y, highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
      ∂Measure.pi (fun l => ternaryIndexMeasure a
        (coefficientRegression η (g ∘ e) (w ∘ e) (φ ∘ e) c l) V ha fun b => (hp (e l) b).le) := by
  let μ (i : Fin n) := ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha fun b => (hp i b).le
  have hpres : MeasurePreserving (fun y : Fin n → Fin 3 => fun l => y (e l))
      (Measure.pi μ) (Measure.pi fun l => μ (e l)) := by
    have hc : iIndepFun (fun j (y : Fin n → Fin 3) => y j) (Measure.pi μ) :=
      iIndepFun_pi (X := fun _ : Fin n => (id : Fin 3 → Fin 3)) fun _ => aemeasurable_id
    refine ⟨measurable_pi_iff.mpr fun l => measurable_pi_apply (e l), ?_⟩
    simpa only [(measurePreserving_eval μ _).map_eq] using
      (iIndepFun_iff_map_fun_eq_pi_map fun l => (measurable_pi_apply (e l)).aemeasurable).mp
        (iIndepFun.precomp e.injective hc)
  let H : (Fin r → Fin 3) → ℝ := fun y =>
    highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
  have hsel (y : Fin n → Fin 3) :
      highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
        highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
          cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) := by
    rw [high_marked_local_score_ratio π activation a V η p pReset cReset g w φ c y hpd hp,
      high_marked_local_score_ratio π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
        cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) (fun l => hpd (e l)) fun l b => hp (e l) b]
    have hprod (z : E) :
        (∏ i, pReset z i / p i) *
            ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
              ternaryMass a (coefficientRegression η g w φ c i) V (y i) =
        (∏ l : Fin r, pReset z (e l) / p (e l)) *
            ∏ l : Fin r, ternaryMass a (coefficientRegression η g w φ (cReset z) (e l)) V (y (e l)) /
              ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.prod_map]
      have ho : (∏ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e,
          (pReset z i / p i) *
            (ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
              ternaryMass a (coefficientRegression η g w φ c i) V (y i))) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        have hiS := (Finset.mem_sdiff.mp hi).2
        have hv : coefficientRegression η g w φ (cReset z) i = coefficientRegression η g w φ c i := by
          simp [coefficientRegression, hw i hiS]
        rw [hReset z i hiS, div_self (hpd i), hv, div_self (hp i (y i)).ne', one_mul]
      rw [ho, one_mul]
    have hsum : (∑ i, (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i))) =
        ∑ l : Fin r, (w (e l)) ^ 2 * (ternaryVarianceDerivative a (y (e l)) /
          ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l))) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.sum_map,
        Finset.sum_eq_zero fun i hi => by simp [hw i (Finset.mem_sdiff.mp hi).2], zero_add]
    simp_rw [mul_assoc, hprod, hsum]; rfl
  calc
    _ = ∫ y, H (fun l => y (e l)) ∂Measure.pi μ :=
      integral_congr_ae <| Filter.Eventually.of_forall fun y => congrArg (· ^ 2) (hsel y)
    _ = ∫ y, H y ∂Measure.pi (fun l => μ (e l)) :=
      (integral_map hpres.measurable.aemeasurable (measurable_of_countable H).aestronglyMeasurable).symm.trans
        (congrArg (fun M => ∫ y, H y ∂M) hpres.map_eq)
    _ = _ := rfl

end PatchAndSelection

-- ============================================================================
-- 3. Complete Source Rows, Mass Annihilation, Tensor Tail, and Invariant Mass
-- ============================================================================

section CompleteSourceAndMass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

theorem high_source_interval_numeric {d : ℕ} (C : ModelConstants d) (M : ℝ)
    (hM : highCenterResolutionThreshold C ≤ M) :
    0 < C.densityLower+1/M ∧ C.densityLower+1/M < C.densityUpper-1/M := by
  have hg := highCenterResolution_guards C M hM
  have hM0 : 0 < M := by linarith [hg.1]
  exact ⟨by linarith [C.densityLower_pos, one_div_pos.mpr hM0],
    by linarith [hg.2, highCenterRadius_pos C, (highCenterRadius_le_margins C).1,
      (highCenterRadius_le_margins C).2]⟩

def completeSourceRows {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (Cfr lam ℓ N μ : ℝ) :=
  sourceRowData d k D M q (C.densityLower+1/(M : ℝ))
    (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ

lemma singletonRowSource_guards {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr : ℝ) (hCfr : 1 ≤ Cfr) :
    HighUnionSourceGuards C (M : ℝ) Cfr
      (singletonRowData d k D q (C.densityLower+1/(M : ℝ)) (C.densityUpper-1/(M : ℝ)) Cfr) := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hCf : 0 < Cfr := by linarith
  have hpos := singletonRowMass_positive d D q hq a b ha hab Cfr hCf
  let A := fun _ : Unit => finePairUnitMatrix d D
  have hA : ∀ i j, Measurable fun ζ : Unit => A ζ i j := fun _ _ => measurable_const
  have hc : Integrable (separatedMatrixCost A) (Measure.dirac ()) := by simp [A, separatedMatrixCost]
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => singletonRow_probability d k D q hq a b ha hab Cfr hCf
    mass_nonneg := fun _ => hpos.le
    total_positive := by simpa [highRowTotalMass, singletonRowData, a, b] using hpos
    activation_measurable := fun _ => absoluteActivation_measurable _ _
      (highPacketMarkWeight_measurable a b D 1 D q Cfr A hA)
    activation_bound := fun _ => highPacketActivation_bound (Measure.dirac ()) a b D 1 D q Cfr A
    activation_centered := fun _ => highPacketActivation_centered (Measure.dirac ()) a b D 1 D q Cfr A hA hc hpos
    slope_measurable := fun _ _ => (highPacketSlope_measurable a b D 1 D q
      (fun _ : Unit => fun _ => (1 : ℝ)) fun _ => measurable_const).comp measurable_fst
    slope_integrable := fun _ _ _ => highPacketSlope_integrable (Measure.dirac ()) a b ha hab D 1 D q
      (by norm_num) Cfr A hA hc hpos (fun _ : Unit => fun _ => (1 : ℝ)) (fun _ => measurable_const)
      (by intro _ _; norm_num)
    slope_centered := fun _ _ _ => highPacketAbsoluteLaw_slope_integral_zero (Measure.dirac ()) a b ha hab
      D 1 D q (by norm_num) Cfr A hA hc hpos (fun _ : Unit => fun _ => (1 : ℝ))
      (fun _ => measurable_const) (by intro _ _; norm_num)
    intercept_measurable := fun _ => highPacketIntercept_measurable a b D 1 D q
    intercept_interval := fun _ e => (densityPacketAtom_mem a b hab.le D 1 D e.2.1).1
    row_reset_interval := fun _ _ e _ v hv => by
      have hh := localDensityReset_mem_interval a b ha hab 1 (by norm_num)
        (densityPacketAtom a b D 1 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 1 D e.2.1).1
        (densityPacketAtom a b D 1 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 1 D e.2.1).2
        (fun _ : Unit => v) (fun _ _ => (1 : ℝ)) () hv (by intro _; norm_num)
      convert hh using 1 <;> dsimp [singletonRowData, highPacketSlope, highPacketIntercept, localDensityReset] <;> ring
    vector_measurable := fun _ γ =>
      (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 1 D q =>
        (highResponseMarkAtom Cfr q h.2).2 γ).comp measurable_snd
    time_measurable := fun _ =>
      (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) D 1 D q =>
        (highResponseMarkAtom (ι := HighFrameIndex d D) 0 q h.2).1).comp measurable_snd
    vector_ball := fun _ _ => covarianceAtom_mem_ball Cfr hCf _ _ _ _
    time_interval := fun _ _ => responseNode_mem_unit q _ }

theorem HighUnionSourceGuards.restrict {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] {C : ModelConstants d} {M Cfr : ℝ}
    {R : HighUnionRowData d k F I E} (G : HighUnionSourceGuards C M Cfr R)
    (i : I) (hpos : 0 < R.rowMass i) :
    HighUnionSourceGuards C M Cfr (highUnionRowRestrict R i) where
  resolution := G.resolution
  frame := G.frame
  row_probability := fun _ => G.row_probability i
  mass_nonneg := fun _ => G.mass_nonneg i
  total_positive := by simpa [highRowTotalMass, highUnionRowRestrict] using hpos
  activation_measurable := fun _ => G.activation_measurable i
  activation_bound := fun _ => G.activation_bound i
  activation_centered := fun _ => G.activation_centered i
  slope_measurable := fun j _ => G.slope_measurable j i
  slope_integrable := fun j x _ => G.slope_integrable j x i
  slope_centered := fun j x _ => G.slope_centered j x i
  intercept_measurable := fun _ => G.intercept_measurable i
  intercept_interval := fun _ => G.intercept_interval i
  row_reset_interval := fun j _ => G.row_reset_interval j i
  vector_measurable := fun _ => G.vector_measurable i
  time_measurable := fun _ => G.time_measurable i
  vector_ball := fun _ => G.vector_ball i
  time_interval := fun _ => G.time_interval i

theorem completeSourceRows_guards {d : ℕ} (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N) :
    HighUnionSourceGuards C (M : ℝ) Cfr (completeSourceRows C k D M q Cfr lam ℓ N μ) := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hCf : 0 < Cfr := by linarith
  have hcomp (i : SourceRowIndex d D M q a b Cfr lam ℓ N μ) :
      HighUnionSourceGuards C (M : ℝ) Cfr (sourceRowComponent d k D M q a b Cfr lam ℓ N μ i) := by
    cases i with
    | inl p =>
      exact (finePairSourceRows_guards C k D M q hD hq hM Cfr hCfr ℓ N hℓ hℓN).restrict p
        (finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf ℓ N hℓ hℓN p)
    | inr i =>
      cases i with
      | inl _ => exact singletonRowSource_guards C k D M q hq hM Cfr hCfr
      | inr i =>
        exact higherBandSourceRow_guards C k (higherBandFamilyTarget i.val)
          (higherBandFamilyGuardDegree M i.val) D q
          (by have hh := (higherBandFamily_target_bounds d D M q a b Cfr lam ℓ N μ i).1; omega)
          (M : ℝ) Cfr lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2 hM hCfr
          i.property.1 i.property.2.2.2
  exact {
    resolution := hM
    frame := hCfr
    row_probability := fun i => (hcomp i).row_probability ()
    mass_nonneg := fun i => (hcomp i).mass_nonneg ()
    total_positive := sourceRowTotalMass_positive d k D M q hq a b ha hab Cfr hCf lam ℓ N μ
    activation_measurable := fun i => (hcomp i).activation_measurable ()
    activation_bound := fun i => (hcomp i).activation_bound ()
    activation_centered := fun i => (hcomp i).activation_centered ()
    slope_measurable := fun j i => (hcomp i).slope_measurable j ()
    slope_integrable := fun j x i => (hcomp i).slope_integrable j x ()
    slope_centered := fun j x i => (hcomp i).slope_centered j x ()
    intercept_measurable := fun i => (hcomp i).intercept_measurable ()
    intercept_interval := fun i => (hcomp i).intercept_interval ()
    row_reset_interval := fun j i => (hcomp i).row_reset_interval j ()
    vector_measurable := fun i => (hcomp i).vector_measurable ()
    time_measurable := fun i => (hcomp i).time_measurable ()
    vector_ball := fun i => (hcomp i).vector_ball ()
    time_interval := fun i => (hcomp i).time_interval () }

abbrev SourceRowDensityMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowDensityMark d D M p
  | .inr (.inl _) => Unit × HighDensityMarkIndex D 1 D
  | .inr (.inr i) => HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2 ×
      HighDensityMarkIndex (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D

instance sourceRowDensityMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (SourceRowDensityMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => infer_instance
  | inr i => cases i <;> dsimp [SourceRowDensityMark] <;> infer_instance

def sourceRowDensityProj (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowMark d D M q a b C lam ℓ N μ i → SourceRowDensityMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowDensityProj d D M q p
  | .inr (.inl _) => fun e => (e.1, e.2.1)
  | .inr (.inr _) => fun e => (e.1, e.2.1)

def sourceRowDensityLift (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowDensityMark d D M q a b C lam ℓ N μ i → SourceRowMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowWithResponse d D M q p r
  | .inr (.inl _) => fun e => (e.1, (e.2, r))
  | .inr (.inr _) => fun e => (e.1, (e.2, r))

theorem sourceRowDensityLift_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    Measurable (sourceRowDensityLift d D M q a b C lam ℓ N μ r i) := by
  cases i with
  | inl p => exact finePairRowWithResponse_measurable d D M q p r
  | inr i => cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

theorem sourceRow_density_projection_slope (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) (j : HighWindowLabels d k)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (e : SourceRowMark d D M q a b C lam ℓ N μ i) (x : Covariate d) :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i e x =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i
      (sourceRowDensityLift d D M q a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) x := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

theorem sourceRow_density_projection_intercept (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (e : SourceRowMark d D M q a b C lam ℓ N μ i) :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i e =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i
      (sourceRowDensityLift d D M q a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

theorem sourceRow_density_observable_zero (d : ℕ) [NeZero d] (k D M q : ℕ)
    (a b C lam ℓ N μ : ℝ)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (H : SourceRowDensityMark d D M q a b C lam ℓ N μ i → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : ∀ z, ‖H z‖ ≤ B) :
    (∫ e, (sourceRowData d k D M q a b C lam ℓ N μ).rowActivation i e *
      H (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)
      ∂(sourceRowData d k D M q a b C lam ℓ N μ).rowLaw i) = 0 := by
  cases i with
  | inl p =>
    exact finePairRow_density_observable_zero d D M q a b C ℓ N
      (fun p => hpos (Sum.inl p)) p H hH B hB
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacketAbsoluteLaw_density_observable_zero (Measure.dirac ()) a b D 1 D q C
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inr (.inl ()))) H hH B hB
    | inr i =>
      exact higherBandRow_density_observable_zero d (higherBandFamilyTarget i.val)
        (higherBandFamilyGuardDegree M i.val) D q a b C lam ℓ
        (higherBandFamilyUpper d ℓ N μ i.val) i.val.2 i.property.1
        (hpos (.inr (.inr i))) H hH B hB

theorem sourceRowMass_positive_actual (d : ℕ) [NeZero d] (k D M q : ℕ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (C : ℝ) (hC : 0 < C) (lam ℓ N μ : ℝ) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p => exact finePairRowMass_positive d D hD M q hq a b ha hab C hC ℓ N hℓ hℓN p
  | inr i =>
    cases i with
    | inl _ => exact singletonRowMass_positive d D q hq a b ha hab C hC
    | inr i => exact higherBandFamily_mass_positive d k D M q a b C lam ℓ N μ i

theorem completeSourceMass_append_indicator_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ))) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ)
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
      highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C) e
      ∂highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)) = 0 := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let E := SourceRowMark d D M q a b Cfr lam ℓ N μ
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hG := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr (by linarith) lam ℓ N μ hℓ hℓN
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((⟨fun _ => 0, by simp⟩, ⟨fun _ => 0, by simp⟩), (false, false), 0)
  let proj := sourceRowDensityProj d D M q a b Cfr lam ℓ N μ
  let lift := sourceRowDensityLift d D M q a b Cfr lam ℓ N μ r₀
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  let Fobs : HighUnionMark E → ℝ := fun e => S.indicator (fun _ : ℝ => (1 : ℝ))
    (highUnionSourceMass C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)))
  have hF : Measurable Fobs := (measurable_const.indicator hS).comp
    ((highUnionSourceMass_measurable C R hG).comp
      ((historyMarkedAppend_measurable _ _ j).comp (measurable_const.prodMk measurable_id)))
  have hFbound (e) : ‖Fobs e‖ ≤ 1 :=
    (norm_indicator_le_norm_self (s := S) (fun _ : ℝ => (1 : ℝ)) _).trans_eq (by simp)
  have hrow (i) : (∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i, e⟩) ∂(R.rowLaw i)) = 0 := by
    let Hi := fun z => Fobs (Sum.inl ⟨i, lift i z⟩)
    have hHi : Measurable Hi := hF.comp (measurable_inl.comp ((rowSigmaMk_measurable i).comp
      (sourceRowDensityLift_measurable d D M q a b Cfr lam ℓ N μ r₀ i)))
    have hf (e : E i) : Fobs (Sum.inl ⟨i, e⟩) = Hi (proj i e) := by
      refine congrArg (S.indicator fun _ : ℝ => (1 : ℝ)) (integral_congr_ae <| Filter.Eventually.of_forall fun x => ?_)
      change (highUnionSourceState C R _).1 x = (highUnionSourceState C R _).1 x
      rw [highUnionSourceState_append, highUnionSourceState_append]
      change (if x ∈ highTorusPatch d k j then (sourceRowData d k D M q a b Cfr lam ℓ N μ).rowSlope j i e x * _ +
          (sourceRowData d k D M q a b Cfr lam ℓ N μ).rowIntercept i e else _) =
        (if x ∈ highTorusPatch d k j then (sourceRowData d k D M q a b Cfr lam ℓ N μ).rowSlope j i (lift i (proj i e)) x * _ +
          (sourceRowData d k D M q a b Cfr lam ℓ N μ).rowIntercept i (lift i (proj i e)) else _)
      rw [sourceRow_density_projection_slope d k D M q a b Cfr lam ℓ N μ r₀ j i e x,
        sourceRow_density_projection_intercept d k D M q a b Cfr lam ℓ N μ r₀ i e]
    calc
      _ = ∫ e, R.rowActivation i e * Hi (proj i e) ∂(R.rowLaw i) :=
        integral_congr_ae <| Filter.Eventually.of_forall fun e => congrArg _ (hf e)
      _ = 0 := sourceRow_density_observable_zero d k D M q a b Cfr lam ℓ N μ hpos i Hi hHi 1 fun _ => hFbound _
  change (∫ e, Fobs e * highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0
  calc
    _ = ∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C) :=
      integral_congr_ae <| Filter.Eventually.of_forall fun _ => mul_comm _ _
    _ = ∑ i, ∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i, e⟩) ∂(R.rowLaw i) :=
      highUnionSource_bounded_action C R hG hpos Fobs hF 1 hFbound
    _ = 0 := by simp only [hrow, Finset.sum_const_zero]

section TensorRowTail
variable {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
include hn hC ha hη hρ hηρ hpPlus

lemma responseTensor_reference_all_count_bound
    {ι J Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace Z] (σ : Measure Z) [IsFiniteMeasure σ]
    (weights : J → ℝ) (A : Z → ι → ι → ℝ)
    (hm : Measurable fun e : Z × (J × HighResponseMarkIndex ι q) => weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2)
    (hi : Integrable (fun e : Z × (J × HighResponseMarkIndex ι q) => weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2) (σ.prod Measure.count))
    (hpos : 0 < signedMarkMass (σ.prod Measure.count) fun e : Z × (J × HighResponseMarkIndex ι q) => weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2)
    (pReset : Z → J → Fin n → ℝ)
    (hmReset : ∀ e i, Measurable fun ζ => pReset ζ e i)
    (hReset : ∀ ζ e i, |pReset ζ e i| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ → ∀ i, |∑ γ, φ i γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y)
    (y : Fin n → Fin 3) :
    |highMarkedResponseAction
      (absoluteMarkLaw (σ.prod Measure.count) fun e : Z × (J × HighResponseMarkIndex ι q) => weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2)
      (absoluteActivation (σ.prod Measure.count) fun e : Z × (J × HighResponseMarkIndex ι q) => weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2) a V η
      (fun e => pReset e.1 e.2.1)
      (fun e => coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
      g w φ y| ≤
      (pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2) *
        signedMarkMass (σ.prod Measure.count) fun e : Z × (J × HighResponseMarkIndex ι q) => weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2 := by
  let ν : Measure (Z × (J × HighResponseMarkIndex ι q)) := σ.prod Measure.count
  let W : Z × (J × HighResponseMarkIndex ι q) → ℝ := fun e => weights e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2
  let Φ : (ι → ℝ) → ℝ := fun v => highResponseProduct a V η g w φ v y
  let O : Z × (J × HighResponseMarkIndex ι q) → ℝ := fun e => (∏ i, pReset e.1 e.2.1 i) *
    Φ (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1)
  let K := pPlus^n * highSeparatedDerivativeBudget a ρ * (n : ℝ)^2 * η^2
  have hO : Measurable O :=
    (Finset.measurable_fun_prod _ fun i _ => measurable_from_prod_countable_left fun e => hmReset e.1 i).mul
      (highMarkedResponseProduct_measurable a V η _ (fun γ =>
        (measurable_of_countable fun e : J × HighResponseMarkIndex ι q =>
          coefficientReset c (highResponseMarkAtom C q e.2).2 (highResponseMarkAtom C q e.2).1 γ).comp measurable_snd) g w φ y)
  have hΦ (r : HighResponseMarkIndex ι q) :
      |Φ (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1)| ≤ 1 := by
    have hb := coefficientReset_mem_ball C c (highResponseMarkAtom C q r).2
      (highResponseMarkAtom C q r).1 (responseNode_mem_unit q r.2.2) hc
      (covarianceAtom_mem_ball C hC _ _ _ _)
    refine highMarkedResponseProduct_abs_le_one a V η ha.ne' g w φ _ (fun i _ => hp _ ?_ _) y
    have hprof := hφ _ hb i
    change |g i+η*w i*(∑ γ, φ i γ*coefficientReset c
      (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1 γ)| ≤ ρ
    have hh : |η*w i*(∑ γ, φ i γ*coefficientReset c
        (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1 γ)| ≤ η := by
      rw [abs_mul, abs_mul, abs_of_nonneg hη]
      have := mul_le_mul (hw i) hprof (abs_nonneg _) zero_le_one
      nlinarith [mul_le_mul_of_nonneg_left this hη]
    exact (abs_add_le _ _).trans (by linarith [hg i])
  have hOb (e) : ‖O e‖ ≤ pPlus^n := by
    change |(∏ i, pReset e.1 e.2.1 i)*Φ _| ≤ _; rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ pPlus hpPlus (hReset e.1 e.2.1))
      (hΦ e.2.2) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hWO := hi.mul_bdd hO.aestronglyMeasurable (Filter.Eventually.of_forall hOb)
  have hSlice (ζ) : |∫ e : J × HighResponseMarkIndex ι q, W (ζ, e)*O (ζ, e) ∂Measure.count| ≤
      K * ∫ e : J × HighResponseMarkIndex ι q, |W (ζ, e)| ∂Measure.count := by
    simp only [integral_count, W, O, Φ, K, ← mul_assoc]
    have he : (∑ e : J × HighResponseMarkIndex ι q,
        weights e.1 * highResponseMarkWeight C q (A ζ) e.2 * (∏ i, pReset ζ e.1 i) *
          highResponseProduct a V η g w φ
            (coefficientReset c (highResponseMarkAtom C q e.2).2 (highResponseMarkAtom C q e.2).1) y) =
        highDensityResponseAction q C weights (fun _ => A ζ) c
          (fun e => ∏ i, pReset ζ e i) (fun v => highResponseProduct a V η g w φ v y) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [show ∀ r : HighResponseMarkIndex ι q,
        weights e * highResponseMarkWeight C q (A ζ) r * (∏ i, pReset ζ e i) *
          highResponseProduct a V η g w φ (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1) y =
        (weights e * ∏ i, pReset ζ e i) * (highResponseMarkWeight C q (A ζ) r *
          highResponseProduct a V η g w φ (coefficientReset c (highResponseMarkAtom C q r).2 (highResponseMarkAtom C q r).1) y)
        from fun _ => by ring, ← Finset.mul_sum]
      rw [highResponseMark_action q C (A ζ) c fun v => highResponseProduct a V η g w φ v y]
    rw [he]
    apply (high_density_response_product_abs_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
      weights (fun _ => A ζ) (pReset ζ) g w φ c hc hg hw hφ hp (hReset ζ) y).trans_eq
    rw [Fintype.sum_prod_type]
    simp only [abs_mul]
    simp_rw [← Finset.mul_sum]
    rw [highResponseMark_variation q C (A ζ)]
    unfold highResponsePacketCost highLocalDerivativeConstant highSeparatedDerivativeBudget
    rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
  unfold highMarkedResponseAction
  have he : (fun e : Z × (J × HighResponseMarkIndex ι q) => absoluteActivation ν W e * (∏ i, pReset e.1 e.2.1 i) *
      highResponseProduct a V η g w φ
        (coefficientReset c (highResponseMarkAtom C q e.2.2).2 (highResponseMarkAtom C q e.2.2).1) y) =
      fun e => absoluteActivation ν W e * O e := by funext e; dsimp [O, Φ]; ring
  rw [he, absoluteMarkLaw_activation_integral ν W hm hpos O, integral_prod _ hWO]
  exact abs_integral_le_integral_abs.trans <|
    (integral_mono hWO.integral_prod_left.abs (hi.abs.integral_prod_left.const_mul K) hSlice).trans_eq <| by
      rw [integral_const_mul, ← integral_prod _ hi.abs]; rfl

end TensorRowTail

theorem sourceRow_reference_all_count_bound {n : ℕ}
    (d : ℕ) [NeZero d] (k D M q : ℕ) (hn : 1 ≤ n)
    (ad bd C lam ℓ N μ a V η ρ pPlus : ℝ)
    (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q ad bd C lam ℓ N μ)
    (reset : SourceRowDensityMark d D M q ad bd C lam ℓ N μ i → Fin n → ℝ)
    (hmReset : ∀ u, Measurable fun e => reset e u)
    (hReset : ∀ e u, |reset e u| ≤ pPlus)
    (g w : Fin n → ℝ) (φ : Fin n → HighFrameIndex d D → ℝ)
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : Fin n → Fin 3) :
    |highMarkedResponseAction ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowLaw i)
      ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowActivation i) a V η
      (fun e => reset (sourceRowDensityProj d D M q ad bd C lam ℓ N μ i e))
      (fun e => coefficientReset c
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowVector i e)
        ((sourceRowData d k D M q ad bd C lam ℓ N μ).rowTime i e)) g w φ y| ≤
      (pPlus^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i := by
  have hpkt : ∀ {Z : Type} [MeasurableSpace Z] (σ : Measure Z) [IsFiniteMeasure σ] (m r : ℕ)
      (A : Z → HighFrameIndex d D → HighFrameIndex d D → ℝ)
      (hA : ∀ γ δ, Measurable fun ζ => A ζ γ δ)
      (hcost : Integrable (separatedMatrixCost A) σ)
      (hp0 : 0 < highPacketMarkMass σ ad bd m r D q C A)
      (res : Z × HighDensityMarkIndex m r D → Fin n → ℝ)
      (hmR : ∀ u, Measurable fun e => res e u) (hbR : ∀ e u, |res e u| ≤ pPlus),
      |highMarkedResponseAction (highPacketAbsoluteLaw σ ad bd m r D q C A)
        (highPacketActivation σ ad bd m r D q C A) a V η
        (fun e => res (e.1, e.2.1))
        (fun e => coefficientReset c (highResponseMarkAtom C q e.2.2).2
          (highResponseMarkAtom 0 q e.2.2).1) g w φ y| ≤
        (pPlus^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
          highPacketMarkMass σ ad bd m r D q C A := by
    intro Z _ σ _ m r A hA hcost hp0 res hmR hbR
    exact responseTensor_reference_all_count_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus σ
      (densityPacketWeight ad bd m r D) A
      (highPacketMarkWeight_measurable ad bd m r D q C A hA)
      (highPacketMarkWeight_integrable σ ad bd m r D q C A hA hcost) hp0
      (fun ζ e => res (ζ, e)) (fun e u => (hmR u).comp (measurable_id.prodMk measurable_const))
      (fun ζ e u => hbR (ζ, e) u) g w φ c hc hg hw hφ hp y
  cases i with
  | inl p =>
    cases p
    · exact hpkt (Measure.dirac ()) D 2 (fun _ => finePairUnitMatrix d D)
        (fun _ _ => measurable_const) (integrable_const _) (hpos (.inl .unit)) reset hmReset hReset
    · exact hpkt (finePairTimeFieldMeasure d 0 ℓ) D 2 (finePairTimeMatrix d (finePairDistanceMatrix d D))
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _)
        (hpos (.inl .coarse)) reset hmReset hReset
    · exact responseTensor_reference_all_count_bound q hn C a V η ρ pPlus hC ha hη hρ hηρ hpPlus
        (finePairTimeFieldMeasure d ℓ N) (finePairDensityWeight ad bd M)
        (finePairTimeMatrix d (finePairDistanceMatrix d D))
        (finePairPacketWeight_measurable ad bd M q C _ (finePairTimeMatrix_measurable d _))
        (finePairPacketWeight_integrable _ ad bd M q C _ (finePairTimeMatrix_measurable d _)
          (finePairTimeMatrix_cost_integrable d ℓ N _))
        (hpos (.inl .fine)) (fun ζ e => reset (ζ, e))
        (fun e u => (hmReset u).comp (measurable_id.prodMk measurable_const))
        (fun ζ e u => hReset (ζ, e) u) g w φ c hc hg hw hφ hp y
  | inr i =>
    cases i with
    | inl _ =>
      exact hpkt (Measure.dirac ()) D 1 (fun _ => finePairUnitMatrix d D)
        (fun _ _ => measurable_const) (integrable_const _) (hpos (.inr (.inl ()))) reset hmReset hReset
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := higherBandFamilyGuardDegree M i.val
      let T := higherBandFamilyUpper d ℓ N μ i.val
      letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
      exact hpkt (higherBandCarrierMeasure d r ℓ T i.val.2) m r
        (higherBandCarrierAmplitude d r D lam i.val.2)
        (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
        (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2)
        (hpos (.inr (.inr i))) reset hmReset hReset

section UnionMassAndInvariant
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
  [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)
  {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

lemma highUnionSourceMass_abs_le_upper (h) : |highUnionSourceMass C R h| ≤ C.densityUpper := by
  have hp := highUnionSourceMass_interval C R G h
  have hM0 : 0 < M := by linarith [(highCenterResolution_guards C M G.resolution).1]
  rw [abs_of_nonneg (by linarith [hp.1, C.densityLower_pos, one_div_pos.mpr hM0])]
  linarith [hp.2, one_div_pos.mpr hM0]

theorem highUnionSourceMass_reference_mean_one :
    (∫ h, highUnionSourceMass C R h
      ∂historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) = 1 := by
  letI := highUnionSourceLaw_probability C R G
  exact historyMarkedReference_mean_one (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (3^d) (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C)) (highUnionSourceMass C R)
    (highUnionSourceMass_measurable C R G) C.densityUpper
    (highUnionSourceMass_abs_le_upper C R G) (highUnionSourceMass_fiber_mean_one C R G)

theorem highUnionSourceMass_reference_mgf (hk : 2 ≤ k) (u : ℝ) :
    (∫ h, Real.exp (u * (highUnionSourceMass C R h-1))
      ∂historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) ≤
      Real.exp (highHistoryMassParameter d k C.densityLower C.densityUpper * u^2) := by
  letI := highUnionSourceLaw_probability C R G
  have hgap : 0 ≤ C.densityUpper-C.densityLower := by
    linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have h := historyMarkedReference_mass_mgf (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (3^d) (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C)) (highUnionSourceMass C R)
    (highUnionSourceMass_measurable C R G) C.densityUpper
    ((2 / (k : ℝ))^d * (C.densityUpper-C.densityLower)) (by positivity)
    (highUnionSourceMass_abs_le_upper C R G) (highUnionSourceMass_fiber_mean_one C R G)
    (fun g j marks marks' hMarks => highUnionSourceMass_block_oscillation C R G hk g marks marks' j hMarks) u
  convert h using 1; congr 1
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
  unfold highHistoryMassParameter; ring

variable (hpos : ∀ i, 0 < R.rowMass i)
include hpos

theorem highUnionSourceActivation_bound (e : HighUnionMark E) :
    |highUnionActivation R (highCenterMix C) e| ≤
      highRowTotalMass R.rowMass / highCenterMix C :=
  highCenteredRowUnionActivation_bound R.rowMass hpos G.total_positive R.rowActivation
    G.activation_bound _ (highCenterMix_mem C).1 e

theorem highUnionSourceActivation_centered :
    (∫ e, highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0 := by
  letI := G.row_probability
  exact highUnionActivation_centered R G.mass_nonneg G.activation_measurable
    (fun i => Integrable.of_bound (G.activation_measurable i).aestronglyMeasurable (R.rowMass i)
      (Filter.Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using G.activation_bound i e))
    G.activation_centered _ (highCenterMix_mem C).1 (highCenterMix_mem C).2.le

theorem highUnionSourcePrior_probability (T : ℝ) (_hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))) := by
  letI := highUnionSourceLaw_probability C R G
  have hB : 0 ≤ highRowTotalMass R.rowMass / highCenterMix C :=
    div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hi : Integrable (highUnionActivation R (highCenterMix C)) (highUnionLaw R (highCenterMix C)) :=
    Integrable.of_bound (highUnionActivation_measurable R G.activation_measurable (highCenterMix C)).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun e => by
        simpa only [Real.norm_eq_abs] using highUnionSourceActivation_bound C R G hpos e)
  exact historyMarkedPrior_probability _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    t _ ht.1 hB _ _ hi (highUnionSourceActivation_centered C R G hpos)
    (highUnionSourceActivation_bound C R G hpos)
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB)
      (historyReferenceRho_pos _).le).trans hsmall)

theorem highUnionSourceMass_prior_law_of_append_annihilation (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass R.rowMass / highCenterMix C) / historyReferenceRho (3^d) ≤
      1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2))
    (hkill : ∀ j h S, MeasurableSet S →
      (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
        (highUnionSourceMass C R (historyMarkedAppend
          (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e))) *
        highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map (highUnionSourceMass C R)
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))) =
    Measure.map (highUnionSourceMass C R)
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) := by
  letI := highUnionSourceLaw_probability C R G
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  exact historyMarkedPrior_invariant_law _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    T _ hT (div_nonneg G.total_positive.le (highCenterMix_mem C).1.le)
    (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
    (highUnionActivation_measurable R G.activation_measurable _)
    (highUnionSourceActivation_centered C R G hpos) (highUnionSourceActivation_bound C R G hpos)
    hsmall _ (highUnionSourceMass_measurable C R G) hkill t ht

end UnionMassAndInvariant
end CompleteSourceAndMass

-- ============================================================================
-- 4. Source Regression, Global Likelihood Score, and Borel Reset Primitives
-- ============================================================================

section SourceRegressionAndScore
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

def highUnionSourceRegression {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k F I E) (η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : ℝ :=
  highFrameField d k η (fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)) x

theorem highUnionSourceRegression_joint_measurable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k F I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R) (η : ℝ) :
    Measurable fun hx : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark E) × Covariate d => highUnionSourceRegression C R η hx.1 hx.2 := by
  have hst : Measurable (highUnionSourceState C R) :=
    historyMarkedRawState_measurable (fun i j => j ∈ highNeighborLabels d k i)
      (highUnionRawUpdate R (highCenterMix C))
      (fun j => highUnionRawUpdate_measurable R G.slope_measurable G.intercept_measurable
        G.vector_measurable G.time_measurable (highCenterMix C) j) highUnionVacuum
  exact highFrameField_joint_measurable d k F η
    (fun h => (highUnionSourceState C R h).2) (measurable_snd.comp hst)

lemma highMarkedLocalScore_sum_of_partition {J ι E : Type*}
    [Fintype J] [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {n : ℕ}
    (π : J → Measure E) (activation : J → E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : J → E → Fin n → ℝ)
    (cReset : J → E → ι → ℝ) (g w : J → Fin n → ℝ)
    (φ : J → Fin n → ι → ℝ) (c : J → ι → ℝ) (f : Fin n → ℝ)
    (hreg : ∀ j, coefficientRegression η (g j) (w j) (φ j) (c j) = f)
    (hpartition : ∀ i, ∑ j, (w j i)^2 = 1) (y : Fin n → Fin 3) :
    (∑ j, highMarkedLocalScore (π j) (activation j) a V η p (pReset j)
      (cReset j) (g j) (w j) (φ j) (c j) y) =
    ((∑ j, highMarkedResponseAction (π j) (activation j) a V η
      (pReset j) (cReset j) (g j) (w j) (φ j) y) -
      η^2*(∏ i, p i)*∑ i, ternaryVarianceDerivative a (y i)*
        ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, ternaryMass a (f l) V (y l)) /
      ((∏ i, p i)*∏ i, ternaryMass a (f i) V (y i)) := by
  unfold highMarkedLocalScore highResponseProduct highResponseVarianceTerm
  simp_rw [hreg]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  congr 2
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, hpartition, one_mul]

section ActualSourceScore
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k D I E)

theorem highUnionSourceRegression_append (n : ℕ) (hk : 4 ≤ k) (η : ℝ)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Fin n → Covariate d) :
    coefficientRegression η
      (fun i => highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i))
      (highUnionResponseReset R e ((highUnionSourceState C R h).2 j)) =
      fun i => highUnionSourceRegression C R η
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) (x i) := by
  unfold highUnionSourceRegression
  have hcoef : (highUnionSourceState C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e))).2 =
      Function.update (highUnionSourceState C R h).2 j
        (highUnionResponseReset R e ((highUnionSourceState C R h).2 j)) := by
    rw [highUnionSourceState_append R C j h e]; rfl
  rw [hcoef]
  let u := highUnionResponseReset R e ((highUnionSourceState C R h).2 j)
  have hupd (x₀ : Covariate d) :
      highLocalFieldWithout d k D η (Function.update (highUnionSourceState C R h).2 j u) j x₀ =
        highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j x₀ := by
    unfold highLocalFieldWithout
    refine congrArg (η * ·) (Finset.sum_congr rfl fun l hl => ?_)
    rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]
  simpa only [Function.update_self, hupd] using
    highFrameField_coefficientRegression d k D n hk η (Function.update (highUnionSourceState C R h).2 j u) j x

def highUnionSourceLocalScore (n : ℕ) (a V η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highFrameMarkedScore d k D n
    (fun _ => highUnionLaw R (highCenterMix C))
    (fun _ => highUnionActivation R (highCenterMix C)) a V η
    (fun i => highUnionSourceDensity C R h (x i))
    (fun l e i => highUnionSourceDensity C R
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) l (h, e)) (x i))
    (fun l e => highUnionResponseReset R e ((highUnionSourceState C R h).2 l))
    (highUnionSourceState C R h).2 x j y

theorem highUnionSourceLikelihoodScore_eq_sum (n : ℕ) (hk : 4 ≤ k) (a V η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
    highHistoryLikelihoodScore (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η) h (x, y) =
      ∑ j, highUnionSourceLocalScore C R n a V η h x j y := by
  have happ (j : HighWindowLabels d k) :
      highAppendLikelihoodAction (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
        (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
        n a V (highUnionSourceDensity C R) (highUnionSourceRegression C R η) j h (x, y) =
      highMarkedResponseAction (highUnionLaw R (highCenterMix C))
        (highUnionActivation R (highCenterMix C)) a V η
        (fun e i => highUnionSourceDensity C R
          (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
            (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) (x i))
        (fun e => highUnionResponseReset R e ((highUnionSourceState C R h).2 j))
        (fun i => highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j (x i))
        (fun i => highPeriodicTensor d k j (x i))
        (fun i => highLocalFrameFeature k j (x i)) y := by
    unfold highAppendLikelihoodAction highMarkedResponseAction
    refine integral_congr_ae <| Filter.Eventually.of_forall fun e => ?_
    dsimp only; unfold highRawSampleLikelihood
    rw [Finset.prod_mul_distrib]; unfold highResponseProduct
    rw [highUnionSourceRegression_append C R n hk η j h e x]
    exact (mul_assoc _ _ _).symm
  simp only [highUnionSourceLocalScore, highFrameMarkedScore]
  rw [highMarkedLocalScore_sum_of_partition
    (hreg := fun j => highFrameField_coefficientRegression d k D n hk η (highUnionSourceState C R h).2 j x)
    (hpartition := fun i => highPeriodicTensor_sq_partition d k (by omega) (x i))]
  unfold highHistoryLikelihoodScore highHistoryLikelihoodDerivative
  simp_rw [happ]
  unfold highRawSampleLikelihood highRawSampleVarianceDerivative highUnionSourceRegression
  rw [Finset.prod_mul_distrib]
  congr 2; simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end ActualSourceScore
end SourceRegressionAndScore

section ScorePrimitives
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)

def highUnionSourceResetDensity (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highUnionSourceDensity C R (historyMarkedAppend
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) x

def highUnionSourceResetCoefficient (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) : HighFrameIndex d D → ℝ :=
  highUnionResponseReset R e ((highUnionSourceState C R h).2 j)

include G in
theorem highUnionSourceDensity_coarse_interval
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : C.densityLower ≤ highUnionSourceDensity C R h x ∧
      highUnionSourceDensity C R h x ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_interval C R G h x
  have hM : 0 < M := by linarith [(highCenterResolution_guards C M G.resolution).1]
  exact ⟨by linarith [hb.1, one_div_pos.mpr hM], by linarith [hb.2, one_div_pos.mpr hM]⟩

include G in
theorem highUnionSourceResetDensity_measurable (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    Measurable (Function.uncurry (highUnionSourceResetDensity C R j h)) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  exact (highUnionSourceDensity_joint_measurable C R G).comp
    (((historyMarkedAppend_measurable (E := HighUnionMark E)
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)

include G in
theorem highUnionSourceResetDensity_abs_le (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Covariate d) :
    |highUnionSourceResetDensity C R j h e x| ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_coarse_interval C R G
    (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) x
  rw [highUnionSourceResetDensity, abs_of_nonneg (C.densityLower_pos.le.trans hb.1)]
  exact hb.2

include G in
theorem highUnionSourceResetCoefficient_measurable (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (γ : HighFrameIndex d D) :
    Measurable fun e => highUnionSourceResetCoefficient C R j h e γ := by
  unfold highUnionSourceResetCoefficient highUnionResponseReset coefficientReset
  exact (measurable_const.sub (highUnionResponseTime_measurable R G.time_measurable)).mul
    measurable_const |>.add ((highUnionResponseTime_measurable R G.time_measurable).mul
      (highUnionResponseVector_measurable R G.vector_measurable γ))

theorem highUnionSourceResetDensity_outside (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    highUnionSourceResetDensity C R j h e x = highUnionSourceDensity C R h x :=
  highUnionSourceDensity_append_of_not_mem R C j h e x hx

end ScorePrimitives

-- ============================================================================
-- 5. Marginal Likelihood, Score Contraction, Score Path, Cost, and Poisson Tail
-- ============================================================================

section MarginalScoreAndCost
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def highMarginalRawLikelihood {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∫ ω, highRawSampleLikelihood n a V (p ω) (F ω) z ∂ν

lemma highMarginalRawLikelihood_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) [SFinite ν] (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalRawLikelihood ν n a V p F) :=
  (highRawSampleLikelihood_joint_measurable n a V p F hp hF).stronglyMeasurable.integral_prod_left'.measurable

lemma highMarginalRawLikelihood_pos {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V P : ℝ) (hP : 0 ≤ P) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpp : ∀ ω x, 0 < p ω x) (hpb : ∀ ω x, |p ω x| ≤ P)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    0 < highMarginalRawLikelihood ν n a V p F z :=
  integral_likelihood_pos ν _
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF).of_uncurry_right (P^n)
    (fun ω => highRawSampleLikelihood_pos n a V p F hpp hq ω z)
    fun ω => (le_abs_self _).trans
      (highRawSampleLikelihood_abs_le n a V P hP _ _ (hpb ω) ha (fun x y => (hq ω x y).le) z)

theorem highMassTilt_index_marginal_density {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    (highSampleIndexKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (highSampleReference d n).withDensity fun z => ENNReal.ofReal
        (highMarginalRawLikelihood ν n a V p F z /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hb (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
  let _ := massPowerTilt_isProbability ν m hm n aRaw bRaw haRaw hb
  have hpabs (ω : Ω) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  let L : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun z =>
    highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 / massPowerNormalizer ν m n
  have hLb (z) : 0 ≤ L z ∧ L z ≤ |bRaw|^n / massPowerNormalizer ν m n :=
    ⟨div_nonneg (Finset.prod_nonneg fun _ _ => mul_nonneg (haRaw.le.trans (hraw z.1 _).1) (hq z.1 _ _)) hG.le,
      div_le_div_of_nonneg_right ((le_abs_self _).trans
        (highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) _ _ (hpabs z.1) ha (hq z.1) z.2)) hG.le⟩
  rw [← Measure.snd_compProd, Measure.snd,
    massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw,
    map_snd_prod_withDensity_ofReal ν (highSampleReference d n) L
      ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).div_const _)
      (|bRaw|^n / massPowerNormalizer ν m n) (by positivity) hLb]
  congr 1; funext z
  simp only [L, integral_div, highMarginalRawLikelihood, m]

def decodeTernaryResponse (a y : ℝ) : Fin 3 :=
  if y = -a then 0 else if y = 0 then 1 else 2

def decodeDesignResponse {d n : ℕ} (a : ℝ) (z : Fin n → Observation d) :
    (Fin n → Covariate d) × (Fin n → Fin 3) :=
  (fun i => (z i).1, fun i => decodeTernaryResponse a (z i).2)

theorem decodeDesignResponse_measurable {d n : ℕ} (a : ℝ) :
    Measurable (decodeDesignResponse (d := d) (n := n) a) := by
  have hdec : Measurable (decodeTernaryResponse a) :=
    Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const <|
      Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const
  exact (measurable_pi_iff.mpr fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    (measurable_pi_iff.mpr fun i => hdec.comp (measurable_snd.comp (measurable_pi_apply i)))

theorem decodeDesignResponse_encode {d n : ℕ} (a : ℝ) (ha : 0 < a)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    decodeDesignResponse a (encodeDesignResponse a z) = z := by
  have hna : -a ≠ 0 := neg_ne_zero.mpr ha.ne'
  have han : a ≠ -a := by linarith
  have hval (u : Fin 3) : decodeTernaryResponse a (ternaryValue a u) = u := by
    fin_cases u <;> simp [decodeTernaryResponse, ternaryValue, hna, ha.ne', han]
  exact Prod.ext rfl (funext fun i => hval (z.2 i))

theorem weighted_score_energy_contraction {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (L D : Ω → ℝ)
    (hL : ∀ ω, 0 < L ω) (hiL : Integrable L ν) (hiD : Integrable D ν)
    (hiE : Integrable (fun ω => D ω ^ 2 / L ω) ν)
    (hmean : 0 < ∫ ω, L ω ∂ν) :
    (∫ ω, D ω ∂ν)^2 / (∫ ω, L ω ∂ν) ≤ ∫ ω, D ω ^ 2 / L ω ∂ν := by
  let r : ℝ := (∫ ω, D ω ∂ν) / (∫ ω, L ω ∂ν)
  have he (ω : Ω) : (D ω - r * L ω)^2 / L ω = D ω^2 / L ω - 2*r*D ω + r^2*L ω := by
    field_simp [(hL ω).ne']; ring
  have hn : 0 ≤ ∫ ω, (D ω - r * L ω)^2 / L ω ∂ν :=
    integral_nonneg fun ω => div_nonneg (sq_nonneg _) (hL ω).le
  have hv : (∫ ω, (D ω - r * L ω)^2 / L ω ∂ν) =
      (∫ ω, D ω^2 / L ω ∂ν) - 2*r*(∫ ω, D ω ∂ν) + r^2*(∫ ω, L ω ∂ν) := by
    simp_rw [he]
    have hv1 := integral_add (hiE.sub (hiD.const_mul (2*r))) (hiL.const_mul (r^2))
    rw [integral_sub' hiE (hiD.const_mul (2*r)), integral_const_mul, integral_const_mul] at hv1
    simpa only [Pi.sub_apply] using hv1
  rw [hv] at hn
  have hr : -2*r*(∫ ω, D ω ∂ν) + r^2*(∫ ω, L ω ∂ν) = -(∫ ω, D ω ∂ν)^2 / (∫ ω, L ω ∂ν) := by
    dsimp only [r]; field_simp [hmean.ne']; ring
  rw [neg_div] at hr; nlinarith [hn, hr]

def highMarginalIndexScore {J E : Type*} [Fintype J] [LinearOrder J] [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∫ ω, highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z ∂ν) /
    highMarginalRawLikelihood ν n a V p F z

def highMarginalRealScore {J E : Type*} [Fintype J] [LinearOrder J] [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : Fin n → Observation d) : ℝ :=
  highMarginalIndexScore dependent hsymm ν π activation n a V η p F (decodeDesignResponse a z)

theorem highMarginalRealScore_measurable {J E : Type*} [Fintype J] [LinearOrder J]
    [MeasurableSpace E] [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [SFinite ν] (π : Measure E) [SFinite π]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable (highMarginalRealScore dependent hsymm ν π activation n a V η p F) :=
  ((highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF).stronglyMeasurable.integral_prod_left'.measurable.div
    (highMarginalRawLikelihood_measurable ν n a V p F hp hF)).comp (decodeDesignResponse_measurable a)

theorem highMarginalRealScore_integral {J E : Type*} [Fintype J] [LinearOrder J]
    [MeasurableSpace E] [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw B : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z, H z * highMarginalRealScore dependent hsymm ν π activation n a V η p F z
      ∂(highRealSampleKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          H (encodeDesignResponse a z.2) *
            highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
  have hmR : Measurable fun z => H z * highMarginalRealScore dependent hsymm ν π activation n a V η p F z :=
    hH.mul (highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF)
  rw [highRealSampleKernel, ← Measure.map_comp _ _ (encodeDesignResponse_measurable a),
    integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hmR.stronglyMeasurable]
  have hdec : (∫ z, H (encodeDesignResponse a z) *
      highMarginalRealScore dependent hsymm ν π activation n a V η p F (encodeDesignResponse a z)
      ∂(highSampleIndexKernel n a V p F hp hF) ∘ₘ (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
    ∫ z, H (encodeDesignResponse a z) *
      highMarginalIndexScore dependent hsymm ν π activation n a V η p F z
      ∂(highSampleIndexKernel n a V p F hp hF) ∘ₘ (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) :=
    integral_congr_ae <| Eventually.of_forall fun z => by
      dsimp only [highMarginalRealScore]
      rw [decodeDesignResponse_encode a ha]
  rw [hdec]
  let m := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hb (ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hb
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]
    exact (hraw ω x).2.trans (le_abs_self _)
  have hL (z) := highMarginalRawLikelihood_pos ν n a V |bRaw| (abs_nonneg _) ha.ne' p F hp hF
    (fun ω x => haRaw.trans_le (hraw ω x).1) hpb hq z
  have hdens : Measurable fun z => ENNReal.ofReal
      (highMarginalRawLikelihood ν n a V p F z / massPowerNormalizer ν m n) :=
    ((highMarginalRawLikelihood_measurable ν n a V p F hp hF).div_const _).ennreal_ofReal
  rw [highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha.ne' hraw
    (fun ω x y => (hq ω x y).le),
    integral_withDensity_eq_integral_toReal_smul hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hL _).le hG.le), smul_eq_mul]
  have hi : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2)
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound
      (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF)).aestronglyMeasurable
      (B * ((Fintype.card J : ℝ) * (Ba * |bRaw|^n) + η^2 * (|bRaw|^n * ((n : ℝ)/a^2))))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa
        habound n a V η |bRaw| (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2)
        (abs_nonneg _) hB
  calc
    _ = (massPowerNormalizer ν m n)⁻¹ *
        ∫ z, H (encodeDesignResponse a z) *
          (∫ ω, highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z ∂ν)
          ∂highSampleReference d n := by
      rw [← integral_const_mul]
      refine integral_congr_ae <| Eventually.of_forall fun z => ?_
      dsimp only [highMarginalIndexScore]
      field_simp [(hL z).ne', hG.ne'] <;> ring
    _ = _ := by
      congr 1
      rw [MeasureTheory.integral_prod_symm _ hi]
      exact integral_congr_ae <| Eventually.of_forall fun z =>
        (integral_const_mul (H (encodeDesignResponse a z)) _).symm

theorem highTiltedObservableMean_eq_dataMean {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V aRaw bRaw B : ℝ) (ha : a ≠ 0) (haRaw : 0 < aRaw) (_hB : 0 ≤ B)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    highTiltedObservableMean ν n a V p F hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a V p F hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) := by
  have hm := highRawDensityMass_joint_measurable p hp
  have hb (ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν _ hm n aRaw bRaw haRaw hb
  let _ := highRealSampleKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  exact (probability_kernel_integral _ _ H <| Integrable.of_bound hH.aestronglyMeasurable B
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hHb z)).symm

theorem paper_score_to_risk {Α : Type*} [MeasurableSpace Α] {d n : ℕ}
    (C : ModelConstants d) (σ : ℝ → Measure Α)
    (L : ℝ → Kernel Α (Fin n → Observation d))
    (θ : ℝ → Α → RegressionParameter d) (V : ℝ → ℝ)
    (R : ℝ → (Fin n → Observation d) → ℝ) (δ ε : ℝ) (hδ : 0 ≤ δ)
    (hσ : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (σ t))
    (hLprob : ∀ t ∈ Icc 0 δ, IsMarkovKernel (L t))
    (hL : ∀ t ∈ Icc 0 δ, ∀ a, L t a = sampleLaw (θ t a) n)
    (hVθ : ∀ t ∈ Icc 0 δ, ∀ a, (θ t a).variance = V t)
    (hV : ∀ t ∈ Icc 0 δ, V t ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : ℝ → Set Α) (hbad : ∀ t ∈ Icc 0 δ, MeasurableSet (bad t))
    (hlegal : ∀ t ∈ Icc 0 δ, ∀ a ∉ bad t, Admissible C (θ t a))
    (hmass : ∀ t ∈ Icc 0 δ, (σ t).real (bad t) ≤ ε)
    (hR : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → MemLp (R t) 2 (L t ∘ₘ σ t))
    (hcenter : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → (∫ x, R t x ∂(L t ∘ₘ σ t)) = 0)
    (hAC : ∀ T : BoundedEstimator C n, AbsolutelyContinuousOnInterval
      (fun t => ∫ x, T.val.val x ∂(L t ∘ₘ σ t)) 0 δ)
    (hderiv : ∀ T : BoundedEstimator C n, ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      HasDerivAt (fun u => ∫ x, T.val.val x ∂(L u ∘ₘ σ u))
        (∫ x, T.val.val x * R t x ∂(L t ∘ₘ σ t)) t)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t))) volume 0 δ) :
    ENNReal.ofReal ((V δ - V 0) ^ 2 /
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂(L t ∘ₘ σ t))) ^ 2
      - (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε) ≤ minimaxRisk C n := by
  have hε : 0 ≤ ε := measureReal_nonneg.trans (hmass 0 ⟨le_rfl, hδ⟩)
  let P (t : ℝ) := L t ∘ₘ σ t
  have hprob (t : ℝ) (ht : t ∈ Icc 0 δ) : IsProbabilityMeasure (P t) := by
    let _ := hσ t ht; let _ := hLprob t ht; dsimp only [P]; infer_instance
  rw [minimaxRisk_eq_inf_bounded]
  refine le_iInf fun T => ?_
  let risk := worstCaseRisk C T.val
  let D := effectiveVarianceUpper C - C.varianceLower
  let r := Real.sqrt (risk.toReal + D ^ 2 * ε)
  have hrEq : r ^ 2 = risk.toReal + D ^ 2 * ε :=
    Real.sq_sqrt (add_nonneg ENNReal.toReal_nonneg (mul_nonneg (sq_nonneg _) hε))
  have hTrisk (t : ℝ) (ht : t ∈ Icc 0 δ) : (∫ x, (T.val.val x - V t) ^ 2 ∂P t) ≤ r ^ 2 := by
    let _ := hσ t ht; let _ := hLprob t ht; rw [hrEq]
    exact boundedEstimator_mixture_risk_le_of_exceptional_set C T (σ t) (L t) (θ t) (V t) ε
      (hL t ht) (hVθ t ht) (hV t ht) (bad t) (hbad t ht) (hlegal t ht) (hmass t ht)
  have hT (t : ℝ) (ht : t ∈ Icc 0 δ) : MemLp T.val.val 2 (P t) := by
    let _ := hprob t ht; exact boundedEstimator_memLp C T (P t) 2
  simpa only [P, D, risk, ENNReal.ofReal_toReal (boundedEstimator_worstCaseRisk_finite C T).ne] using
    ENNReal.ofReal_le_ofReal (probability_absolutelyContinuous_score_path_risk_lower_bound
      P T.val.val R V δ r risk.toReal D ε hδ (Real.sqrt_nonneg _) hprob hT hR hcenter (hAC T)
      (hderiv T) hTrisk hscoreInt hrEq)

def localScorePathLength (c B I : ℝ) : ℝ := c / (1 + B + I)

theorem localScorePathLength_pos {c B I : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : 0 < localScorePathLength c B I :=
  div_pos hc (by linarith only [hB, hI])

theorem localScorePathLength_energy_le {c B I : ℝ} (hc : 0 ≤ c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) : localScorePathLength c B I * I ≤ c := by
  rw [localScorePathLength, div_mul_eq_mul_div]
  exact (div_le_iff₀ (by linarith only [hB, hI])).mpr (mul_le_mul_of_nonneg_left (by linarith only [hB]) hc)

theorem score_cost_numeric {c B I η score : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) (hscore0 : 0 ≤ score)
    (hscore : score ≤ localScorePathLength c B I * I) :
    c ^ 2 / (3 * (2 + c) ^ 2) * η ^ 4 / (1 + B ^ 2 + I ^ 2) ≤
      η ^ 4 * (localScorePathLength c B I) ^ 2 / (2 + score) ^ 2 := by
  have hden : 0 < 1 + B + I := by linarith only [hB, hI]
  have hsc : score ≤ c := hscore.trans (localScorePathLength_energy_le hc.le hB hI)
  have hscpos : 0 < 2 + score := by linarith only [hscore0]
  have hcpos : 0 < 2 + c := by linarith only [hc]
  have hprod : (2 + score) ^ 2 * (1 + B + I) ^ 2 ≤ 3 * (2 + c) ^ 2 * (1 + B ^ 2 + I ^ 2) :=
    calc
      _ ≤ (2 + c) ^ 2 * (1 + B + I) ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hsc, hscpos, hcpos]) (sq_nonneg _)
      _ ≤ (2 + c) ^ 2 * (3 * (1 + B ^ 2 + I ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (by nlinarith only [sq_nonneg (1 - B), sq_nonneg (1 - I), sq_nonneg (B - I)]) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ = (c ^ 2 * η ^ 4) / (3 * (2 + c) ^ 2 * (1 + B ^ 2 + I ^ 2)) := by field_simp <;> ring
    _ ≤ (c ^ 2 * η ^ 4) / ((2 + score) ^ 2 * (1 + B + I) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
    _ = _ := by rw [localScorePathLength]; field_simp <;> ring

def poissonCountWeight (x : ℝ) (k : ℕ) : ℝ := x ^ k / (k.factorial : ℝ)

theorem poissonCountWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ poissonCountWeight x k := by unfold poissonCountWeight; positivity

theorem poissonCountWeight_summable (x : ℝ) : Summable (poissonCountWeight x) :=
  Real.summable_pow_div_factorial x

theorem poissonCountWeight_tail_le {x : ℝ} (hx : 0 ≤ x) (a : ℕ) :
    (∑' j, poissonCountWeight x (a + j)) ≤ Real.exp x * poissonCountWeight x a := by
  have hs : Summable fun j => poissonCountWeight x (a + j) :=
    (poissonCountWeight_summable x).comp_injective fun _ _ h => Nat.add_left_cancel h
  have hg : Summable fun j => poissonCountWeight x a * poissonCountWeight x j :=
    (poissonCountWeight_summable x).mul_left _
  have hadd (j : ℕ) : poissonCountWeight x (a + j) ≤ poissonCountWeight x a * poissonCountWeight x j := by
    have hf : (a.factorial : ℝ) * (j.factorial : ℝ) ≤ ((a + j).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a j)
    simpa only [poissonCountWeight, pow_add, div_mul_div_comm] using
      div_le_div_of_nonneg_left (pow_nonneg hx (a + j))
        (mul_pos (by exact_mod_cast Nat.factorial_pos a) (by exact_mod_cast Nat.factorial_pos j)) hf
  have htsum : (∑' k, poissonCountWeight x k) = Real.exp x := by
    simpa only [poissonCountWeight, Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq
  calc
    _ ≤ ∑' j, poissonCountWeight x a * poissonCountWeight x j := hs.tsum_le_tsum hadd hg
    _ = Real.exp x * poissonCountWeight x a := by rw [tsum_mul_left, htsum, mul_comm]

end MarginalScoreAndCost

-- ============================================================================
-- 6. Lower Activity Hierarchy, Higher-Band Conversion, and Lower Alias Scale
-- ============================================================================

section HierarchyAndScale
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

lemma log_profile_div_scale_tends_zero {f M : ℝ → ℝ} {c : ℝ}
    (hM : Tendsto M atTop atTop) (p : ℕ) (hc : 0 < c)
    (hf : ∀ᶠ x in atTop, 0 < f x)
    (hr : Tendsto (fun x => f x / (M x)^p) atTop (𝓝 c)) :
    Tendsto (fun x => Real.log (f x) / M x) atTop (𝓝 0) := by
  have hh := ((Real.continuousAt_log hc.ne').tendsto.comp hr).mul hM.inv_tendsto_atTop |>.add
    ((Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hM).const_mul (p : ℝ))
  simp only [mul_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [hf, hM.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hMx
  simp only [Function.comp_apply, id_eq, Pi.inv_apply]
  rw [Real.log_div hx.ne' (pow_pos hMx p).ne', Real.log_pow]
  field_simp [hMx.ne']; ring

theorem positive_profile_tends_zero_of_log_div_negative {f M : ℝ → ℝ} {c : ℝ}
    (hM : Tendsto M atTop atTop) (hc : c < 0) (hf : ∀ᶠ x in atTop, 0 < f x)
    (hr : Tendsto (fun x => Real.log (f x) / M x) atTop (𝓝 c)) :
    Tendsto f atTop (𝓝 0) :=
  (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative hM hr hc)).congr'
    (hf.mono fun _ hx => Real.exp_log hx)

def lowerAliasH (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 + Real.log (lowerSaddleN s d m θ C τM x)

def lowerAliasQ (s d m θ C Cact a : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Cact * (lowerSaddleD d m x : ℝ) * lowerAliasH s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^(a/d)

def lowerAliasCutoff (s d m θ C c0 : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  lowerSaddleN s d m θ C τM x * Real.exp (-c0 * lowerSaddleD d m x)

def lowerAliasTargetScale (s d m θ C : ℝ) (τM : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  lowerSaddleN s d m θ C τM x *
    (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x)^(((r : ℝ)-2)/d)

lemma lowerSaddleD_eventually_positive {d m : ℝ} (hd : 0 < d) (hm : 0 < m) :
    ∀ᶠ x in atTop, 0 < (lowerSaddleD d m x : ℝ) := by
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  exact lt_of_lt_of_le (by positivity : 0 < (d+8)/4 * (lowerSaddleM m x : ℝ)) (Nat.le_ceil _)

lemma log_lowerSaddleD_div_M_tends_zero {d m : ℝ} (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => Real.log (lowerSaddleD d m x) / lowerSaddleM m x) atTop (𝓝 0) :=
  log_profile_div_scale_tends_zero (lowerSaddleM_tendsto_atTop hm) 1 (by linarith : 0 < (d+8)/4)
    (lowerSaddleD_eventually_positive hd hm) (by simpa only [pow_one] using lowerSaddleD_div_M_limit hd hm)

lemma lowerSaddleM_sq_tendsto_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleM m x : ℝ)^2) atTop atTop := by
  simpa only [pow_two] using (lowerSaddleM_tendsto_atTop hm).atTop_mul_atTop₀ (lowerSaddleM_tendsto_atTop hm)

theorem lowerSaddleD_div_M_sq_tends_zero {d m : ℝ} (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => (lowerSaddleD d m x : ℝ) / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
  have hh := (lowerSaddleD_div_M_limit hd hm).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  simp only [mul_zero] at hh
  convert hh using 1; funext x
  simp only [Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv, mul_assoc]

lemma log_lowerSaddleD_div_M_sq_tends_zero {d m : ℝ} (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x => Real.log (lowerSaddleD d m x) / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
  have hh := (log_lowerSaddleD_div_M_tends_zero hd hm).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop
  simp only [mul_zero] at hh
  convert hh using 1; funext x
  simp only [Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv, mul_assoc]

def lowerAliasFineTargetBound (d θ c0 : ℝ) : ℕ :=
  Nat.ceil (3 + d*c0*(((d+8)/4)/θ + 1))

def LowerAliasHierarchy (s d m θ C Cact Cs c0 : ℝ) (τM : ℕ → ℝ) (x : ℝ) : Prop :=
  1 < lowerAliasCutoff s d m θ C c0 τM x ∧
  τM (lowerSaddleM m x) ≤ c0 ∧
  lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x ≤ 1 ∧
  Real.log (lowerAliasH s d m θ C τM x) ≤ lowerSaddleM m x ∧
  2 * Real.log (lowerAliasH s d m θ C τM x) < lowerSaddleOmega d m θ C x ∧
  lowerAliasQ s d m θ C Cact 2 τM x ≤ lowerAliasQ s d m θ C Cact 1 τM x ∧
  lowerAliasQ s d m θ C Cact 1 τM x ≤ 1/2 ∧
  (lowerSaddleD d m x : ℝ)^2 * lowerAliasQ s d m θ C Cact 1 τM x ≤ 1 ∧
  Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) *
    lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x ≤ 1 ∧
  Cs * (lowerSaddleD d m x : ℝ) * Real.exp (c0*((lowerSaddleD d m x : ℝ)+1)) ≤
    lowerSaddleN s d m θ C τM x ∧
  lowerAliasFineTargetBound d θ c0 ≤ lowerSaddleM m x ∧
  ∀ r : ℕ, lowerAliasCutoff s d m θ C c0 τM x < lowerAliasTargetScale s d m θ C τM r x →
    r ≤ lowerAliasFineTargetBound d θ c0

section Asymptotics
variable {s d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
  (hs : 1 < s) (hd : 4*s < d) (hm : 0 < m) (hθ : 0 < θ)
  (hcontrol : LowerExponentControl τM τ Cτ)
include hs hd hm hθ hcontrol

lemma lowerAliasH_eventually_positive (C : ℝ) :
    ∀ᶠ x in atTop, 0 < lowerAliasH s d m θ C τM x := by
  filter_upwards [(lowerSaddleN_tendsto_atTop hs hd hm hθ hcontrol C).eventually
    (eventually_gt_atTop (1 : ℝ))] with x hx
  unfold lowerAliasH; linarith [Real.log_pos hx]

lemma log_lowerAliasH_div_M_tends_zero (C : ℝ) :
    Tendsto (fun x => Real.log (lowerAliasH s d m θ C τM x) / lowerSaddleM m x) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hlim : Tendsto (fun x => lowerAliasH s d m θ C τM x / (lowerSaddleM m x : ℝ)^2)
      atTop (𝓝 (((d-4*s)/(d*(d+4)))/m^2)) := by
    have hh := ((lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.pow 2).add
      (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C)
    simp only [zero_pow (by decide : 2 ≠ 0), zero_add] at hh
    convert hh using 1; funext x
    simp only [lowerAliasH, add_div, one_div, Pi.inv_apply, inv_pow]
  exact log_profile_div_scale_tends_zero (lowerSaddleM_tendsto_atTop hm) 2
    (by positivity : 0 < ((d-4*s)/(d*(d+4)))/m^2)
    (lowerAliasH_eventually_positive hs hd hm hθ hcontrol C) hlim

lemma lowerAliasMuH_eventually_positive (C : ℝ) :
    ∀ᶠ x in atTop, 0 < lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), lowerAliasH_eventually_positive hs hd hm hθ hcontrol C] with x hx hH
  rw [lowerSaddleMu_eq_exp hx]; positivity

lemma lowerAliasMuH_log_div_M_limit (C : ℝ) :
    Tendsto (fun x => Real.log (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) /
      lowerSaddleM m x) atTop (𝓝 (-θ)) := by
  have hh := (lowerSaddleOmega_div_M_limit (d := d) (by linarith) hm hθ C).neg.add
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), lowerAliasH_eventually_positive hs hd hm hθ hcontrol C]
    with x hx hH
  rw [lowerSaddleMu_eq_exp hx, Real.log_mul (Real.exp_pos _).ne' hH.ne', Real.log_exp]; ring

lemma lowerAliasQ_log_div_M_limit {Cact : ℝ} (hCact : 0 < Cact) (C a : ℝ) :
    Tendsto (fun x => Real.log (lowerAliasQ s d m θ C Cact a τM x) / lowerSaddleM m x)
      atTop (𝓝 (-θ * (a/d))) := by
  have hd0 : 0 < d := by linarith
  have hh := ((((lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log Cact)).add
    (log_lowerSaddleD_div_M_tends_zero hd0 hm)).add
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)).add
      ((lowerAliasMuH_log_div_M_limit hs hd hm hθ hcontrol C).const_mul (a/d))
  simp only [mul_zero, zero_add, mul_comm (a/d)] at hh
  refine hh.congr' ?_
  filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
    lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
    lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
  simp only [Pi.inv_apply]; unfold lowerAliasQ
  rw [Real.log_mul (mul_pos (mul_pos hCact hD) hH).ne' (Real.rpow_pos_of_pos hbase _).ne',
    Real.log_mul (mul_pos hCact hD).ne' hH.ne', Real.log_mul hCact.ne' hD.ne', Real.log_rpow hbase]
  ring

lemma eventually_lowerAlias_hierarchy {Cact Cs c0 : ℝ}
    (hCact : 0 < Cact) (hCs : 0 < Cs) (hc0 : 0 < c0) (hτc0 : τ < c0) (C : ℝ) :
    ∀ᶠ x in atTop, LowerAliasHierarchy s d m θ C Cact Cs c0 τM x := by
  have hd0 : 0 < d := by linarith
  have hA : 0 < ((d-4*s)/(d*(d+4)))/m^2 := by positivity
  have hMuH0 : Tendsto (fun x => lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) atTop (𝓝 0) :=
    positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm) (neg_neg_of_pos hθ)
      (lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C)
      (lowerAliasMuH_log_div_M_limit hs hd hm hθ hcontrol C)
  have hqpos : ∀ᶠ x in atTop, 0 < lowerAliasQ s d m θ C Cact 1 τM x := by
    filter_upwards [lowerSaddleD_eventually_positive hd0 hm,
      lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
      lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C] with x hD hH hbase
    exact mul_pos (mul_pos (mul_pos hCact hD) hH) (Real.rpow_pos_of_pos hbase _)
  have hQ0 : Tendsto (lowerAliasQ s d m θ C Cact 1 τM) atTop (𝓝 0) :=
    positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) (div_pos one_pos hd0))
      hqpos (lowerAliasQ_log_div_M_limit hs hd hm hθ hcontrol hCact C 1)
  have hDQ0 : Tendsto (fun x => (lowerSaddleD d m x : ℝ)^2 * lowerAliasQ s d m θ C Cact 1 τM x) atTop (𝓝 0) := by
    have hh := ((log_lowerSaddleD_div_M_tends_zero hd0 hm).const_mul 2).add
      (lowerAliasQ_log_div_M_limit hs hd hm hθ hcontrol hCact C 1)
    simp only [mul_zero, zero_add] at hh
    refine positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_tendsto_atTop hm)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) (div_pos one_pos hd0)) ?_ ?_
    · filter_upwards [lowerSaddleD_eventually_positive hd0 hm, hqpos] with x hD hQ; positivity
    · refine hh.congr' ?_
      filter_upwards [lowerSaddleD_eventually_positive hd0 hm, hqpos] with x hD hQ
      rw [Real.log_mul (sq_pos_of_pos hD).ne' hQ.ne', Real.log_pow]; ring
  have hcut : Tendsto (lowerAliasCutoff s d m θ C c0 τM) atTop atTop := by
    have hh := (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C).sub
      ((lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul c0)
    simp only [mul_zero, sub_zero] at hh
    have hlog : Tendsto (fun x => Real.log (lowerAliasCutoff s d m θ C c0 τM x) /
        (lowerSaddleM m x : ℝ)^2) atTop (𝓝 (((d-4*s)/(d*(d+4)))/m^2)) := by
      convert hh using 1; funext x
      rw [lowerAliasCutoff, Real.log_mul (lowerSaddleN_positive _ _ _ _ _ _ _).ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have ht : Tendsto (fun x => Real.log (lowerAliasCutoff s d m θ C c0 τM x)) atTop atTop := by
      refine ((lowerSaddleM_sq_tendsto_atTop hm).atTop_mul_pos hA hlog).congr' ?_
      filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
      exact mul_div_cancel₀ _ (sq_pos_of_pos hx).ne'
    convert Real.tendsto_exp_atTop.comp ht using 1; funext x
    exact (Real.exp_log (mul_pos (lowerSaddleN_positive _ _ _ _ _ _ _) (Real.exp_pos _))).symm
  have hsing : Tendsto (fun x => Cs * (lowerSaddleD d m x : ℝ) *
      Real.exp (c0*((lowerSaddleD d m x : ℝ)+1)) / lowerSaddleN s d m θ C τM x) atTop (𝓝 0) := by
    have hconst : Tendsto (fun x => Real.log Cs / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
      simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log Cs)
    have hconstc : Tendsto (fun x => c0 / (lowerSaddleM m x : ℝ)^2) atTop (𝓝 0) := by
      simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using (lowerSaddleM_sq_tendsto_atTop hm).inv_tendsto_atTop.const_mul c0
    have hh := (((hconst.add (log_lowerSaddleD_div_M_sq_tends_zero hd0 hm)).add
      ((lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul c0)).add hconstc).sub
        (lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C)
    simp only [mul_zero, zero_add, zero_sub] at hh
    refine positive_profile_tends_zero_of_log_div_negative (lowerSaddleM_sq_tendsto_atTop hm) (neg_neg_of_pos hA) ?_ ?_
    · filter_upwards [lowerSaddleD_eventually_positive hd0 hm] with x hD
      exact div_pos (mul_pos (mul_pos hCs hD) (Real.exp_pos _)) (lowerSaddleN_positive _ _ _ _ _ _ _)
    · refine hh.congr' ?_
      filter_upwards [lowerSaddleD_eventually_positive hd0 hm] with x hD
      rw [Real.log_div (mul_pos (mul_pos hCs hD) (Real.exp_pos _)).ne' (lowerSaddleN_positive _ _ _ _ _ _ _).ne',
        Real.log_mul (mul_pos hCs hD).ne' (Real.exp_pos _).ne', Real.log_mul hCs.ne' hD.ne', Real.log_exp]; ring
  have hgap2 := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
    ((log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C).const_mul 2)
  simp only [mul_zero, sub_zero] at hgap2
  have hglim := (lowerSaddleOmega_div_M_limit hd0 hm hθ C).sub
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C)
  simp only [sub_zero] at hglim
  have hDgap : Tendsto (fun x => (lowerSaddleD d m x : ℝ) /
      (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x))) atTop (𝓝 (((d+8)/4)/θ)) := by
    refine ((lowerSaddleD_div_M_limit hd0 hm).div hglim hθ.ne').congr' ?_
    filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    simp only [Pi.div_apply, ← sub_div, div_div_div_cancel_right₀ hx.ne']
  have hfine := ((hDgap.const_mul (d*c0)).const_add 2).eventually
    (gt_mem_nhds (by nlinarith : 2 + d*c0*(((d+8)/4)/θ) < 3 + d*c0*(((d+8)/4)/θ+1)))
  filter_upwards [
    hcut.eventually (eventually_gt_atTop (1 : ℝ)),
    (lowerSaddleTau_limit hm hcontrol).eventually (gt_mem_nhds hτc0),
    hMuH0.eventually (gt_mem_nhds one_pos),
    (log_lowerAliasH_div_M_tends_zero hs hd hm hθ hcontrol C).eventually (gt_mem_nhds one_pos),
    hgap2.eventually (lt_mem_nhds hθ),
    hQ0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    hDQ0.eventually (gt_mem_nhds one_pos),
    hsing.eventually (gt_mem_nhds one_pos),
    hfine,
    (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop (lowerAliasFineTargetBound d θ c0)),
    hglim.eventually (lt_mem_nhds hθ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
    lowerAliasMuH_eventually_positive hs hd hm hθ hcontrol C,
    lowerSaddleD_eventually_positive hd0 hm,
    lowerAliasH_eventually_positive hs hd hm hθ hcontrol C,
    eventually_gt_atTop (0 : ℝ)]
    with x hell hτ hbase hlog hgap hq hsmall hsng hthr hMnat hgapnorm hMpos hbase0 hD hH hx
  refine ⟨hell, hτ.le, hbase.le, by simpa only [one_mul] using ((div_lt_iff₀ hMpos).1 hlog).le,
    ?_, ?_, hq.le, hsmall.le, ?_,
    by simpa only [one_mul] using ((div_lt_iff₀ (lowerSaddleN_positive _ _ _ _ _ _ _)).1 hsng).le,
    hMnat, fun r hr => ?_⟩
  · exact (div_lt_div_iff_of_pos_right hMpos).mp (by simpa only [mul_div_assoc] using sub_pos.mp hgap)
  · unfold lowerAliasQ
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hbase0 hbase.le (div_le_div_of_nonneg_right (by norm_num) hd0.le))
      (by positivity)
  · rw [show Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) *
        lowerAliasCutoff s d m θ C c0 τM x / lowerSaddleN s d m θ C τM x =
        Real.exp ((τM (lowerSaddleM m x)-c0)*lowerSaddleD d m x) by
      unfold lowerAliasCutoff
      calc _ = Real.exp (τM (lowerSaddleM m x) * lowerSaddleD d m x) * Real.exp (-c0 * lowerSaddleD d m x) := by
              field_simp [(lowerSaddleN_positive s d m θ C τM x).ne']
        _ = _ := by rw [← Real.exp_add]; congr 1; ring]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hτ.le) (Nat.cast_nonneg _))
  · have hlogb : Real.log (lowerSaddleMu d m θ C x * lowerAliasH s d m θ C τM x) =
        -lowerSaddleOmega d m θ C x + Real.log (lowerAliasH s d m θ C τM x) := by
      rw [lowerSaddleMu_eq_exp hx, Real.log_mul (Real.exp_pos _).ne' hH.ne', Real.log_exp]
    have hgap0 : 0 < lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x) := by
      have hg : 0 < (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) / lowerSaddleM m x := by
        linarith [hgapnorm, sub_div (lowerSaddleOmega d m θ C x) (Real.log (lowerAliasH s d m θ C τM x)) (lowerSaddleM m x)]
      linarith [(lt_div_iff₀ hMpos).1 hg]
    have hln := Real.log_lt_log (Real.exp_pos _) ((mul_lt_mul_iff_right₀ (lowerSaddleN_positive s d m θ C τM x)).mp hr)
    rw [Real.log_exp, Real.log_rpow hbase0, hlogb] at hln
    have hm_ineq := mul_lt_mul_of_pos_right hln hd0
    rw [show (((r : ℝ)-2)/d * (-lowerSaddleOmega d m θ C x + Real.log (lowerAliasH s d m θ C τM x)))*d =
      -((r : ℝ)-2)*(lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) by
      field_simp [hd0.ne']; ring] at hm_ineq
    have hrlt : (r : ℝ) < 2 + d*c0*(lowerSaddleD d m x : ℝ) /
        (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) := by
      have hv := (lt_div_iff₀ hgap0).2 (by nlinarith : ((r : ℝ)-2)*(lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) < d*c0*lowerSaddleD d m x)
      linarith
    have hbound : (r : ℝ) < (lowerAliasFineTargetBound d θ c0 : ℝ) :=
      hrlt.trans <| (show 2 + d*c0*(lowerSaddleD d m x : ℝ) /
          (lowerSaddleOmega d m θ C x - Real.log (lowerAliasH s d m θ C τM x)) <
          3 + d*c0*(((d+8)/4)/θ+1) by simpa only [mul_div_assoc] using hthr).trans_le (Nat.le_ceil _)
    exact Nat.le_of_lt (by exact_mod_cast hbound)

end Asymptotics

theorem actual_lowerAlias_hierarchy {s d a b Cact Cs : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hCact : 0 < Cact) (hCs : 0 < Cs) (C : ℝ) :
    ∀ᶠ x in atTop,
      LowerAliasHierarchy s d
        (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C Cact Cs
        (densityIntervalExponent a b + 1) (shrunkDensityExponent a b) x := by
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  exact eventually_lowerAlias_hierarchy hs hd (lowerSaddleCoefficient_pos hs hd hτ)
    (lowerSaddleTheta_pos hs hd hτ) hcontrol hCact hCs (by linarith) (by linarith) C

def higherBandInterpolationBase (d : ℕ) (lam : ℝ) : ℝ := 1024 * |lam| *(d : ℝ)^2

def higherBandGeometricConstant (B Ci : ℝ) : ℝ := 2*(1+B)*(1+Ci)
def higherBandGeometricPrefactor (B Ci Rsp : ℝ) : ℝ := 8*Rsp*(1+B)^2*(1+Ci)
def higherBandGeometricRatio (d D : ℕ) (Cact H base a : ℝ) : ℝ :=
  Cact*(D : ℝ)*H*base^(a/(d : ℝ))

lemma higherBandTargetScale_eq {d r : ℕ} (hr : 2 ≤ r) (N mu : ℝ)
    (hbase : 0 ≤ mu*(1+Real.log N)) :
    higherBandTargetScale d r N mu =
      N*((mu*(1+Real.log N))^(1/(d : ℝ)))^(r-2) := by
  unfold higherBandTargetScale; congr 1
  rw [show ((r : ℝ)-2)/(d : ℝ) = (1/(d : ℝ))*(r-2 : ℕ) by rw [Nat.cast_sub hr]; push_cast; ring,
    Real.rpow_mul_natCast hbase]

lemma higherBandRowActivityCap_geometric_le {d r m D q : ℕ} (hr : 2 ≤ r)
    (a b C lam T B H base P alpha : ℝ) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hbase : 0 ≤ base) (hP : 0 ≤ P) (_hH : 0 ≤ H)
    (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hlog : 1+Real.log T ≤ H)
    (hT2 : T^2 ≤ P*(base^(alpha/(d : ℝ)))^(r-2)) :
    higherBandRowActivityCap d r m D q a b C lam T ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) *
      (D : ℝ)^2 * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) * P *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) H base alpha)^(r-2) := by
  have hb0 : 0 ≤ ordinaryDensityActivityBase a b := by unfold ordinaryDensityActivityBase; positivity
  let Ci := higherBandInterpolationBase d lam
  have hCi : 0 ≤ Ci := by unfold Ci higherBandInterpolationBase; positivity
  have hrEq : r = (r-2)+2 := by omega
  have hrEq1 : r-1 = (r-2)+1 := by omega
  have hbpow : ordinaryDensityActivityBase a b ^ r ≤ (1+B)^2*(1+B)^(r-2) :=
    (pow_le_pow_left₀ hb0 (by linarith : ordinaryDensityActivityBase a b ≤ 1+B) r).trans_eq
      (by nth_rw 1 [hrEq]; rw [pow_add]; ring)
  have hcipow : Ci^(r-1) ≤ (1+Ci)*(1+Ci)^(r-2) :=
    (pow_le_pow_left₀ hCi (by linarith : Ci ≤ 1+Ci) _).trans_eq
      (by rw [hrEq1, pow_succ]; ring)
  have hrpow : (r : ℝ) ≤ (2 : ℝ)^r := by exact_mod_cast Nat.lt_two_pow_self.le
  have hrcoef : 2*(r : ℝ) ≤ 8*(2 : ℝ)^(r-2) := by
    rw [show (2 : ℝ)^r = 4*(2 : ℝ)^(r-2) by nth_rw 1 [hrEq]; rw [pow_add]; norm_num; ring] at hrpow
    nlinarith
  have hcoef : ordinaryDensityActivityBase a b ^ r * Ci^(r-1) * (2*(r : ℝ)) ≤
      (8*(1+B)^2*(1+Ci)) * (higherBandGeometricConstant B Ci)^(r-2) :=
    (mul_le_mul (mul_le_mul hbpow hcipow (by positivity) (by positivity)) hrcoef
      (by positivity) (by positivity)).trans_eq (by unfold higherBandGeometricConstant; rw [mul_pow, mul_pow]; ring)
  have hlog0 : 0 ≤ 1+Real.log T := by linarith [Real.log_nonneg hT]
  have hCact : 0 ≤ higherBandGeometricConstant B Ci := by unfold higherBandGeometricConstant; positivity
  have hDpower : (D : ℝ)^r = (D : ℝ)^2*(D : ℝ)^(r-2) := by nth_rw 1 [hrEq]; rw [pow_add]; ring
  have h := mul_le_mul hcoef (mul_le_mul hT2 (pow_le_pow_left₀ hlog0 hlog (r-2)) (by positivity) (by positivity))
    (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (D : ℝ)^r * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) *
      ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) by positivity)
  convert hh using 1 <;>
    simp only [Ci, higherBandRowActivityCap, higherBandInterpolationCap, higherBandGeometricPrefactor,
      higherBandGeometricRatio, higherBandInterpolationBase, hDpower, mul_pow] <;> ring

lemma higherBandTargetScale_le_N {d r : ℕ} (hr : 2 ≤ r)
    {N mu : ℝ} (hN : 1 ≤ N) (hmu : 0 ≤ mu) (hbase1 : mu*(1+Real.log N) ≤ 1) :
    higherBandTargetScale d r N mu ≤ N := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hpower := Real.rpow_le_one (mul_nonneg hmu hH) hbase1
    (div_nonneg (sub_nonneg.mpr (by exact_mod_cast hr : (2 : ℝ) ≤ r)) (Nat.cast_nonneg d))
  unfold higherBandTargetScale
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower (by linarith : 0 ≤ N)

theorem higherBandRowActivityCap_coarse_geometric_le {d r D q : ℕ} (_hd : 0 < d) (hr : 2 ≤ r)
    (a b C lam N mu ell B : ℝ) (hN : 1 ≤ N) (hmu : 0 ≤ mu)
    (hbase1 : mu*(1+Real.log N) ≤ 1)
    (hT : 1 ≤ min ell (higherBandTargetScale d r N mu)) (hB : 0 ≤ B)
    (hbB : ordinaryDensityActivityBase a b ≤ B) :
    higherBandRowActivityCap d r D D q a b C lam (min ell (higherBandTargetScale d r N mu)) ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) *
      (D : ℝ)^2 * Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) * (N*ell) *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (mu*(1+Real.log N)) 1)^(r-2) := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  have hell : 0 ≤ ell := by linarith [min_le_left ell (higherBandTargetScale d r N mu)]
  have hTN : min ell (higherBandTargetScale d r N mu) ≤ N :=
    (min_le_right _ _).trans (higherBandTargetScale_le_N hr hN hmu hbase1)
  refine higherBandRowActivityCap_geometric_le hr a b C lam _ B _ _ (N*ell) 1 hT hB hbase (by positivity) hH hbB
    (add_le_add_right (Real.log_le_log (by linarith) hTN) 1) ?_
  calc _ ≤ ell * higherBandTargetScale d r N mu := by
          simpa only [pow_two] using mul_le_mul (min_le_left _ _) (min_le_right _ _) (by linarith) hell
    _ = _ := by rw [higherBandTargetScale_eq hr N mu hbase]; ring

theorem higherBandRowActivityCap_fine_geometric_le {d r M D q : ℕ} (_hd : 0 < d) (hr : 2 ≤ r)
    (a b C lam N mu B : ℝ) (hN : 1 ≤ N) (hmu : 0 ≤ mu)
    (hbase1 : mu*(1+Real.log N) ≤ 1) (hT : 1 ≤ higherBandTargetScale d r N mu)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B) :
    higherBandRowActivityCap d r M D q a b C lam (higherBandTargetScale d r N mu) ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam)
        ((∑ h : Fin (2*q+2), |responseWeight q h|)*(2*C^2)) *
      (D : ℝ)^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) * N^2 *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
        (1+Real.log N) (mu*(1+Real.log N)) 2)^(r-2) := by
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hmu hH
  refine higherBandRowActivityCap_geometric_le hr a b C lam _ B _ _ (N^2) 2 hT hB hbase (by positivity) hH hbB
    (add_le_add_right (Real.log_le_log (by linarith) (higherBandTargetScale_le_N hr hN hmu hbase1)) 1) (le_of_eq ?_)
  rw [higherBandTargetScale_eq hr N mu hbase, mul_pow, ← pow_mul, Nat.mul_comm (r-2) 2, pow_mul,
    show ((mu*(1+Real.log N))^(1/(d : ℝ)))^2 = (mu*(1+Real.log N))^(2/(d : ℝ)) by
      rw [← Real.rpow_mul_natCast hbase]; congr 1; push_cast; ring]

def uniformOrdinaryDensityActivityBase (a b c0 : ℝ) : ℝ :=
  Real.exp (1+c0)*((b-a)/a)

lemma ordinaryDensityActivityBase_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ordinaryDensityActivityBase a b = Real.exp (1+densityIntervalExponent a b)*((b-a)/a) := by
  have he : b/densityMargin a b 0 = -((b-a)/a) := by
    unfold densityMargin
    field_simp [ha.ne', (ha.trans hab).ne', (sub_pos.mpr hab).ne']; ring
  unfold ordinaryDensityActivityBase
  rw [he, abs_neg, abs_of_pos (div_pos (sub_pos.mpr hab) ha), exteriorTau_sqrt_ratio a b ha hab]
  rfl

theorem ordinaryDensityActivityBase_shrunk_le {a b t c0 : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hshrink : a+t < b-t)
    (htau : densityIntervalExponent (a+t) (b-t) ≤ c0) :
    ordinaryDensityActivityBase (a+t) (b-t) ≤ uniformOrdinaryDensityActivityBase a b c0 := by
  have hap : 0 < a+t := by linarith
  rw [ordinaryDensityActivityBase_eq hap hshrink]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
    ((div_le_div_iff₀ hap ha).mpr (by nlinarith))
    (div_pos (sub_pos.mpr hshrink) hap).le (Real.exp_pos _).le

def higherBandSourceCact (d : ℕ) (a b c0 lam : ℝ) : ℝ :=
  higherBandGeometricConstant (uniformOrdinaryDensityActivityBase a b c0) (higherBandInterpolationBase d lam)

theorem higherBandSourceCact_positive (d : ℕ) {a b c0 lam : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < higherBandSourceCact d a b c0 lam := by
  have hB : 0 < uniformOrdinaryDensityActivityBase a b c0 :=
    mul_pos (Real.exp_pos _) (div_pos (sub_pos.mpr hab) ha)
  unfold higherBandSourceCact higherBandGeometricConstant higherBandInterpolationBase
  positivity

def cardinalBandDimensionConstant (d : ℕ) : ℝ :=
  (100 * (d : ℝ))^2 * 16 * spatialScaleIntegralConstant d

theorem cardinalBandDimensionConstant_nonneg (d : ℕ) :
    0 ≤ cardinalBandDimensionConstant d := by
  unfold cardinalBandDimensionConstant spatialScaleIntegralConstant; positivity

def lowerAliasSpatialA (d R : ℕ) : ℝ :=
  (R : ℝ)^2 * (2 : ℝ)^d * (1+cardinalBandDimensionConstant d)^R

def lowerAliasSpatialL (d R : ℕ) (c0 K : ℝ) : ℝ :=
  c0*K*((d : ℝ)-4) + R

theorem lowerAliasSpatialA_nonneg (d R : ℕ) : 0 ≤ lowerAliasSpatialA d R := by
  unfold lowerAliasSpatialA
  have := cardinalBandDimensionConstant_nonneg d; positivity

theorem cardinalBandSquareBudget_cutoff_le {d r R : ℕ} {M D K c0 N : ℝ}
    (hd : 4 ≤ d) (hr : r ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (_hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M) (hN : 0 < N)
    (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) :
    (r : ℝ)^2 * (2 : ℝ)^d * cardinalBandSquareBudget d r (N*Real.exp (-c0*D)) ≤
      lowerAliasSpatialA d R * N^(4-(d : ℝ)) * Real.exp (lowerAliasSpatialL d R c0 K * M) := by
  have hC := cardinalBandDimensionConstant_nonneg d
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have he1 : Real.exp (-c0*D) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hellN : N*Real.exp (-c0*D) ≤ N := by nlinarith
  have hHp : 0 < 1+Real.log N := by linarith [Real.log_nonneg (hell.trans hellN)]
  have hlog : 1+Real.log (N*Real.exp (-c0*D)) ≤ 1+Real.log N :=
    add_le_add_right (Real.log_le_log (by positivity) hellN) 1
  have hlog0 : 0 ≤ 1+Real.log (N*Real.exp (-c0*D)) := by linarith [Real.log_nonneg hell]
  have hHexp : 1+Real.log N ≤ Real.exp M := by simpa only [Real.exp_log hHp] using Real.exp_le_exp.mpr hH
  have hlogpower : (1+Real.log (N*Real.exp (-c0*D)))^(r-2) ≤ Real.exp ((R : ℝ)*M) :=
    ((pow_le_pow_left₀ hlog0 (hlog.trans hHexp) _).trans
      (pow_le_pow_right₀ (Real.one_le_exp_iff.mpr hM) (by omega))).trans_eq (Real.exp_nat_mul M R).symm
  have hCpower : (cardinalBandDimensionConstant d)^(r-1) ≤ (1+cardinalBandDimensionConstant d)^R :=
    (pow_le_pow_left₀ hC (by linarith) (r-1)).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hr2 : (r : ℝ)^2 ≤ (R : ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hr 2
  have hscale : (N*Real.exp (-c0*D))^(4-(d : ℝ)) ≤
      N^(4-(d : ℝ)) * Real.exp ((c0*K*((d : ℝ)-4))*M) := by
    rw [Real.mul_rpow hN.le (Real.exp_pos _).le, ← Real.exp_mul]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hDK (show 0 ≤ c0*((d : ℝ)-4) by positivity)]))
      (Real.rpow_nonneg hN.le _)
  have hbound := mul_le_mul (mul_le_mul (mul_le_mul hr2 (le_refl ((2 : ℝ)^d)) (by positivity) (sq_nonneg _))
      hCpower (by positivity) (by positivity))
    (mul_le_mul hscale hlogpower (by positivity) (by positivity)) (by positivity) (by positivity)
  unfold cardinalBandSquareBudget cardinalBandDimensionConstant at hbound
  calc
    _ = ((r : ℝ)^2 * (2 : ℝ)^d * (cardinalBandDimensionConstant d)^(r-1)) *
        ((N*Real.exp (-c0*D))^(4-(d : ℝ)) * (1+Real.log (N*Real.exp (-c0*D)))^(r-2)) := by
      unfold cardinalBandSquareBudget cardinalBandDimensionConstant; ring
    _ ≤ _ := hbound
    _ = _ := by
      unfold lowerAliasSpatialA lowerAliasSpatialL cardinalBandDimensionConstant
      rw [show Real.exp ((c0*K*((d : ℝ)-4)+(R : ℝ))*M) =
        Real.exp ((c0*K*((d : ℝ)-4))*M) * Real.exp ((R : ℝ)*M) by rw [← Real.exp_add]; congr 1; ring]
      ring

def lowerAliasSpatialFixedL (d : ℕ) (θ c0 : ℝ) : ℝ :=
  lowerAliasSpatialL d (lowerAliasFineTargetBound d θ c0) c0 (((d : ℝ)+8)/4+1)

theorem lowerSaddleD_le_fixed_linear {d m x : ℝ} (hd : 0 < d)
    (hM : 1 ≤ (lowerSaddleM m x : ℝ)) :
    (lowerSaddleD d m x : ℝ) ≤ ((d+8)/4+1) * lowerSaddleM m x := by
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (d+8)/4*(lowerSaddleM m x : ℝ) by positivity)
  change (lowerSaddleD d m x : ℝ) < (d+8)/4*(lowerSaddleM m x : ℝ)+1 at hceil
  nlinarith

theorem lowerAliasSpatialFixedL_nonneg {d : ℕ} (hd : 4 ≤ d) (θ : ℝ)
    {c0 : ℝ} (hc0 : 0 ≤ c0) : 0 ≤ lowerAliasSpatialFixedL d θ c0 := by
  unfold lowerAliasSpatialFixedL lowerAliasSpatialL
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

end HierarchyAndScale

end NearlyMinimax
