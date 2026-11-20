module

public import NearlyMinimax.CardinalCoefficientBounds
public import NearlyMinimax.CardinalWeightedBounds
public import NearlyMinimax.CardinalSeparatedBand

@[expose] public section

/-! Actual scale-band spatial integrals used in the interpolation matrix
squared-norm bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def anchoredCardinalScale {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalScale lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i

section
variable {d n : ℕ} (i : Fin n)

section
variable (lam : ℝ) (x : Covariate d)

theorem anchored_cardinal_scale_product_actual
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalScale i lam x t Y = ∏ j : SpatialScaleIndex i,
      t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x (Y j))) := by
  unfold anchoredCardinalScale
  norm_num [spatial_cardinal_scale_product, anchored_configuration_same, anchored_configuration_other]

theorem anchored_cardinal_scale_continuous_actual :
    Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2) := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialSquaredDistance
  fun_prop

theorem anchored_cardinal_scale_nonnegative_actual
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) (Y : SpatialScaleIndex i → Covariate d) :
    0 ≤ anchoredCardinalScale i lam x t Y :=
  by apply spatial_cardinal_scale_nonnegative <;> assumption

end

section
variable {lam T : ℝ}
    (hlam : 0 ≤ lam) (hT : 1 ≤ T)
include hlam hT

theorem anchored_cardinal_scale_upper_bound (x : Covariate d) (t : SpatialScaleVector i)
    (ht : t ∈ spatialScaleDomain i T) (Y : SpatialScaleIndex i → Covariate d) :
    |anchoredCardinalScale i lam x t Y| ≤ (T ^ 2 * lam ^ 2) ^ Fintype.card (SpatialScaleIndex i) := by
  rw [abs_of_nonneg (anchored_cardinal_scale_nonnegative_actual i lam x t ht.1 Y),
    anchored_cardinal_scale_product_actual]
  calc
    _ ≤ ∏ _j : SpatialScaleIndex i, T ^ 2 * lam ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact mul_nonneg (mul_nonneg (ht.1 j) (sq_nonneg _)) (Real.exp_pos _).le
      · intro j hj
        have htj := ht.1 j
        have hdist : 0 ≤ spatialSquaredDistance x (Y j) := Finset.sum_nonneg (fun r _ => sq_nonneg _)
        have he :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg htj hlam) hdist))
        have hsmall := (spatial_scale_domain_subset_box i T hT ht).2 j
        exact (mul_le_mul_of_nonneg_left he (mul_nonneg htj (sq_nonneg _))).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_right (show t j ≤ T ^ 2 by linarith) (sq_nonneg lam))
    _ = _ := by simp

theorem anchored_cardinal_band_scale_joint_integrable (L : ℝ) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2)
      ((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod (spatialPatchDesignMeasure i d)) := by
  letI := spatial_scale_measure_finite i T hT
  have hμ : volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L) ≤ spatialScaleMeasure i T :=
    Measure.restrict_mono_set volume Set.diff_subset
  letI : IsFiniteMeasure (volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)) :=
    isFiniteMeasure_of_le (spatialScaleMeasure i T) hμ
  apply Integrable.of_bound (anchored_cardinal_scale_continuous_actual i lam x).aestronglyMeasurable
    ((T ^ 2 * lam ^ 2) ^ Fintype.card (SpatialScaleIndex i))
  have hae : ∀ᵐ z ∂((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod
      (spatialPatchDesignMeasure i d)), z.1 ∈ spatialScaleDomain i T := by
    apply (Measure.ae_prod_iff_ae_ae ((spatial_scale_domain_isClosed i T).measurableSet.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    simp_all
  filter_upwards [hae] with z hz
  solve_by_elim [anchored_cardinal_scale_upper_bound]

end

end

def spatialScaleIntegralConstant (d : ℕ) : ℝ :=
  (spatialInterpolationLambda d) ^ 2 * Real.exp (1 / 2) *
    (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d

section
variable {d n : ℕ}

theorem anchored_cardinal_scale_spatial_integral_product (i : Fin n) (lam : ℝ)
    (x : Covariate d) (t : SpatialScaleVector i) :
    (∫ Y, anchoredCardinalScale i lam x t Y ∂spatialPatchDesignMeasure i d) =
      ∏ j : SpatialScaleIndex i, lam ^ 2 * ∫ y in spatialPatchBox d,
        t j * Real.exp (-(t j * lam * spatialSquaredDistance x y)) := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialPatchDesignMeasure
  rw [integral_fintype_prod_eq_prod
    (fun (j : SpatialScaleIndex i) (y : Covariate d) =>
      t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x y)))]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← integral_const_mul]
  ring

theorem anchored_cardinal_scale_spatial_integral_decay (hd : 0 < d) (i : Fin n)
    (x : Covariate d) (hx : x ∈ spatialPatchBox d) (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    (∫ Y, anchoredCardinalScale i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤
      (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (1 - (d : ℝ) / 2) := by
  rw [anchored_cardinal_scale_spatial_integral_product]
  have h : (∏ j : SpatialScaleIndex i, (spatialInterpolationLambda d) ^ 2 *
      ∫ y in spatialPatchBox d, t j * Real.exp (-(t j * spatialInterpolationLambda d * spatialSquaredDistance x y))) ≤
      ∏ j : SpatialScaleIndex i, spatialScaleIntegralConstant d * (1 + t j) ^ (1 - (d : ℝ) / 2) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      apply mul_nonneg (sq_nonneg _)
      apply integral_nonneg
      intro y
      exact mul_nonneg (ht j) (Real.exp_pos _).le
    · intro j hj
      have hdec := mul_le_mul_of_nonneg_left
        (spatial_scale_exponential_patch_integral_decay hd (t j) (ht j) x hx)
        (sq_nonneg (spatialInterpolationLambda d))
      simpa only [spatialScaleIntegralConstant, mul_assoc] using hdec
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

/-- The actual squared-kernel spatial decay integrated over a true
truncated scale band, with every Fubini exchange justified. -/
theorem anchored_cardinal_band_scale_spatial_integral_bound (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) :
    (∫ Y, (∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
      anchoredCardinalScale i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialScaleIntegralConstant d) ^ (n - 1) *
        L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2) := by
  have hd0 : 0 < d := by omega
  have hdR : (5 : ℝ) ≤ d := by simp_all
  let b : ℝ := ((d : ℝ) - 4) / 2
  have hb : (1 / 2 : ℝ) ≤ b := by dsimp [b]; linarith
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hC : 0 ≤ spatialScaleIntegralConstant d := by unfold spatialScaleIntegralConstant; positivity
  have h := spatial_scale_tail_prod_integral_le (spatialPatchDesignMeasure i d) hn i hb hL hC
    ((spatial_scale_domain_isClosed i T).measurableSet.diff (spatial_scale_domain_isClosed i L).measurableSet)
    (fun _ ht => ⟨ht.1.1, ht.2⟩) (anchored_cardinal_band_scale_joint_integrable i hlam hT L x)
    (fun t ht => by simpa only [show 1-(d : ℝ)/2 = -b-1 by dsimp [b]; ring] using
      anchored_cardinal_scale_spatial_integral_decay hd0 i x hx t ht)
  simpa only [show -2*b = 4-(d : ℝ) by dsimp [b]; ring] using h

end

end NearlyMinimax
