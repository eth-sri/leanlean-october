module

public import NearlyMinimax.CardinalScaleTail

@[expose] public section

/-! Actual spatial interpolation bias: genuine patch integrals of the
integrated cardinal-weight defect, using Gaussian decay and scale tails. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable {d n : ℕ} {i : Fin n} {lam : ℝ} (hlam : 0 ≤ lam) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d)

def anchoredPatchConfiguration : DesignSample d n :=
  fun j => if h : j ≠ i then Y ⟨j, h⟩ else x

def spatialPatchDesignMeasure (i : Fin n) (d : ℕ) :
    Measure (SpatialScaleIndex i → Covariate d) :=
  Measure.pi (fun _ => volume.restrict (spatialPatchBox d))

instance spatialPatchCube_finite (d : ℕ) :
    IsFiniteMeasure (volume.restrict (spatialPatchBox d)) := by
  apply isFiniteMeasure_restrict.mpr
  exact isCompact_Icc.measure_ne_top

instance spatialPatchDesignMeasure_finite (i : Fin n) (d : ℕ) :
    IsFiniteMeasure (spatialPatchDesignMeasure i d) := by
  unfold spatialPatchDesignMeasure
  infer_instance

def anchoredCardinalScaleWeight (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalWeight lam (spatialScaleExtend t) (anchoredPatchConfiguration x Y) i

theorem anchored_configuration_same : anchoredPatchConfiguration x Y i = x := by
  simp [anchoredPatchConfiguration]

theorem anchored_configuration_other (j : SpatialScaleIndex i) :
    anchoredPatchConfiguration x Y j.val = Y j := by
  simp [anchoredPatchConfiguration, j.property]

theorem anchored_cardinal_scale_joint_continuous (i : Fin n) (lam : ℝ) (x : Covariate d) :
    Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight lam x z.1 z.2) := by
  simp_rw [anchoredCardinalScaleWeight, spatial_cardinal_weight_scale_product, anchored_configuration_same, anchored_configuration_other]
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

include hlam in
theorem anchored_cardinal_scale_integrable :
    IntegrableOn (fun t => anchoredCardinalScaleWeight lam x t Y) (Ici 0) :=
  spatial_cardinal_weight_orthant_integrable i hlam _

include hlam in
theorem anchored_cardinal_scale_norm_integral_le :
    (∫ t in Ici 0, ‖anchoredCardinalScaleWeight lam x t Y‖) ≤ 1 := by
  have he : (fun t => ‖anchoredCardinalScaleWeight lam x t Y‖) =ᵐ[volume.restrict (Ici 0)]
      (fun t => anchoredCardinalScaleWeight lam x t Y) := by
    filter_upwards [spatial_cardinal_weight_orthant_nonnegative ..] with t ht
    simpa
  rw [integral_congr_ae he]
  solve_by_elim [spatial_cardinal_weight_orthant_integral_le_one]

end

section
variable {d n : ℕ} (i : Fin n) {lam : ℝ} (hlam : 0 ≤ lam) (T : ℝ) (x : Covariate d)

include hlam in
/-- Actual joint integrability, derived from the exact Gamma-normalized scale
weights and the finite patch measure. -/
theorem anchored_cardinal_scale_joint_integrable :
    Integrable (fun z =>
      anchoredCardinalScaleWeight lam x z.1 z.2)
      ((volume.restrict (Ici 0)).prod (spatialPatchDesignMeasure i d)) := by
  have hc := anchored_cardinal_scale_joint_continuous i lam x
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun Y => anchored_cardinal_scale_integrable hlam x Y), ?_⟩
  exact (integrable_const 1).mono'
    hc.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact anchored_cardinal_scale_norm_integral_le hlam x Y)

include hlam in
/-- The tail restriction preserves genuine joint integrability. -/
theorem anchored_cardinal_tail_joint_integrable :
    Integrable (fun z =>
      anchoredCardinalScaleWeight lam x z.1 z.2)
      ((volume.restrict (Ici 0 \ spatialScaleDomain i T)).prod (spatialPatchDesignMeasure i d)) := (anchored_cardinal_scale_joint_integrable i hlam x).mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set _ Set.diff_subset) le_rfl)

theorem anchored_cardinal_spatial_integral_product (lam : ℝ)
    (x : Covariate d) (t : SpatialScaleVector i) :
    (∫ Y, anchoredCardinalScaleWeight lam x t Y ∂spatialPatchDesignMeasure i d) =
      ∏ j, ∫ y in spatialPatchBox d, spatialUnaryWeight lam (t j) x y := by
  simp_rw [anchoredCardinalScaleWeight, spatial_cardinal_weight_scale_product, anchored_configuration_same, anchored_configuration_other]
  exact integral_fintype_prod_eq_prod _

end

theorem anchored_cardinal_spatial_integral_decay {d n : ℕ} (hd : 0 < d) {i : Fin n}
    {x : Covariate d} (hx : x ∈ spatialPatchBox d) {t : SpatialScaleVector i} (ht : t ∈ Ici 0) :
    (∫ Y, anchoredCardinalScaleWeight (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤
      (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (-(d : ℝ) / 2 - 1) := by
  rw [anchored_cardinal_spatial_integral_product]
  have h : (∏ j, ∫ y in spatialPatchBox d,
      spatialUnaryWeight (spatialInterpolationLambda d) (t j) x y) ≤
      ∏ j, spatialUnaryIntegralConstant d * (1 + t j) ^ (-(d : ℝ) / 2 - 1) := by
    apply Finset.prod_le_prod₀
    · intro j _
      apply integral_nonneg
      intro y
      have htj : 0 ≤ t j := ht j
      unfold spatialUnaryWeight
      positivity
    · intro j _
      solve_by_elim [spatial_unary_patch_integral_decay]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

variable {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n) (i : Fin n) {lam : ℝ} {x : Covariate d}
    (hx : x ∈ spatialPatchBox d) {T : ℝ} (hT : 1 ≤ T)

include hd hn hx hT in
/-- The actual spatial-and-scale complement integral, with all Fubini
exchanges justified by previously derived joint integrability. -/
theorem anchored_cardinal_tail_spatial_integral_bound :
    (∫ Y, (∫ t in Ici 0 \ spatialScaleDomain i T,
      anchoredCardinalScaleWeight (spatialInterpolationLambda d) x t Y)
      ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
        T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hjoint := anchored_cardinal_tail_joint_integrable i hlam T x
  rw [((integral_prod_symm _ hjoint).symm.trans (integral_prod _ hjoint))]
  have hpowint := (spatial_scale_complement_power_integrable hn i
    (by positivity : 0 < (d : ℝ) / 2) T).const_mul
      ((spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
  have hdom : (fun t =>
      ∫ Y, anchoredCardinalScaleWeight (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤ᵐ[
        volume.restrict (Ici 0 \ spatialScaleDomain i T)]
      (fun t => (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (-(d : ℝ) / 2 - 1)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)] with t ht
    exact anchored_cardinal_spatial_integral_decay hd hx ht.1
  have hneg : -d / 2 = -((d : ℝ) / 2) := by ring
  rw [hneg] at hdom
  have h := integral_mono_ae hjoint.integral_prod_left hpowint hdom
  rw [integral_const_mul, spatial_scale_index_card] at h
  have htail := spatial_scale_complement_power_integral_le hn i
    (by linarith : (1 / 2) ≤ (d : ℝ) / 2) hT
  have hh := mul_le_mul_of_nonneg_left htail
    (by unfold spatialUnaryIntegralConstant; positivity :
      0 ≤ (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
  have he : -2 * (d / 2) = -(d : ℝ) := by ring
  rw [spatial_scale_index_card, he] at hh
  exact h.trans (by simpa only [mul_pow, mul_assoc,  mul_left_comm] using hh)

def anchoredCardinalDefect {i : Fin n} (lam T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  1 - integratedCardinalWeight lam T (anchoredPatchConfiguration x Y) i

theorem anchored_cardinal_defect_mem_unit {i : Fin n} {lam : ℝ} (hlam : 0 ≤ lam)
    (T : ℝ) (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalDefect lam T x Y ∈ Icc 0 1 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam (anchoredPatchConfiguration x Y)
  simp_all [anchoredCardinalDefect]

include hd in
/-- The true integrated cardinal defect equals the complementary scale
integral almost everywhere under the actual Lebesgue patch design. -/
theorem anchored_cardinal_defect_ae_eq_tail (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    (fun Y => anchoredCardinalDefect lam T x Y) =ᵐ[spatialPatchDesignMeasure i d]
      (fun Y => ∫ t in Ici 0 \ spatialScaleDomain i T,
        anchoredCardinalScaleWeight lam x t Y) := by
  filter_upwards [(by letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩; apply ae_all_iff.mpr; solve_by_elim [Measure.ae_eval_ne] : ∀ᵐ (Y : SpatialScaleIndex i → Covariate d) ∂spatialPatchDesignMeasure i d, ∀ (j : SpatialScaleIndex i), Y j ≠ x)] with Y hY
  have hU : ∀ j, j ≠ i → anchoredPatchConfiguration x Y i ≠ anchoredPatchConfiguration x Y j := by
    grind [anchoredPatchConfiguration]
  solve_by_elim [integrated_cardinal_weight_defect_eq_complement]

include hd in
theorem anchored_cardinal_defect_integrable (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    Integrable (anchoredCardinalDefect lam T x) (spatialPatchDesignMeasure i d) := ((anchored_cardinal_tail_joint_integrable i hlam.le T x).integral_prod_right).congr (anchored_cardinal_defect_ae_eq_tail hd i hlam T x).symm

include hd in
theorem anchored_cardinal_defect_square_integrable (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    Integrable (fun Y => anchoredCardinalDefect lam T x Y ^ 2) (spatialPatchDesignMeasure i d) := by
  have h := anchored_cardinal_defect_integrable hd i hlam T x
  exact h.mono' (by
    fun_prop) (Filter.Eventually.of_forall fun Y => by
    have hr := anchored_cardinal_defect_mem_unit hlam.le T x Y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hr.1, hr.2])

include hd hn hx hT in
/-- The actual squared interpolation-bias bound, without a desired bias or
score premise. The only parameters are the dimension, number of points, scale
cutoff and the actual fixed spatial anchor. -/
theorem anchored_cardinal_defect_square_integral_le :
    (∫ Y, anchoredCardinalDefect (spatialInterpolationLambda d) T x Y ^ 2
      ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
        T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
  have hlam : 0 < spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  calc
    _ ≤ _ :=
      integral_mono_ae (anchored_cardinal_defect_square_integrable hd i hlam T x)
        (anchored_cardinal_defect_integrable hd i hlam T x) (Filter.Eventually.of_forall fun Y => by
          have hr := anchored_cardinal_defect_mem_unit hlam.le T x Y
          nlinarith [hr.1, hr.2])
    _ = _ :=
      integral_congr_ae (anchored_cardinal_defect_ae_eq_tail hd i hlam T x)
    _ ≤ _ := anchored_cardinal_tail_spatial_integral_bound hd hn i hx hT

end NearlyMinimax
