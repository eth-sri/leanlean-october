module

public import NearlyMinimax.CardinalScaleTail

@[expose] public section

/-! Actual spatial interpolation bias: genuine patch integrals of the
integrated cardinal-weight defect, using Gaussian decay and scale tails. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax

variable {d n : ℕ} (i : Fin n)

def anchoredPatchConfiguration (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : Fin n → Covariate d :=
  fun j => if h : j ≠ i then Y ⟨j, h⟩ else x

def spatialPatchDesignMeasure {n : ℕ} (i : Fin n) (d : ℕ) :
    Measure (SpatialScaleIndex i → Covariate d) :=
  Measure.pi (fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d))

instance spatialPatchCube_finite (d : ℕ) :
    IsFiniteMeasure ((volume : Measure (Covariate d)).restrict (spatialPatchBox d)) := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top

instance spatialPatchDesignMeasure_finite {n : ℕ} (i : Fin n) (d : ℕ) :
    IsFiniteMeasure (spatialPatchDesignMeasure i d) := by
  unfold spatialPatchDesignMeasure
  infer_instance

section
variable (i : Fin n)

def anchoredCardinalScaleWeight (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalWeight lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i

section
variable (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d)

theorem anchored_configuration_same 
    : anchoredPatchConfiguration i x Y i = x := by
  simp [anchoredPatchConfiguration]

theorem anchored_configuration_other 
    (j : SpatialScaleIndex i) :
    anchoredPatchConfiguration i x Y j.val = Y j := by
  simp [anchoredPatchConfiguration, j.property]

end

section
variable (lam : ℝ) (x : Covariate d)

theorem anchored_cardinal_scale_product 
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalScaleWeight i lam x t Y =
      ∏ j, spatialUnaryWeight lam (t j) x (Y j) := by
  unfold anchoredCardinalScaleWeight
  rw [spatial_cardinal_weight_scale_product]
  simp_rw [anchored_configuration_same, anchored_configuration_other]

theorem anchored_cardinal_scale_joint_continuous :
    Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2) := by
  simp_rw [anchored_cardinal_scale_product]
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

end

section
variable {lam : ℝ}

theorem anchored_cardinal_scale_integrable (hlam : 0 ≤ lam)
    (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    IntegrableOn (fun t => anchoredCardinalScaleWeight i lam x t Y) (Ici 0) :=
  spatial_cardinal_weight_orthant_integrable i lam hlam (anchoredPatchConfiguration i x Y)

theorem anchored_cardinal_scale_norm_integral_le 
    (hlam : 0 ≤ lam) (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    (∫ t : SpatialScaleVector i in Ici 0, ‖anchoredCardinalScaleWeight i lam x t Y‖) ≤ 1 := by
  have he : (fun t => ‖anchoredCardinalScaleWeight i lam x t Y‖) =ᵐ[volume.restrict (Ici 0)]
      (fun t => anchoredCardinalScaleWeight i lam x t Y) := by
    filter_upwards [spatial_cardinal_weight_orthant_nonnegative i lam (anchoredPatchConfiguration i x Y)] with t ht
    have hnn : 0 ≤ anchoredCardinalScaleWeight i lam x t Y := ht
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [integral_congr_ae he]
  exact spatial_cardinal_weight_orthant_integral_le_one i lam hlam (anchoredPatchConfiguration i x Y)

/-- Actual joint integrability, derived from the exact Gamma-normalized scale
weights and the finite patch measure. -/
theorem anchored_cardinal_scale_joint_integrable 
    (hlam : 0 ≤ lam) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0)).prod (spatialPatchDesignMeasure i d)) := by
  have hc := anchored_cardinal_scale_joint_continuous i lam x
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun Y => anchored_cardinal_scale_integrable i hlam x Y), ?_⟩
  exact (integrable_const (1 : ℝ)).mono'
    hc.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact anchored_cardinal_scale_norm_integral_le i hlam x Y)

/-- The tail restriction preserves genuine joint integrability. -/
theorem anchored_cardinal_tail_joint_integrable 
    (hlam : 0 ≤ lam) (T : ℝ) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0 \ spatialScaleDomain i T)).prod (spatialPatchDesignMeasure i d)) := (anchored_cardinal_scale_joint_integrable i hlam x).mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set _ Set.diff_subset) le_rfl)

end

theorem anchored_cardinal_spatial_integral_product (lam : ℝ)
    (x : Covariate d) (t : SpatialScaleVector i) :
    (∫ Y, anchoredCardinalScaleWeight i lam x t Y ∂spatialPatchDesignMeasure i d) =
      ∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d, spatialUnaryWeight lam (t j) x y := by
  simp_rw [anchored_cardinal_scale_product]
  unfold spatialPatchDesignMeasure
  exact integral_fintype_prod_eq_prod
    (fun (j : SpatialScaleIndex i) (y : Covariate d) => spatialUnaryWeight lam (t j) x y)

end

theorem anchored_cardinal_spatial_integral_decay (hd : 0 < d) (i : Fin n)
    (x : Covariate d) (hx : x ∈ spatialPatchBox d) (t : SpatialScaleVector i) (ht : t ∈ Ici 0) :
    (∫ Y, anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤
      (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (-(d : ℝ) / 2 - 1) := by
  rw [anchored_cardinal_spatial_integral_product]
  have h : (∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d,
      spatialUnaryWeight (spatialInterpolationLambda d) (t j) x y) ≤
      ∏ j : SpatialScaleIndex i, spatialUnaryIntegralConstant d * (1 + t j) ^ (-(d : ℝ) / 2 - 1) := by
    apply Finset.prod_le_prod₀
    · intro j _
      apply integral_nonneg
      intro y
      have htj : (0 : ℝ) ≤ t j := ht j
      unfold spatialUnaryWeight
      positivity
    · intro j _
      exact spatial_unary_patch_integral_decay hd (t j) (ht j) x hx
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

/-- The actual spatial-and-scale complement integral, with all Fubini
exchanges justified by previously derived joint integrability. -/
theorem anchored_cardinal_tail_spatial_integral_bound (hd : 0 < d) (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d) {T : ℝ} (hT : 1 ≤ T) :
    (∫ Y, (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y)
      ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
        T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hjoint := anchored_cardinal_tail_joint_integrable i hlam T x
  have hfub :
      (∫ Y, (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
        anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d) =
        ∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
          (∫ Y, anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) :=
    (integral_prod_symm _ hjoint).symm.trans (integral_prod _ hjoint)
  rw [hfub]
  have hpowint := (spatial_scale_complement_power_integrable hn i
    (by positivity : (0 : ℝ) < (d : ℝ) / 2) T).const_mul
      ((spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
  have hdom : (fun t : SpatialScaleVector i =>
      ∫ Y, anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤ᵐ[
        volume.restrict (Ici 0 \ spatialScaleDomain i T)]
      (fun t => (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (-(d : ℝ) / 2 - 1)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)] with t ht
    exact anchored_cardinal_spatial_integral_decay hd i x hx t ht.1
  have hneg : -(d : ℝ) / 2 = -((d : ℝ) / 2) := by ring
  rw [hneg] at hdom
  have h := integral_mono_ae hjoint.integral_prod_left hpowint hdom
  rw [integral_const_mul, spatial_scale_index_card] at h
  have htail := spatial_scale_complement_power_integral_le hn i
    (by linarith : (1 / 2 : ℝ) ≤ (d : ℝ) / 2) hT
  have hh := mul_le_mul_of_nonneg_left htail
    (by unfold spatialUnaryIntegralConstant; positivity :
      0 ≤ (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
  have he : -2 * ((d : ℝ) / 2) = -(d : ℝ) := by ring
  rw [spatial_scale_index_card, he] at hh
  calc
    _ ≤ _ := h
    _ ≤ _ := by simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh

section
variable (i : Fin n)

def anchoredCardinalDefect (lam T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  1 - integratedCardinalWeight lam T (anchoredPatchConfiguration i x Y) i

theorem anchored_cardinal_defect_mem_unit {lam : ℝ} (hlam : 0 ≤ lam)
    (T : ℝ) (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalDefect i lam T x Y ∈ Icc (0 : ℝ) 1 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam (anchoredPatchConfiguration i x Y)
  unfold anchoredCardinalDefect
  constructor <;> linarith [h.1, h.2]

end

theorem anchored_patch_collision_null (hd : 0 < d) (i : Fin n) (x : Covariate d) :
    ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ j : SpatialScaleIndex i, Y j ≠ x := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply ae_all_iff.mpr
  intro j
  exact Measure.ae_eval_ne (fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d)) j x

/-- The true integrated cardinal defect equals the complementary scale
integral almost everywhere under the actual Lebesgue patch design. -/
theorem anchored_cardinal_defect_ae_eq_tail (hd : 0 < d) (i : Fin n)
    {lam : ℝ} (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    (fun Y => anchoredCardinalDefect i lam T x Y) =ᵐ[spatialPatchDesignMeasure i d]
      (fun Y => ∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
        anchoredCardinalScaleWeight i lam x t Y) := by
  filter_upwards [anchored_patch_collision_null hd i x] with Y hY
  have hU : ∀ j, j ≠ i → anchoredPatchConfiguration i x Y i ≠ anchoredPatchConfiguration i x Y j := by
    intro j hj
    rw [anchored_configuration_same]
    have he : anchoredPatchConfiguration i x Y j = Y ⟨j, hj⟩ := by
      simp [anchoredPatchConfiguration, hj]
    rw [he]
    exact (hY ⟨j, hj⟩).symm
  exact integrated_cardinal_weight_defect_eq_complement i lam T hlam (anchoredPatchConfiguration i x Y) hU

theorem anchored_cardinal_defect_integrable (hd : 0 < d) (i : Fin n)
    {lam : ℝ} (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    Integrable (anchoredCardinalDefect i lam T x) (spatialPatchDesignMeasure i d) := by
  have h := (anchored_cardinal_tail_joint_integrable i hlam.le T x).integral_prod_right
  exact h.congr (anchored_cardinal_defect_ae_eq_tail hd i hlam T x).symm

theorem anchored_cardinal_defect_square_integrable (hd : 0 < d) (i : Fin n)
    {lam : ℝ} (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    Integrable (fun Y => anchoredCardinalDefect i lam T x Y ^ 2) (spatialPatchDesignMeasure i d) := by
  have h := anchored_cardinal_defect_integrable hd i hlam T x
  have hmeas : AEStronglyMeasurable (fun Y => anchoredCardinalDefect i lam T x Y ^ 2)
      (spatialPatchDesignMeasure i d) := by
    have hh := h.aestronglyMeasurable.mul h.aestronglyMeasurable
    change AEStronglyMeasurable (fun Y => anchoredCardinalDefect i lam T x Y *
      anchoredCardinalDefect i lam T x Y) (spatialPatchDesignMeasure i d) at hh
    simpa only [pow_two] using hh
  exact h.mono' hmeas (Filter.Eventually.of_forall fun Y => by
    have hr := anchored_cardinal_defect_mem_unit i hlam.le T x Y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hr.1, hr.2])

/-- The actual squared interpolation-bias bound, without a desired bias or
score premise. The only parameters are the dimension, number of points, scale
cutoff and the actual fixed spatial anchor. -/
theorem anchored_cardinal_defect_square_integral_le (hd : 0 < d) (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d) {T : ℝ} (hT : 1 ≤ T) :
    (∫ Y, anchoredCardinalDefect i (spatialInterpolationLambda d) T x Y ^ 2
      ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
        T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
  have hlam : 0 < spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  calc
    _ ≤ ∫ Y, anchoredCardinalDefect i (spatialInterpolationLambda d) T x Y ∂spatialPatchDesignMeasure i d :=
      integral_mono_ae (anchored_cardinal_defect_square_integrable hd i hlam T x)
        (anchored_cardinal_defect_integrable hd i hlam T x) (Filter.Eventually.of_forall fun Y => by
          have hr := anchored_cardinal_defect_mem_unit i hlam.le T x Y
          nlinarith [hr.1, hr.2])
    _ = ∫ Y, (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
          anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d :=
      integral_congr_ae (anchored_cardinal_defect_ae_eq_tail hd i hlam T x)
    _ ≤ _ := anchored_cardinal_tail_spatial_integral_bound hd hn i x hx hT

end NearlyMinimax
