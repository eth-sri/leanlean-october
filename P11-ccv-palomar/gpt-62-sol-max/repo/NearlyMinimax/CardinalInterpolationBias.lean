module

public import NearlyMinimax.CardinalScaleTail
public import NearlyMinimax.ProductSectionBounds

@[expose] public section

/-! Actual spatial interpolation bias: genuine patch integrals of the
integrated cardinal-weight defect, using Gaussian decay and scale tails. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def anchoredPatchConfiguration {d n : ℕ} (i : Fin n) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : Fin n → Covariate d :=
  fun j => if h : j ≠ i then Y ⟨j, h⟩ else x

def spatialPatchDesignMeasure {n : ℕ} (i : Fin n) (d : ℕ) :
    Measure (SpatialScaleIndex i → Covariate d) :=
  Measure.pi (fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d))

instance spatialPatchDesignMeasure_finite {n : ℕ} (i : Fin n) (d : ℕ) :
    IsFiniteMeasure (spatialPatchDesignMeasure i d) := by
  unfold spatialPatchDesignMeasure
  infer_instance

def anchoredCardinalScaleWeight {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalWeight lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i

section
variable {d n : ℕ}

section
variable (i : Fin n)

section
variable (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d)

theorem anchored_configuration_same : anchoredPatchConfiguration i x Y i = x := by
  simp [anchoredPatchConfiguration]

theorem anchored_configuration_other (j : SpatialScaleIndex i) :
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
  norm_num [spatial_cardinal_weight_scale_product, anchored_configuration_same, anchored_configuration_other]

theorem anchored_cardinal_scale_joint_continuous :
    Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2) := by
  simp_rw [anchored_cardinal_scale_product]
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

end

section
variable {lam : ℝ} (hlam : 0 ≤ lam)
include hlam

theorem anchored_cardinal_scale_integrable
    (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    IntegrableOn (fun t => anchoredCardinalScaleWeight i lam x t Y) (Ici 0) :=
  by apply spatial_cardinal_weight_orthant_integrable <;> assumption

theorem anchored_cardinal_scale_norm_integral_le (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    (∫ t : SpatialScaleVector i in Ici 0, ‖anchoredCardinalScaleWeight i lam x t Y‖) ≤ 1 := by
  have he : (fun t => ‖anchoredCardinalScaleWeight i lam x t Y‖) =ᵐ[volume.restrict (Ici 0)]
      (fun t => anchoredCardinalScaleWeight i lam x t Y) := by
    filter_upwards [spatial_cardinal_weight_orthant_nonnegative i lam (anchoredPatchConfiguration i x Y)] with t ht
    simp_all <;> positivity
  rw [integral_congr_ae he]
  apply spatial_cardinal_weight_orthant_integral_le_one <;> assumption

/-- Actual joint integrability, derived from the exact Gamma-normalized scale
weights and the finite patch measure. -/
theorem anchored_cardinal_scale_joint_integrable (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0)).prod (spatialPatchDesignMeasure i d)) := by
  exact integrable_prod_of_section_norm_le (anchored_cardinal_scale_joint_continuous i lam x).aestronglyMeasurable
    (integrable_const (1 : ℝ)) (.of_forall (anchored_cardinal_scale_integrable i hlam x))
    (.of_forall (anchored_cardinal_scale_norm_integral_le i hlam x))

/-- The tail restriction preserves genuine joint integrability. -/
theorem anchored_cardinal_tail_joint_integrable (T : ℝ) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0 \ spatialScaleDomain i T)).prod (spatialPatchDesignMeasure i d)) := by
  exact (anchored_cardinal_scale_joint_integrable i hlam x).mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set _ Set.diff_subset) le_rfl)

end

theorem anchored_cardinal_spatial_integral_product (lam : ℝ)
    (x : Covariate d) (t : SpatialScaleVector i) :
    (∫ Y, anchoredCardinalScaleWeight i lam x t Y ∂spatialPatchDesignMeasure i d) =
      ∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d, spatialUnaryWeight lam (t j) x y := by
  simp_rw [anchored_cardinal_scale_product]
  solve_by_elim [integral_fintype_prod_eq_prod]

end

section
variable (hd : 0 < d)
include hd

theorem anchored_cardinal_spatial_integral_decay (i : Fin n)
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
      solve_by_elim [spatial_unary_patch_integral_decay]
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

/-- The actual spatial-and-scale complement integral, with all Fubini
exchanges justified by previously derived joint integrability. -/
theorem anchored_cardinal_tail_spatial_integral_bound (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d) {T : ℝ} (hT : 1 ≤ T) :
    (∫ Y, (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      anchoredCardinalScaleWeight i (spatialInterpolationLambda d) x t Y)
      ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialUnaryIntegralConstant d) ^ (n - 1) *
        T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hC : 0 ≤ spatialUnaryIntegralConstant d := by unfold spatialUnaryIntegralConstant; positivity
  have h := spatial_scale_tail_prod_integral_le (spatialPatchDesignMeasure i d) hn i
    (show (1 / 2 : ℝ) ≤ (d : ℝ)/2 by linarith) hT hC
    (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
    Subset.rfl (anchored_cardinal_tail_joint_integrable i hlam T x)
    (fun t ht => by simpa only [neg_div] using anchored_cardinal_spatial_integral_decay hd i x hx t ht)
  simpa only [show -2*((d : ℝ)/2) = -(d : ℝ) by ring] using h

end

end

def anchoredCardinalDefect {d n : ℕ} (i : Fin n) (lam T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  1 - integratedCardinalWeight lam T (anchoredPatchConfiguration i x Y) i

section
variable {d n : ℕ}

theorem anchored_cardinal_defect_mem_unit (i : Fin n) {lam : ℝ} (hlam : 0 ≤ lam)
    (T : ℝ) (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalDefect i lam T x Y ∈ Icc (0 : ℝ) 1 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam (anchoredPatchConfiguration i x Y)
  unfold anchoredCardinalDefect
  grind

section
variable (hd : 0 < d)
include hd

section
variable (i : Fin n)

theorem anchored_patch_collision_null (x : Covariate d) :
    ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ j : SpatialScaleIndex i, Y j ≠ x := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  solve_by_elim [ae_all_iff.mpr, Measure.ae_eval_ne]

/-- The true integrated cardinal defect equals the complementary scale
integral almost everywhere under the actual Lebesgue patch design. -/
theorem anchored_cardinal_defect_ae_eq_tail
    {lam : ℝ} (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    (fun Y => anchoredCardinalDefect i lam T x Y) =ᵐ[spatialPatchDesignMeasure i d]
      (fun Y => ∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
        anchoredCardinalScaleWeight i lam x t Y) := by
  filter_upwards [anchored_patch_collision_null hd i x] with Y hY
  have hU : ∀ j, j ≠ i → anchoredPatchConfiguration i x Y i ≠ anchoredPatchConfiguration i x Y j := by
    simp [Covariate, anchoredPatchConfiguration] <;> grind
  apply integrated_cardinal_weight_defect_eq_complement <;> assumption

theorem anchored_cardinal_defect_integrable
    {lam : ℝ} (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    Integrable (anchoredCardinalDefect i lam T x) (spatialPatchDesignMeasure i d) := by
  have h := (anchored_cardinal_tail_joint_integrable i hlam.le T x).integral_prod_right
  exact h.congr (anchored_cardinal_defect_ae_eq_tail hd i hlam T x).symm

theorem anchored_cardinal_defect_square_integrable
    {lam : ℝ} (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    Integrable (fun Y => anchoredCardinalDefect i lam T x Y ^ 2) (spatialPatchDesignMeasure i d) := by
  have h := anchored_cardinal_defect_integrable hd i hlam T x
  have hmeas : AEStronglyMeasurable (fun Y => anchoredCardinalDefect i lam T x Y ^ 2)
      (spatialPatchDesignMeasure i d) := by
    fun_prop
  exact h.mono' hmeas (Filter.Eventually.of_forall fun Y => by
    have hr := anchored_cardinal_defect_mem_unit i hlam.le T x Y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hr.1, hr.2])

end

/-- The actual squared interpolation-bias bound, without a desired bias or
score premise. The only parameters are the dimension, number of points, scale
cutoff and the actual fixed spatial anchor. -/
theorem anchored_cardinal_defect_square_integral_le (hn : 2 ≤ n)
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

end

end

end NearlyMinimax
