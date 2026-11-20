module

public import NearlyMinimax.IntegratedCardinalCovariance

@[expose] public section

/-! Actual normalization of the unary scale law and probabilistic
range/monotonicity of the integrated cardinal weights. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

def unaryScaleDensity (alpha t : ℝ) : ℝ := t * alpha ^ 2 * Real.exp (-(alpha * t))

section
variable {d n : ℕ} (i : Fin n) {lam : ℝ} (hlam : 0 ≤ lam) (U : DesignSample d n) {alpha : ℝ}
    (x y : Covariate d)

theorem unary_scale_density_integrable (ha : 0 ≤ alpha) :
    IntegrableOn (unaryScaleDensity alpha) (Ici 0) := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst alpha
    change Integrable (fun t => t * 0 ^ 2 * Real.exp (-(0 * t))) _
    simp
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
      (by norm_num) (by norm_num) hpos).const_mul (alpha ^ 2)
    change Integrable (fun t => t * alpha ^ 2 * Real.exp (-(alpha * t))) _
    convert h using 1
    funext t
    simp
    ring

theorem unary_scale_density_integral (ha : 0 ≤ alpha) :
    (∫ t in Ici 0, unaryScaleDensity alpha t) = if alpha = 0 then 0 else 1 := by
  by_cases hzero : alpha = 0
  · simp [unaryScaleDensity, hzero]
  · have hGamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2)
      (by norm_num) (lt_of_le_of_ne ha (Ne.symm hzero))
    have he : (unaryScaleDensity alpha) = fun t => alpha ^ 2 * (t * Real.exp (-(alpha * t))) := by
      funext t
      unfold unaryScaleDensity
      ring
    rw [he, integral_Ici_eq_integral_Ioi, integral_const_mul]
    norm_num only [ Real.rpow_one] at hGamma
    simp_all

include hlam in
theorem spatial_unary_scale_integrable :
    IntegrableOn (fun t => spatialUnaryWeight lam t x y) (Ici 0) := by
  have he : (fun t => spatialUnaryWeight lam t x y) = unaryScaleDensity (lam * spatialSquaredDistance x y) := by
    funext t
    unfold spatialUnaryWeight unaryScaleDensity
    ring
  rw [he]
  exact unary_scale_density_integrable (mul_nonneg hlam (Finset.sum_nonneg (fun r _ => sq_nonneg _)))

include hlam in
theorem spatial_unary_scale_integral_le_one :
    (∫ t in Ici 0, spatialUnaryWeight lam t x y) ≤ 1 := by
  have hdist : 0 ≤ spatialSquaredDistance x y := Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have he : (fun t => spatialUnaryWeight lam t x y) = unaryScaleDensity (lam * spatialSquaredDistance x y) := by
    funext t
    unfold spatialUnaryWeight unaryScaleDensity
    ring
  rw [he, unary_scale_density_integral (mul_nonneg hlam hdist)]
  split_ifs <;> norm_num

theorem spatial_cardinal_weight_scale_product (lam : ℝ)
    (U : DesignSample d n) (t : SpatialScaleVector i) :
    spatialCardinalWeight lam (spatialScaleExtend t) U i =
      ∏ j, spatialUnaryWeight lam (t j) (U i) (U j.val) := by
  unfold spatialCardinalWeight
  rw [Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i)
    (fun j => by simp) (fun j => spatialUnaryWeight lam (spatialScaleExtend t j) (U i) (U j))]
  apply Finset.prod_congr rfl
  simp_all [spatialScaleExtend]

theorem spatial_scale_orthant_measure :
    volume.restrict (Ici 0) =
      Measure.pi (fun _j : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ))) := by
  have hset : Ici (0 : SpatialScaleVector i) = Set.univ.pi (fun _ => Ici 0) := by
    ext t
    aesop
  rw [hset]
  apply Measure.restrict_pi_pi

include hlam in
theorem spatial_cardinal_weight_orthant_integrable :
    Integrable (fun t => spatialCardinalWeight lam (spatialScaleExtend t) U i)
      (volume.restrict (Ici (0 : SpatialScaleVector i))) := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure]
  exact Integrable.fintype_prod
    (μ := fun _j  => volume.restrict (Ici 0))
    (fun j => spatial_unary_scale_integrable hlam ..)

theorem spatial_cardinal_weight_orthant_nonnegative
    (lam : ℝ) (U : DesignSample d n) :
    0 ≤ᵐ[volume.restrict (Ici (0 : SpatialScaleVector i))]
      (fun t => spatialCardinalWeight lam (spatialScaleExtend t) U i) := by
  filter_upwards [(ae_restrict_mem measurableSet_Ici)] with t ht
  rw [spatial_cardinal_weight_scale_product]
  apply Finset.prod_nonneg
  intro j _
  unfold spatialUnaryWeight <;> bound

include hlam in
theorem spatial_cardinal_weight_orthant_integral_le_one :
    (∫ t, spatialCardinalWeight lam (spatialScaleExtend t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) ≤ 1 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod
    (μ := fun _j : SpatialScaleIndex i => volume.restrict (Ici 0))
    (fun j t => spatialUnaryWeight lam t (U i) (U j.val))]
  apply (Finset.prod_le_prod₀ _ (fun j _ => spatial_unary_scale_integral_le_one hlam ..)).trans_eq
  · exact Finset.prod_const_one
  · intro j _
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := ht
    unfold spatialUnaryWeight
    positivity

/-- The genuine integrated weights belong to [0,1], by the exact
unary Gamma normalization and finite-product Fubini. -/
theorem integrated_cardinal_weight_mem_unit
    (lam T : ℝ) (hlam : 0 ≤ lam) (U : DesignSample d n) :
    integratedCardinalWeight lam T U i ∈ Icc 0 1 := by
  have hnn := spatial_cardinal_weight_orthant_nonnegative i lam U
  have hμ := (Measure.restrict_mono_set _ (fun _ ht => ht.1) : spatialScaleMeasure i T ≤ volume.restrict (Ici 0))
  refine ⟨integral_nonneg_of_ae (hnn.filter_mono (ae_mono hμ)), ?_⟩
  exact (integral_mono_measure hμ hnn (spatial_cardinal_weight_orthant_integrable i hlam U)).trans
    (spatial_cardinal_weight_orthant_integral_le_one i hlam U)

theorem spatial_squared_distance_pos {x y : Covariate d} (hxy : x ≠ y) :
    0 < spatialSquaredDistance x y := by
  have he : ∃ r, x r ≠ y r := by
    grind
  obtain ⟨r, hr⟩ := he
  apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
  exact ⟨r, Finset.mem_univ r, sq_pos_of_ne_zero (by positivity)⟩

theorem spatial_unary_scale_integral_eq_one (hlam : 0 < lam)
    {x y : Covariate d} (hxy : x ≠ y) :
    (∫ t in Ici 0, spatialUnaryWeight lam t x y) = 1 := by
  have ha  := mul_pos hlam (spatial_squared_distance_pos hxy)
  have he : (fun t => spatialUnaryWeight lam t x y) = unaryScaleDensity (lam * spatialSquaredDistance x y) := by
    funext t
    unfold spatialUnaryWeight unaryScaleDensity
    ring
  rw [he, unary_scale_density_integral ha.le, ite_eq_right ha.ne']

end

variable {d n D : ℕ} (hn : 2 ≤ n) (i : Fin n) (lam T : ℝ) (hlam : 0 < lam) (U : DesignSample d n)

/-- Away from coincident observations the full untruncated scale
measure has exact weight one. -/
theorem spatial_cardinal_weight_orthant_integral_eq_one {i : Fin n}
    {lam : ℝ} (hlam : 0 < lam) {U : DesignSample d n}
    (hU : ∀ j, j ≠ i → U i ≠ U j) :
    (∫ t, spatialCardinalWeight lam (spatialScaleExtend t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) = 1 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod
    (μ := fun _j : SpatialScaleIndex i => volume.restrict (Ici 0))
    (fun j t => spatialUnaryWeight lam t (U i) (U j.val))]
  apply Finset.prod_eq_one
  intro j _
  exact spatial_unary_scale_integral_eq_one hlam (hU j.val j.property)

theorem spatial_scale_domain_one : spatialScaleDomain i 1 = {0} := by
  ext t
  constructor
  · intro ht
    apply mem_singleton_iff.mpr
    funext j
    have hsub := spatial_scale_domain_subset_box i 1 (by norm_num) ht
    have hhigh  := hsub.2 j
    norm_num at hhigh
    exact le_antisymm hhigh (hsub.1 j)
  · rintro rfl
    constructor
    · simp
    · simp [spatialScaleLogSum]

include hn in
theorem spatial_scale_measure_one_eq_zero :
    spatialScaleMeasure i 1 = 0 := by
  letI := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  letI : Nonempty (SpatialScaleIndex i) := ⟨⟨j, hji⟩⟩
  unfold spatialScaleMeasure
  rw [spatial_scale_domain_one]
  simp

include hn in
theorem integrated_cardinal_matrix_one_eq_zero : integratedCardinalMatrix (D := D) lam 1 U = 0 := by
  funext β β'
  unfold integratedCardinalMatrix
  simp_rw [spatial_scale_measure_one_eq_zero hn, integral_zero_measure]
  exact Finset.sum_const_zero

include hlam in
/-- The true interpolation defect is exactly the complementary scale
integral off the collision set. This supplies the object to which the
Gamma-tail spatial estimates apply. -/
theorem integrated_cardinal_weight_defect_eq_complement
    (hU : ∀ j, j ≠ i → U i ≠ U j) :
    1 - integratedCardinalWeight lam T U i =
      ∫ t, spatialCardinalWeight lam (spatialScaleExtend t) U i
        ∂volume.restrict ((Ici 0) \ spatialScaleDomain i T) := by
  have hdom := (spatial_scale_domain_isClosed i T).measurableSet
  have h := integral_add_compl hdom (spatial_cardinal_weight_orthant_integrable i hlam.le U)
  have hright : (volume.restrict (Ici 0)).restrict (spatialScaleDomain i T)ᶜ =
      volume.restrict ((Ici 0) \ spatialScaleDomain i T) := by
    rw [Measure.restrict_restrict hdom.compl]
    congr 1
    ext t
    simp
    tauto
  rw [(Measure.restrict_restrict_of_subset (fun _ ht => ht.1)), hright, spatial_cardinal_weight_orthant_integral_eq_one hlam hU] at h
  change integratedCardinalWeight lam T U i + _ = 1 at h
  linarith

end NearlyMinimax
