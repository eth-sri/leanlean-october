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

def unaryScaleDensity (alpha t : ℝ) : ℝ := alpha ^ 2 * (t * Real.exp (-(alpha * t)))

private theorem unary_scale_density_integrable {alpha : ℝ} (ha : 0 ≤ alpha) :
    IntegrableOn (unaryScaleDensity alpha) (Ici 0) := by
  rcases ha.eq_or_lt with h | h
  · subst alpha
    change Integrable (fun t : ℝ => 0 ^ 2 * (t * Real.exp (-(0 * t)))) _
    simp
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    change Integrable (fun t : ℝ => alpha ^ 2 * (t * Real.exp (-(alpha * t)))) _
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := alpha)
        (by norm_num) (by norm_num) h).const_mul (alpha ^ 2)

private theorem unary_scale_density_integral {alpha : ℝ} (ha : 0 ≤ alpha) :
    (∫ t in Ici 0, unaryScaleDensity alpha t) = if alpha = 0 then 0 else 1 := by
  by_cases hzero : alpha = 0
  · simp [unaryScaleDensity, hzero]
  · have hGamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := alpha)
      (by norm_num) (lt_of_le_of_ne ha (Ne.symm hzero))
    rw [integral_Ici_eq_integral_Ioi, ite_eq_right hzero]
    simp only [unaryScaleDensity, integral_const_mul]
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hGamma
    simp_all

private theorem spatial_unary_weight_eq_density {d : ℕ} (lam : ℝ) (x y : Covariate d) :
    (fun t => spatialUnaryWeight lam t x y) = unaryScaleDensity (lam * spatialSquaredDistance x y) := by
  ext t
  unfold spatialUnaryWeight unaryScaleDensity
  ring

private theorem spatial_unary_rate_nonneg {d : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (x y : Covariate d) :
    0 ≤ lam * spatialSquaredDistance x y := by unfold spatialSquaredDistance; positivity

theorem spatial_cardinal_weight_scale_product {d n : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialCardinalWeight lam (spatialScaleExtend i t) U i =
      ∏ j : SpatialScaleIndex i, spatialUnaryWeight lam (t j) (U i) (U j.val) := by
  unfold spatialCardinalWeight
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun j => by simp) (fun j : Fin n => spatialUnaryWeight lam (spatialScaleExtend i t j) (U i) (U j))]
  apply Finset.prod_congr rfl
  intro j _
  simp only [spatialScaleExtend, dite_eq_left j.property]

theorem spatial_scale_orthant_measure {n : ℕ} (i : Fin n) :
    (volume : Measure (SpatialScaleVector i)).restrict (Ici 0) =
      Measure.pi (fun _j : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ))) := by
  have hset : Ici (0 : SpatialScaleVector i) = Set.univ.pi (fun _ => Ici (0 : ℝ)) := by
    ext t
    tauto
  rw [hset]
  apply Measure.restrict_pi_pi

section
variable {d n : ℕ} (i : Fin n)
    (lam : ℝ)

theorem spatial_cardinal_weight_orthant_integrable (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    Integrable (fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i)
      (volume.restrict (Ici (0 : SpatialScaleVector i))) := by
  simpa only [spatial_cardinal_weight_scale_product, spatial_scale_orthant_measure] using Integrable.fintype_prod (𝕜 := ℝ)
      (f := fun (j : SpatialScaleIndex i) (t : ℝ) => spatialUnaryWeight lam t (U i) (U j.val))
      (μ := fun _j : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ)))
      (fun j => by
        rw [spatial_unary_weight_eq_density]
        exact unary_scale_density_integrable (spatial_unary_rate_nonneg hlam _ _))

theorem spatial_cardinal_weight_orthant_nonnegative (U : Fin n → Covariate d) :
    0 ≤ᵐ[volume.restrict (Ici (0 : SpatialScaleVector i))]
      (fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i) := by
  have hae : ∀ᵐ t : SpatialScaleVector i ∂volume.restrict (Ici (0 : SpatialScaleVector i)),
      t ∈ Ici (0 : SpatialScaleVector i) := ae_restrict_mem measurableSet_Ici
  filter_upwards [hae] with t ht
  rw [spatial_cardinal_weight_scale_product]
  apply Finset.prod_nonneg
  intro j _
  have htj : (0 : ℝ) ≤ t j := ht j
  unfold spatialUnaryWeight
  positivity

private theorem spatial_cardinal_weight_orthant_integral (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    (∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) =
      ∏ j : SpatialScaleIndex i, if lam * spatialSquaredDistance (U i) (U j.val) = 0 then 0 else 1 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod (fun (j : SpatialScaleIndex i) t => spatialUnaryWeight lam t (U i) (U j.val))]
  apply Finset.prod_congr rfl
  intro j _
  rw [spatial_unary_weight_eq_density, unary_scale_density_integral (spatial_unary_rate_nonneg hlam _ _)]

theorem spatial_cardinal_weight_orthant_integral_le_one (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    (∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) ≤ 1 := by
  rw [spatial_cardinal_weight_orthant_integral i lam hlam U]
  apply Finset.prod_le_one₀ <;> intro j _ <;> split_ifs <;> norm_num

end

theorem spatial_scale_measure_le_orthant {n : ℕ} (i : Fin n) (T : ℝ) :
    spatialScaleMeasure i T ≤ volume.restrict (Ici (0 : SpatialScaleVector i)) :=
  Measure.restrict_mono_set _ (fun _ ht => ht.1)

/-- The genuine integrated weights belong to [0,1], by the exact
unary Gamma normalization and finite-product Fubini. -/
theorem integrated_cardinal_weight_mem_unit {d n : ℕ} (i : Fin n)
    (lam T : ℝ) (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    integratedCardinalWeight lam T U i ∈ Icc (0 : ℝ) 1 := by
  have hnn := spatial_cardinal_weight_orthant_nonnegative i lam U
  have hint := spatial_cardinal_weight_orthant_integrable i lam hlam U
  have hμ := spatial_scale_measure_le_orthant i T
  refine ⟨integral_nonneg_of_ae (hnn.filter_mono (ae_mono hμ)), ?_⟩
  exact (integral_mono_measure hμ hnn hint).trans
    (spatial_cardinal_weight_orthant_integral_le_one i lam hlam U)

theorem spatial_scale_domain_mono {n : ℕ} (i : Fin n) {L T : ℝ}
    (hL : 0 < L) (hLT : L ≤ T) : spatialScaleDomain i L ⊆ spatialScaleDomain i T := by
  intro t ht
  refine ⟨ht.1, ?_⟩
  exact (show spatialScaleLogSum i t ≤ 2 * Real.log L from ht.2).trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log hL hLT) (by norm_num))

section
variable {d : ℕ}

theorem spatial_squared_distance_pos (x y : Covariate d) (hxy : x ≠ y) :
    0 < spatialSquaredDistance x y := by
  have he : ∃ r, x r ≠ y r := by
    grind
  obtain ⟨r, hr⟩ := he
  apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
  exact ⟨r, Finset.mem_univ r, sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hr))⟩


end

/-- Away from coincident observations the full untruncated scale
measure has exact weight one. -/
theorem spatial_cardinal_weight_orthant_integral_eq_one {d n : ℕ} (i : Fin n)
    (lam : ℝ) (hlam : 0 < lam) (U : Fin n → Covariate d)
    (hU : ∀ j, j ≠ i → U i ≠ U j) :
    (∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) = 1 := by
  rw [spatial_cardinal_weight_orthant_integral i lam hlam.le U]
  exact Finset.prod_eq_one fun j _ => ite_eq_right (mul_pos hlam (spatial_squared_distance_pos _ _ (hU j j.property))).ne'

section
variable {n : ℕ}

theorem spatial_scale_domain_one (i : Fin n) : spatialScaleDomain i 1 = {0} := by
  ext t
  constructor
  · intro ht
    apply mem_singleton_iff.mpr
    funext j
    have hsub := spatial_scale_domain_subset_box i 1 (by norm_num) ht
    have hlow := hsub.1 j
    have hhigh := hsub.2 j
    norm_num at hhigh
    exact le_antisymm hhigh hlow
  · rintro rfl
    constructor
    · simp
    · simp [spatialScaleLogSum]

theorem spatial_scale_measure_one_eq_zero (hn : 2 ≤ n) (i : Fin n) :
    spatialScaleMeasure i 1 = 0 := by
  have hni := Fin.nontrivial_iff_two_le.mpr hn
  letI := hni
  obtain ⟨j, hji⟩ := exists_ne i
  letI : Nonempty (SpatialScaleIndex i) := ⟨⟨j, hji⟩⟩
  unfold spatialScaleMeasure
  simp [spatial_scale_domain_one]

end

theorem integrated_cardinal_matrix_one_eq_zero {d n D : ℕ} (hn : 2 ≤ n)
    (lam : ℝ) (U : Fin n → Covariate d) : integratedCardinalMatrix (D := D) lam 1 U = 0 := by
  funext β β'
  unfold integratedCardinalMatrix
  simp [spatial_scale_measure_one_eq_zero hn, integral_zero_measure]

/-- The true interpolation defect is exactly the complementary scale
integral off the collision set. This supplies the object to which the
Gamma-tail spatial estimates apply. -/
theorem integrated_cardinal_weight_defect_eq_complement {d n : ℕ} (i : Fin n)
    (lam T : ℝ) (hlam : 0 < lam) (U : Fin n → Covariate d)
    (hU : ∀ j, j ≠ i → U i ≠ U j) :
    1 - integratedCardinalWeight lam T U i =
      ∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
        ∂volume.restrict ((Ici (0 : SpatialScaleVector i)) \ spatialScaleDomain i T) := by
  have hdom := (spatial_scale_domain_isClosed i T).measurableSet
  have h := integral_add_compl hdom (spatial_cardinal_weight_orthant_integrable i lam hlam.le U)
  have hleft : (volume.restrict (Ici (0 : SpatialScaleVector i))).restrict (spatialScaleDomain i T) =
      spatialScaleMeasure i T :=
    Measure.restrict_restrict_of_subset (fun _ ht => ht.1)
  have hright : (volume.restrict (Ici (0 : SpatialScaleVector i))).restrict (spatialScaleDomain i T)ᶜ =
      volume.restrict ((Ici (0 : SpatialScaleVector i)) \ spatialScaleDomain i T) := by
    rw [Measure.restrict_restrict hdom.compl]
    congr 1
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  rw [hleft, hright, spatial_cardinal_weight_orthant_integral_eq_one i lam hlam U hU] at h
  change integratedCardinalWeight lam T U i + _ = 1 at h
  linarith

end NearlyMinimax
