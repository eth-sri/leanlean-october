module
public import NearlyMinimax.CardinalCoefficientBounds
public import NearlyMinimax.CardinalSeparatedBand
public import NearlyMinimax.ExponentialSpatialKernels
@[expose] public section
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
section
variable {d n D : ℕ} {lam T L : ℝ}
def anchoredPatchConfiguration  (i : Fin n) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : Fin n → Covariate d :=
  fun j => if h : j ≠ i then Y ⟨j, h⟩ else x
def spatialPatchDesignMeasure  (i : Fin n) (d : ℕ) :
    Measure (SpatialScaleIndex i → Covariate d) :=
  Measure.pi (fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d))
instance spatialPatchCube_finite (d : ℕ) :
    IsFiniteMeasure ((volume : Measure (Covariate d)).restrict (spatialPatchBox d)) := by
  apply isFiniteMeasure_restrict.mpr
  exact isCompact_Icc.measure_ne_top
instance spatialPatchDesignMeasure_finite {n : ℕ} (i : Fin n) (d : ℕ) :
    IsFiniteMeasure (spatialPatchDesignMeasure i d) := by
  unfold spatialPatchDesignMeasure
  infer_instance
def anchoredCardinalScaleWeight  (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalWeight lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i
theorem anchored_configuration_same  (i : Fin n) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : anchoredPatchConfiguration i x Y i = x := by
  simp [anchoredPatchConfiguration]
theorem anchored_configuration_other  (i : Fin n) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) (j : SpatialScaleIndex i) :
    anchoredPatchConfiguration i x Y j.val = Y j := by
  simp [anchoredPatchConfiguration, j.property]
theorem anchored_cardinal_scale_product  (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalScaleWeight i lam x t Y =
      ∏ j, spatialUnaryWeight lam (t j) x (Y j) := by
  unfold anchoredCardinalScaleWeight
  rw [spatial_cardinal_weight_scale_product]
  simp_rw [anchored_configuration_same, anchored_configuration_other]
theorem anchored_cardinal_scale_integrable  (i : Fin n)  (hlam : 0 ≤ lam)
    (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    IntegrableOn (fun t => anchoredCardinalScaleWeight i lam x t Y) (Ici 0) :=
  spatial_cardinal_weight_orthant_integrable i lam hlam (anchoredPatchConfiguration i x Y)
theorem anchored_cardinal_scale_joint_integrable  (i : Fin n) 
    (hlam : 0 ≤ lam) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0)).prod (spatialPatchDesignMeasure i d)) := by
  have h_anchored_cardinal_scale_joint_continuous : Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2) := by
    simp_rw [anchored_cardinal_scale_product]
    unfold spatialUnaryWeight spatialSquaredDistance
    fun_prop
  have hc := h_anchored_cardinal_scale_joint_continuous
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun Y => anchored_cardinal_scale_integrable i hlam x Y), ?_⟩
  exact (integrable_const ↑1).mono'
    hc.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have he : (fun t => ‖anchoredCardinalScaleWeight i lam x t Y‖) =ᵐ[volume.restrict (Ici 0)]
          (fun t => anchoredCardinalScaleWeight i lam x t Y) := by
        filter_upwards [spatial_cardinal_weight_orthant_nonnegative i lam (anchoredPatchConfiguration i x Y)] with t ht
        have hnn : 0 ≤ anchoredCardinalScaleWeight i lam x t Y := ht
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [integral_congr_ae he]
      exact spatial_cardinal_weight_orthant_integral_le_one i lam hlam (anchoredPatchConfiguration i x Y))
theorem anchored_cardinal_tail_joint_integrable  (i : Fin n) 
    (hlam : 0 ≤ lam) (T ) (x ) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0 \ spatialScaleDomain i T)).prod (spatialPatchDesignMeasure i d)) := by
  exact (anchored_cardinal_scale_joint_integrable i hlam x).mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set _ Set.diff_subset) le_rfl)
def anchoredCardinalDefect  (i : Fin n) (lam T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  1 - integratedCardinalWeight lam T (anchoredPatchConfiguration i x Y) i
theorem anchored_cardinal_defect_mem_unit  (i : Fin n)  (hlam : 0 ≤ lam)
    (T : ℝ) (x : Covariate d) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalDefect i lam T x Y ∈ Icc ↑0 1 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam (anchoredPatchConfiguration i x Y)
  unfold anchoredCardinalDefect
  constructor <;> linarith [h.1, h.2]
theorem anchored_cardinal_defect_ae_eq_tail  (hd : 0 < d) (i : Fin n)
     (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    (fun Y => anchoredCardinalDefect i lam T x Y) =ᵐ[spatialPatchDesignMeasure i d]
      (fun Y => ∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
        anchoredCardinalScaleWeight i lam x t Y) := by
  have h_anchored_patch_collision_null : ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ j : SpatialScaleIndex i, Y j ≠ x := by
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    apply ae_all_iff.mpr
    intro j
    exact Measure.ae_eval_ne (fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d)) j x
  filter_upwards [h_anchored_patch_collision_null] with Y hY
  have hU : ∀ j, j ≠ i → anchoredPatchConfiguration i x Y i ≠ anchoredPatchConfiguration i x Y j := by
    intro j hj
    rw [anchored_configuration_same]
    have he : anchoredPatchConfiguration i x Y j = Y ⟨j, hj⟩ := by
      simp [anchoredPatchConfiguration, hj]
    rw [he]
    exact (hY ⟨j, hj⟩).symm
  exact integrated_cardinal_weight_defect_eq_complement i lam T hlam (anchoredPatchConfiguration i x Y) hU
theorem anchored_cardinal_defect_integrable  (hd : 0 < d) (i : Fin n)
     (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
    Integrable (anchoredCardinalDefect i lam T x) (spatialPatchDesignMeasure i d) := ((anchored_cardinal_tail_joint_integrable i hlam.le T x).integral_prod_right).congr (anchored_cardinal_defect_ae_eq_tail hd i hlam T x).symm
theorem anchored_cardinal_defect_square_integrable  (hd : 0 < d) (i : Fin n)
     (hlam : 0 < lam) (T : ℝ) (x : Covariate d) :
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
theorem integral_square_le_weight_mass_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (h w g : α → ℝ) (hh : Integrable h μ)
    (hw : Integrable w μ) (hg : Integrable g μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hdom : ∀ᵐ x ∂μ, (h x) ^ 2 ≤ w x * g x) :
    (∫ x, h x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, g x ∂μ) := by
  have hew : (fun x => Real.sqrt (w x) ^ 2) =ᵐ[μ] w := by
    filter_upwards [hwn] with x hx
    exact Real.sq_sqrt hx
  have heg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hgn] with x hx
    exact Real.sq_sqrt hx
  have hwL  :=
    (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable)).mpr (hw.congr hew.symm)
  have hgL  :=
    (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable)).mpr (hg.congr heg.symm)
  have hcs := integral_cauchy_schwarz μ _ _ hwL hgL
  rw [integral_congr_ae hew, integral_congr_ae heg] at hcs
  have hbound : |∫ x, h x ∂μ| ≤ Real.sqrt (∫ x, w x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
    calc
      _ ≤ ∫ x, |h x| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm h
      _ ≤ ∫ x, Real.sqrt (w x) * Real.sqrt (g x) ∂μ := integral_mono_ae hh.abs (memLp_one_iff_integrable.mp (hwL.fun_mul hgL)) (by filter_upwards [hwn, hgn, hdom] with x hx hy hz; apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp; simpa only [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] using hz)
      _ ≤ |∫ x, Real.sqrt (w x) * Real.sqrt (g x) ∂μ| := le_abs_self _
      _ ≤ _ := hcs
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg_of_ae hwn), Real.sq_sqrt (integral_nonneg_of_ae hgn)] using ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hbound)
def anchoredCardinalScale  (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalScale lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i
theorem anchored_cardinal_scale_product_actual  (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) :
    anchoredCardinalScale i lam x t Y = ∏ j : SpatialScaleIndex i,
      t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x (Y j))) := by
  unfold anchoredCardinalScale
  rw [spatial_cardinal_scale_product]
  simp_rw [anchored_configuration_same, anchored_configuration_other, neg_mul]
theorem anchored_cardinal_scale_continuous_actual  (i : Fin n) (lam : ℝ) (x : Covariate d) :
    Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2) := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialSquaredDistance
  fun_prop
theorem anchored_cardinal_band_scale_joint_integrable  (i : Fin n) 
    (hlam : 0 ≤ lam) (hT : 1 ≤ T) (L : ℝ) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScale i lam x z.1 z.2)
      ((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod (spatialPatchDesignMeasure i d)) := by
  letI := spatial_scale_measure_finite i T hT
  letI : IsFiniteMeasure (volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)) :=
    isFiniteMeasure_of_le (spatialScaleMeasure i T) (Measure.restrict_mono_set volume Set.diff_subset)
  apply Integrable.of_bound (anchored_cardinal_scale_continuous_actual i lam x).aestronglyMeasurable
    ((T ^ 2 * lam ^ 2) ^ Fintype.card (SpatialScaleIndex i))
  have hae : ∀ᵐ z ∂((volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)).prod
      (spatialPatchDesignMeasure i d)), z.1 ∈ spatialScaleDomain i T := by
    apply (Measure.ae_prod_iff_ae_ae ((spatial_scale_domain_isClosed i T).measurableSet.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    exact ae_of_all _ (fun Y => ht.1)
  filter_upwards [hae] with z hz
  rw [Real.norm_eq_abs]
  have h_anchored_cardinal_scale_nonnegative_actual : 0 ≤ anchoredCardinalScale i lam x z.1 z.2 := spatial_cardinal_scale_nonnegative i lam (anchoredPatchConfiguration i x z.2) z.1 hz.1
  rw [abs_of_nonneg h_anchored_cardinal_scale_nonnegative_actual,
    anchored_cardinal_scale_product_actual]
  calc
    _ ≤ ∏ _j : SpatialScaleIndex i, T ^ 2 * lam ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact mul_nonneg (mul_nonneg (hz.1 j) (sq_nonneg _)) (Real.exp_pos _).le
      · intro j hj
        have htj  := hz.1 j
        have := (spatial_scale_domain_subset_box i T hT hz).2 j
        exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg htj hlam) (Finset.sum_nonneg (fun r _ => sq_nonneg _))))) (mul_nonneg htj (sq_nonneg _))).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_right (show z.1 j ≤ T ^ 2 by linarith) (sq_nonneg lam))
    _ = _ := by simp
def spatialScaleIntegralConstant (d : ℕ) : ℝ :=
  (spatialInterpolationLambda d) ^ 2 * Real.exp (1 / 2) *
    (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d
theorem mvpolynomial_product_coefficients_continuous {α κ σ : Type*}
    [TopologicalSpace α] [DecidableEq σ] (s )
    (P : κ → α → MvPolynomial σ ℝ)
    (hP : ∀ k ∈ s, ∀ β, Continuous (fun x => (P k x).coeff β)) :
    ∀ β, Continuous (fun x => (∏ k ∈ s, P k x).coeff β) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro β; simp only [Finset.prod_empty]; exact continuous_const
  | @insert k s hk ih =>
    intro β
    simp only [Finset.prod_insert hk, coeff_mul]
    apply continuous_finsetSum
    intro w _
    exact (hP k (Finset.mem_insert_self _ _) w.1).mul
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) w.2)
theorem spatial_cardinal_polynomial_coefficients_continuous 
    (i : Fin n) (β : Fin d →₀ ℕ) :
    Continuous (fun U : Fin n → Covariate d => (spatialCardinalPolynomial U i).coeff β) := by
  have hcoeff (j : Fin n) (δ : Fin d →₀ ℕ) :
      Continuous (fun U : Fin n → Covariate d => (spatialCardinalAffine (U i) (U j)).coeff δ) := by
    simp only [spatialCardinalAffine, coeff_sum, coeff_sub, coeff_C_mul]
    apply continuous_finsetSum
    intro r _
    apply Continuous.sub
    · by_cases hδ : (0 : Fin d →₀ ℕ) = δ
      · simp only [coeff_C, hδ, ite_true]; fun_prop
      · simp only [coeff_C, hδ, ite_false]; exact continuous_const
    · exact (by fun_prop : Continuous (fun U : Fin n → Covariate d => 8 * (U j r - U i r))).mul
        continuous_const
  exact mvpolynomial_product_coefficients_continuous
    (α := Fin n → Covariate d) (κ := Fin n) (σ := Fin d)
    ((Finset.univ : Finset (Fin n)).erase i)
    (fun j (U : Fin n → Covariate d) => spatialCardinalAffine (U i) (U j))
    (fun j _ δ => hcoeff j δ) β
def centeredCardinalBandMatrix  (i : Fin n) (lam L T : ℝ)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) : ℝ :=
  ∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
    spatialCenteredCardinalMatrix i lam U t β β'
theorem centered_cardinal_band_matrix_l1_square_le  (i ) 
    (hlam : 0 ≤ lam) (L )  (hT : 1 ≤ T)
    (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2) :
    (spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U)) ^ 2 ≤
      (100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
        ∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
          spatialCardinalScale lam (spatialScaleExtend i t) U i := by
  let s := spatialScaleDomain i T \ spatialScaleDomain i L
  let C : ℝ := (100 * d) ^ (2 * Fintype.card (SpatialScaleIndex i))
  have hs : s ⊆ Ici 0 := fun t ht => ht.1.1
  have hμ : volume.restrict s ≤ spatialScaleMeasure i T := Measure.restrict_mono_set volume Set.sdiff_subset
  have h_spatial_centered_matrix_cost_integrable : Integrable (fun t => spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t))
      (spatialScaleMeasure i T) := by
    unfold spatialMatrixL1
    exact integrable_finsetSum _ (fun β _ => integrable_finsetSum _
      (fun β' _ => (spatial_centered_cardinal_matrix_integrable i lam T hT U β β').abs))
  have hh := h_spatial_centered_matrix_cost_integrable.mono_measure hμ
  have hw : Integrable (fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i) (volume.restrict s) :=
    (spatial_cardinal_weight_orthant_integrable i lam hlam U).mono_measure
      (Measure.restrict_mono_set volume hs)
  have hscale : Integrable (fun t => spatialCardinalScale lam (spatialScaleExtend i t) U i) (volume.restrict s) := by
    have hi : IntegrableOn (fun t => spatialCardinalScale lam (spatialScaleExtend i t) U i)
        (spatialScaleDomain i T) :=
      (spatial_centered_cardinal_scale_continuous i lam U).continuousOn.integrableOn_compact
        (spatial_scale_domain_isCompact i T hT)
    exact hi.mono_set Set.sdiff_subset
  have hnn : ∀ᵐ t ∂volume.restrict s, 0 ≤ spatialCardinalScale lam (spatialScaleExtend i t) U i := by
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    exact spatial_cardinal_scale_nonnegative i lam U t ht.1.1
  have hwn : ∀ᵐ t ∂volume.restrict s, 0 ≤ spatialCardinalWeight lam (spatialScaleExtend i t) U i :=
    (spatial_cardinal_weight_orthant_nonnegative i lam U).filter_mono
      (ae_mono (Measure.restrict_mono_set volume hs))
  have hdom : ∀ᵐ t ∂volume.restrict s,
      (spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t)) ^ 2 ≤
        spatialCardinalWeight lam (spatialScaleExtend i t) U i *
          (C * spatialCardinalScale lam (spatialScaleExtend i t) U i) := by
    filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
      (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
    have h_spatial_centered_matrix_l1_square_le_weight_scale (ht : t ∈ Ici 0) : (spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t)) ^ 2 ≤
        spatialCardinalWeight lam (spatialScaleExtend i t) U i *
          ((100 * ↑d) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
            spatialCardinalScale lam (spatialScaleExtend i t) U i) := by
      have hn := spatial_cardinal_scale_nonnegative i lam U t ht
      have hc := (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        (frameCoefficientL1_nonneg _)).mpr (highFrameCoefficients_sum_abs_le (D := D) (spatialCardinalPolynomial U i))
      have h_spatial_cardinal_polynomial_coefficient_l1_square_le : (frameCoefficientL1 (spatialCardinalPolynomial U i)) ^ 2 ≤
          (100 * ↑d) ^ Fintype.card (SpatialScaleIndex i) *
            ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) := by
        rw [spatial_cardinal_polynomial_scale_product]
        have hp := frameCoefficientL1_prod Finset.univ (fun j : SpatialScaleIndex i => spatialCardinalAffine (U i) (U j.val))
        have hs := (sq_le_sq₀ (frameCoefficientL1_nonneg _) (Finset.prod_nonneg (fun _ _ => frameCoefficientL1_nonneg _))).mpr hp
        calc
          _ ≤ (∏ j : SpatialScaleIndex i, frameCoefficientL1 (spatialCardinalAffine (U i) (U j.val))) ^ 2 := hs
          _ = ∏ j : SpatialScaleIndex i, (frameCoefficientL1 (spatialCardinalAffine (U i) (U j.val))) ^ 2 := by rw [Finset.prod_pow]
          _ ≤ ∏ j : SpatialScaleIndex i, 100 * ↑d * spatialSquaredDistance (U i) (U j.val) :=
            Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
              (fun j _ => spatial_cardinal_affine_coefficient_l1_square_le _ _ (hU j.val))
          _ = _ := by rw [Finset.prod_mul_distrib]; simp
      have hb := hc.trans h_spatial_cardinal_polynomial_coefficient_l1_square_le
      have h_spatial_centered_matrix_l1_eq : spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t) =
          |spatialCardinalScale lam (spatialScaleExtend i t) U i| *
            (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) ^ 2 := by
        unfold spatialMatrixL1 spatialCenteredCardinalMatrix
        simp_rw [abs_mul]
        rw [show (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
            |spatialCardinalScale lam (spatialScaleExtend i t) U i| *
              |highFrameCoefficients (spatialCardinalPolynomial U i) β| *
              |highFrameCoefficients (spatialCardinalPolynomial U i) β'|) =
            |spatialCardinalScale lam (spatialScaleExtend i t) U i| *
              (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) *
              (∑ β : HighFrameIndex d D, |highFrameCoefficients (spatialCardinalPolynomial U i) β|) by
          simp_rw [← Finset.mul_sum]
          rw [← Finset.sum_mul, ← Finset.mul_sum]]
        ring
      rw [h_spatial_centered_matrix_l1_eq, abs_of_nonneg hn]
      have hprod : 0 ≤ ∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val) :=
        Finset.prod_nonneg (fun j _ => Finset.sum_nonneg (fun r _ => sq_nonneg _))
      have hs := (sq_le_sq₀ (mul_nonneg hn (sq_nonneg _)) (mul_nonneg hn (mul_nonneg (by positivity) hprod))).mpr
        (mul_le_mul_of_nonneg_left hb hn)
      apply hs.trans_eq
      have h_spatial_cardinal_weight_eq_scale_distance_product : spatialCardinalWeight lam (spatialScaleExtend i t) U i =
          spatialCardinalScale lam (spatialScaleExtend i t) U i *
            (∏ j : SpatialScaleIndex i, spatialSquaredDistance (U i) (U j.val)) ^ 2 := by
        rw [spatial_cardinal_weight_scale_product, spatial_cardinal_scale_product, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j hj
        unfold spatialUnaryWeight
        rw [mul_pow]
        ring
      rw [h_spatial_cardinal_weight_eq_scale_distance_product, show (100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) =
          ((100 * (d : ℝ)) ^ Fintype.card (SpatialScaleIndex i)) ^ 2 by
        rw [← pow_mul, Nat.mul_comm]]
      ring
    exact (h_spatial_centered_matrix_l1_square_le_weight_scale ht.1.1)
  have hcs := integral_square_le_weight_mass_mul (volume.restrict s) _ _ _ hh hw (hscale.const_mul C)
    hwn (hnn.mono (fun t ht => mul_nonneg (by dsimp [C]; positivity) ht)) hdom
  have hmass : (∫ t in s, spatialCardinalWeight lam (spatialScaleExtend i t) U i) ≤ 1 :=
    (integral_mono_measure (Measure.restrict_mono_set volume hs)
      (spatial_cardinal_weight_orthant_nonnegative i lam U)
      (spatial_cardinal_weight_orthant_integrable i lam hlam U)).trans
        (spatial_cardinal_weight_orthant_integral_le_one i lam hlam U)
  have hnonneg : 0 ≤ ∫ t in s, C * spatialCardinalScale lam (spatialScaleExtend i t) U i :=
    integral_nonneg_of_ae (hnn.mono (fun t ht => mul_nonneg (by dsimp [C]; positivity) ht))
  have hbound := hcs.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hnonneg)
  have hnCost : 0 ≤ ∫ t in s, spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t) :=
    integral_nonneg (fun _ => spatial_matrix_l1_nonnegative _)
  have h_spatial_centered_band_cost_le_integral_cost : spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ≤
      ∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
        spatialMatrixL1 (spatialCenteredCardinalMatrix (D := D) i lam U t) := by
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
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t => spatialCenteredCardinalMatrix i lam U t β β'))
  have htriangle := (sq_le_sq₀ (spatial_matrix_l1_nonnegative _) hnCost).mpr
    h_spatial_centered_band_cost_le_integral_cost
  exact htriangle.trans (by simpa only [integral_const_mul] using hbound)
def anchoredCenteredCardinalBandMatrix  (i : Fin n) (lam L T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  centeredCardinalBandMatrix i lam L T (anchoredPatchConfiguration i x Y)
theorem anchored_centered_band_matrix_entry_measurable  (i : Fin n) (lam L T : ℝ)
    (x : Covariate d) (β β' : HighFrameIndex d D) :
    Measurable (fun Y => anchoredCenteredCardinalBandMatrix i lam L T x Y β β') := by
  have h_anchored_patch_configuration_continuous : Continuous (anchoredPatchConfiguration i x) := by
    apply continuous_pi
    intro l
    unfold anchoredPatchConfiguration
    split_ifs <;> fun_prop
  have hc (γ : HighFrameIndex d D) :
      Continuous (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
        highFrameCoefficients (spatialCardinalPolynomial (anchoredPatchConfiguration i x z.2) i) γ) :=
    (spatial_cardinal_polynomial_coefficients_continuous i (polynomialBoxExponent γ.val)).comp
      (h_anchored_patch_configuration_continuous.comp continuous_snd)
  have h := (((anchored_cardinal_scale_continuous_actual i lam x).mul (hc β)).mul (hc β')).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L))
  exact h.measurable
theorem anchored_patch_configuration_in_box_ae  (i : Fin n) (x : Covariate d)
    (hx : x ∈ spatialPatchBox d) :
    ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ l r, |anchoredPatchConfiguration i x Y l r| ≤ 2 := by
  have hae : ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ j : SpatialScaleIndex i, Y j ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro j
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d))
      (i := j)).eventually (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hae] with Y hY
  intro l r
  by_cases hl : l ≠ i
  · have hh := hY ⟨l, hl⟩
    simp only [anchoredPatchConfiguration, dite_eq_left hl]
    apply (abs_le.mpr ⟨hh.1 r, hh.2 r⟩).trans
    norm_num
  · have  := not_ne_iff.mp hl
    subst l
    rw [anchored_configuration_same]
    exact (abs_le.mpr ⟨hx.1 r, hx.2 r⟩).trans (by norm_num)
theorem anchored_centered_band_matrix_l1_square_integrable  (i : Fin n)
     (hlam : 0 ≤ lam) (hT : 1 ≤ T) (L : ℝ) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    Integrable (fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i lam L T x Y)) ^ 2)
      (spatialPatchDesignMeasure i d) := by
  have hi := (anchored_cardinal_band_scale_joint_integrable i hlam hT L x).integral_prod_right.const_mul
    ((100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)))
  have h_anchored_centered_band_matrix_l1_square_measurable : Measurable (fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i lam L T x Y)) ^ 2) := by
    exact (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (anchored_centered_band_matrix_entry_measurable i lam L T x β β').abs))).pow_const 2
  apply hi.mono' h_anchored_centered_band_matrix_l1_square_measurable.aestronglyMeasurable
  filter_upwards [anchored_patch_configuration_in_box_ae i x hx] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact centered_cardinal_band_matrix_l1_square_le i hlam L hT (anchoredPatchConfiguration i x Y) hY
theorem anchored_centered_band_matrix_l1_square_integral_le  (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d)  (hL : 1 ≤ L) (hT : 1 ≤ T) :
    (∫ Y, (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i (spatialInterpolationLambda d) L T x Y)) ^ 2
      ∂spatialPatchDesignMeasure i d) ≤
      ((100 * d) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) *
        L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2) := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hi := (anchored_cardinal_band_scale_joint_integrable i hlam hT L x).integral_prod_right.const_mul
    ((100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)))
  have hdom : (fun Y => (spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i (spatialInterpolationLambda d) L T x Y)) ^ 2)
      ≤ᵐ[spatialPatchDesignMeasure i d]
      (fun Y => (100 * (d : ℝ)) ^ (2 * Fintype.card (SpatialScaleIndex i)) *
        ∫ t in spatialScaleDomain i T \ spatialScaleDomain i L,
          anchoredCardinalScale i (spatialInterpolationLambda d) x t Y) := by
    filter_upwards [anchored_patch_configuration_in_box_ae i x hx] with Y hY
    exact centered_cardinal_band_matrix_l1_square_le i hlam L hT (anchoredPatchConfiguration i x Y) hY
  have hfirst := integral_mono_ae (anchored_centered_band_matrix_l1_square_integrable i hlam hT L x hx) hi hdom
  rw [integral_const_mul, spatial_scale_index_card] at hfirst
  have h_anchored_cardinal_band_scale_spatial_integral_bound : (∫ Y, (∫ t : SpatialScaleVector i in spatialScaleDomain i T \ spatialScaleDomain i L,
      anchoredCardinalScale i (spatialInterpolationLambda d) x t Y) ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialScaleIntegralConstant d) ^ (n - 1) *
        L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2) := by
    have hd0 : 0 < d := by omega
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    let b : ℝ := ((d : ℝ) - 4) / 2
    have hb : (1 / 2 : ℝ) ≤ b := by dsimp [b]; linarith
    have hpos : 0 < b := by linarith
    have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
    have hjoint := anchored_cardinal_band_scale_joint_integrable i hlam hT L x
    have hfub  :=
      (integral_prod_symm _ hjoint).symm.trans (integral_prod _ hjoint)
    rw [hfub]
    have hsub : spatialScaleDomain i T \ spatialScaleDomain i L ⊆ Ici 0 \ spatialScaleDomain i L :=
      fun t ht => ⟨ht.1.1, ht.2⟩
    have hμ := Measure.restrict_mono_set (volume : Measure (SpatialScaleVector i)) hsub
    have hpowint := spatial_scale_complement_power_integrable hn i hpos L
    have hpowint' : Integrable (fun t : SpatialScaleVector i => ∏ j, (1 + t j) ^ (-b - 1 : ℝ))
        (volume.restrict (Ici 0 \ spatialScaleDomain i L)) := hpowint
    have hpowband := hpowint'.mono_measure hμ
    have hdom : (fun t : SpatialScaleVector i =>
        ∫ Y, anchoredCardinalScale i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤ᵐ[
          volume.restrict (spatialScaleDomain i T \ spatialScaleDomain i L)]
        (fun t => (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
          ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) := by
      filter_upwards [ae_restrict_mem ((spatial_scale_domain_isClosed i T).measurableSet.diff
        (spatial_scale_domain_isClosed i L).measurableSet)] with t ht
      have h_anchored_cardinal_scale_spatial_integral_decay : (∫ Y, anchoredCardinalScale i (spatialInterpolationLambda d) x t Y ∂spatialPatchDesignMeasure i d) ≤
        (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
          ∏ j, (1 + t j) ^ (1 - (d : ℝ) / 2) := by
        have h_anchored_cardinal_scale_spatial_integral_product (lam : ℝ) (x : Covariate d) (t : SpatialScaleVector i) : (∫ Y, anchoredCardinalScale i lam x t Y ∂spatialPatchDesignMeasure i d) =
            ∏ j : SpatialScaleIndex i, lam ^ 2 * ∫ y in spatialPatchBox d,
              t j * Real.exp (-t j * lam * spatialSquaredDistance x y) := by
          simp_rw [anchored_cardinal_scale_product_actual]
          unfold spatialPatchDesignMeasure
          rw [integral_fintype_prod_eq_prod
            (fun (j : SpatialScaleIndex i) (y : Covariate d) =>
              t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance x y)))]
          apply Finset.prod_congr rfl
          intro j hj
          rw [← integral_const_mul]
          congr 1
          funext y
          ring
        rw [h_anchored_cardinal_scale_spatial_integral_product]
        have h : (∏ j : SpatialScaleIndex i, (spatialInterpolationLambda d) ^ 2 *
            ∫ y in spatialPatchBox d, t j * Real.exp (-t j * spatialInterpolationLambda d * spatialSquaredDistance x y)) ≤
            ∏ j : SpatialScaleIndex i, spatialScaleIntegralConstant d * (1 + t j) ^ (1 - (d : ℝ) / 2) := by
          apply Finset.prod_le_prod₀
          · intro j hj
            apply mul_nonneg (sq_nonneg _)
            apply integral_nonneg
            intro y
            exact mul_nonneg (ht.1.1 j) (Real.exp_pos _).le
          · intro j hj
            have h_spatial_scale_exponential_patch_integral_decay (t : ℝ) (ht : 0 ≤ t) : (∫ y in spatialPatchBox d,
                t * Real.exp (-t * spatialInterpolationLambda d * spatialSquaredDistance x y)) ≤
                Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d *
                  (1 + t) ^ (1 - (d : ℝ) / 2) := by
              let lam := spatialInterpolationLambda d
              let b := lam * (1 + t) / 2
              let A := t * Real.exp (1 / 2)
              have : 0 < (d : ℝ) := by exact_mod_cast hd0
              have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
              have hs : 0 < 1 + t := by linarith
              have hb : 0 < b := by dsimp [b]; positivity
              have hInt := (radial_gaussian_integrable b hb x).const_mul A
              have hBound (y : Covariate d) (hy : y ∈ spatialPatchBox d) :
                  t * Real.exp (-t * lam * spatialSquaredDistance x y) ≤
                  A * Real.exp (-b * spatialSquaredDistance x y) := by
                obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd0 x y hx hy
                have he : -t * lam * spatialSquaredDistance x y ≤
                    1 / 2 + -b * spatialSquaredDistance x y := by
                  dsimp [b]
                  nlinarith
                have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) ht
                rw [Real.exp_add] at h
                exact h.trans_eq (by dsimp [A]; ring)
              calc
                _ ≤ ∫ y in spatialPatchBox d, A * Real.exp (-b * spatialSquaredDistance x y) :=
                  setIntegral_mono_on (by apply ContinuousOn.integrableOn_compact isCompact_Icc; unfold spatialSquaredDistance; fun_prop) hInt.integrableOn measurableSet_Icc hBound
                _ ≤ ∫ y, A * Real.exp (-b * spatialSquaredDistance x y) :=
                  integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun y => by dsimp [A]; positivity)) hInt
                _ = A * (Real.sqrt (Real.pi / b)) ^ d := by rw [integral_const_mul, radial_gaussian_integral]
                _ = A * ((Real.sqrt (2 * Real.pi / lam)) ^ d * (1 + t) ^ (-(d : ℝ) / 2)) := by
                  rw [radial_gaussian_scale_normalization d lam t hlam ht]
                _ ≤ Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / lam)) ^ d *
                    (1 + t) ^ (1 - (d : ℝ) / 2) := by
                  rw [Real.rpow_sub hs, Real.rpow_one]
                  have h := mul_le_mul_of_nonneg_right (show t ≤ 1 + t by linarith)
                    (by positivity : 0 ≤ Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / lam)) ^ d /
                      (1 + t) ^ ((d : ℝ) / 2))
                  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le]
                  convert h using 1 <;> ring
            have hdec := mul_le_mul_of_nonneg_left
              (h_spatial_scale_exponential_patch_integral_decay (t j) (ht.1.1 j))
              (sq_nonneg (spatialInterpolationLambda d))
            simpa only [spatialScaleIntegralConstant, mul_assoc] using hdec
        simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h
      have h := h_anchored_cardinal_scale_spatial_integral_decay
      simpa only [show 1 - (d : ℝ) / 2 = -b - 1 by dsimp [b]; ring] using h
    have hC : 0 ≤ (spatialScaleIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) := by
      unfold spatialScaleIntegralConstant
      positivity
    have hfirst := integral_mono_ae hjoint.integral_prod_left (hpowband.const_mul _) hdom
    rw [integral_const_mul] at hfirst
    have hmiddle := integral_mono_measure hμ (by filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i L).measurableSet)] with t ht; apply Finset.prod_nonneg; intro j hj; exact Real.rpow_nonneg (by have htj : (0 : ℝ) ≤ t j := ht.1 j; linarith) _) hpowint
    have htail := spatial_scale_complement_power_integral_le hn i hb hL
    have hfull := hfirst.trans ((mul_le_mul_of_nonneg_left hmiddle hC).trans (mul_le_mul_of_nonneg_left htail hC))
    rw [spatial_scale_index_card, show -2 * b = 4 - (d : ℝ) by dsimp [b]; ring] at hfull
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hfull
  have htail := mul_le_mul_of_nonneg_left h_anchored_cardinal_band_scale_spatial_integral_bound
    (by positivity : 0 ≤ (100 * (d : ℝ)) ^ (2 * (n - 1)))
  have hfull := hfirst.trans htail
  rw [show 2 * (n - 1) = (n - 1) * 2 by omega, pow_mul] at hfull
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm, mul_assoc, mul_comm, mul_left_comm] using hfull
theorem spatial_centered_cardinal_matrix_joint_continuous  (i : Fin n) (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Continuous (fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      spatialCenteredCardinalMatrix i lam z.1 z.2 β β') := by
  have hc (γ : HighFrameIndex d D) : Continuous (fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      highFrameCoefficients (spatialCardinalPolynomial z.1 i) γ) :=
    (spatial_cardinal_polynomial_coefficients_continuous i (polynomialBoxExponent γ.val)).comp continuous_fst
  have h_spatial_centered_cardinal_scale_joint_continuous : Continuous (fun z : (Fin n → Covariate d) × SpatialScaleVector i =>
      spatialCardinalScale lam (spatialScaleExtend i z.2) z.1 i) := by
    simp_rw [spatial_cardinal_scale_product]
    unfold spatialSquaredDistance
    fun_prop
  exact (h_spatial_centered_cardinal_scale_joint_continuous.mul (hc β)).mul (hc β')
theorem integrated_cardinal_matrix_continuous  (lam )  (hT : 1 ≤ T)
    (β β' : HighFrameIndex d D) :
    Continuous (fun U : Fin n → Covariate d => integratedCardinalMatrix lam T U β β') := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_parametric_integral_of_continuous
    (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
    (spatial_scale_domain_isCompact i T hT)
theorem integrated_cardinal_band_continuous  (lam : ℝ)  (hL : 1 ≤ L) (hT : 1 ≤ T)
    (β β' : HighFrameIndex d D) :
    Continuous (fun U : Fin n → Covariate d =>
      integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β') :=
  (integrated_cardinal_matrix_continuous lam hT β β').sub
    (integrated_cardinal_matrix_continuous lam hL β β')
def cardinalHeadSplit  (i : Fin n) :
    (Fin n → Covariate d) ≃ᵐ Covariate d × (SpatialScaleIndex i → Covariate d) where
  toFun U := (U i, fun j => U j.val)
  invFun z := anchoredPatchConfiguration i z.1 z.2
  left_inv U := by
    funext j
    change (if h : j ≠ i then U j else U i) = U j
    split_ifs with h
    · rfl
    · exact congrArg U (not_ne_iff.mp h).symm
  right_inv z := by
    apply Prod.ext
    · exact anchored_configuration_same i z.1 z.2
    · funext j
      exact anchored_configuration_other i z.1 z.2 j
  measurable_toFun := (measurable_pi_apply i).prodMk
    (Measurable.of_eval (fun j => measurable_pi_apply j.val))
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    change Measurable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      if h : j ≠ i then z.2 ⟨j, h⟩ else z.1)
    split_ifs <;> fun_prop
theorem cardinalHeadSplit_measurePreserving  (i : Fin n)
    (μ : Measure (Covariate d)) [SigmaFinite μ] :
    MeasurePreserving (cardinalHeadSplit i) (Measure.pi (fun _ : Fin n => μ))
      (μ.prod (Measure.pi (fun _ : SpatialScaleIndex i => μ))) := by
  letI : Unique {j : Fin n // j = i} :=
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  have hs := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ) (fun j => j = i)
  have heq : (@Measure.pi {j : Fin n // j = i} (fun _ => Covariate d)
      (Subtype.fintype (fun j => j = i)) (fun _ => inferInstance) (fun _ => μ)) =
      Measure.pi (fun _ : {j : Fin n // j = i} => μ) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [heq] at hs
  have hh := (measurePreserving_funUnique μ {j : Fin n // j = i}).prod
    (MeasurePreserving.id (Measure.pi (fun _ : SpatialScaleIndex i => μ)))
  exact hh.comp hs
def fullSpatialPatchDesign (d n ) : Measure (Fin n → Covariate d) :=
  Measure.pi (fun _ => volume.restrict (spatialPatchBox d))
instance fullSpatialPatchDesign_finite (d n : ℕ) : IsFiniteMeasure (fullSpatialPatchDesign d n) := by
  unfold fullSpatialPatchDesign
  infer_instance
theorem fullSpatialPatchDesign_split  (i )
    (f : (Fin n → Covariate d) → ℝ) :
    (∫ U, f U ∂fullSpatialPatchDesign d n) =
      ∫ z : Covariate d × (SpatialScaleIndex i → Covariate d),
        f (anchoredPatchConfiguration i z.1 z.2)
        ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d) := (((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm).integral_comp' f).symm
end
variable {d k : ℕ}
theorem pi_finset_subtype_instance_eq  [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E) (s : Finset I) :
    (@Measure.pi s (fun _ => E) (Subtype.fintype (fun i => i ∈ s))
      (fun _ => inferInstance) (fun _ => μ)) = Measure.pi (fun _ : s => μ) := by
  congr 1
  exact Subsingleton.elim _ _
theorem finite_pi_subset_integral  [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (s : Finset I) (f : (s → E) → ℝ) :
    (∫ U : I → E, f (fun j : s => U j.val) ∂Measure.pi (fun _ : I => μ)) =
      μ.real univ ^ (Fintype.card I - s.card) * ∫ V, f V ∂Measure.pi (fun _ : s => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => E) (fun i => i ∈ s)
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ => μ) (fun i => i ∈ s)
  rw [pi_finset_subtype_instance_eq μ s] at hp
  have he : (∫ U : I → E, f (fun j => U j.val) ∂Measure.pi (fun _ => μ)) =
      ∫ z : (s → E) × ({i : I // i ∉ s} → E), f z.1
        ∂(Measure.pi (fun _ => μ)).prod (Measure.pi (fun _ : {i : I // i ∉ s} => μ)) := by
    have h := hp.symm.integral_comp' (fun U => f (fun j => U j.val))
    have hf (z : (s → E) × ({i : I // i ∉ s} → E)) :
        (fun j => e.symm z j.val) = z.1 := by
      funext j
      change (if h : j.val ∈ s then z.1 ⟨j.val, h⟩ else z.2 ⟨j.val, h⟩) = z.1 j
      simp [j.property]
    change (∫ z : (s → E) × ({i : I // i ∉ s} → E), f (fun j => e.symm z j.val)
      ∂(Measure.pi (fun _ => μ)).prod (Measure.pi (fun _ : {i : I // i ∉ s} => μ))) = _ at h
    simp_rw [hf] at h
    exact h.symm
  rw [he, integral_fun_fst]
  have hc : (Measure.pi (fun _ : {i : I // i ∉ s} => μ)).real univ =
      μ.real univ ^ (Fintype.card I - s.card) := by
    simp only [measureReal_def, Measure.pi_univ, Finset.prod_const, Finset.card_univ,
      ENNReal.toReal_pow]
    rw [Fintype.card_subtype_compl]
    simp
  rw [hc]
  rfl
theorem finite_pi_subset_integrable  [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ ) [IsFiniteMeasure μ]
    (s : Finset I) (f : (s → E) → ℝ) (hf : Integrable f (Measure.pi (fun _ : s => μ))) :
    Integrable (fun U : I → E => f (fun j : s => U j.val)) (Measure.pi (fun _ : I => μ)) := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => μ) (fun i => i ∈ s)
  rw [pi_finset_subtype_instance_eq μ s] at hp
  exact hp.integrable_comp_of_integrable (hf.comp_fst _)
def spatialSubsetConfiguration  (s : Finset (Fin k))
    (U : Fin k → Covariate d) : Fin s.card → Covariate d :=
  fun j => U ((Fintype.equivFin s).symm (Fin.cast (Fintype.card_coe s).symm j)).val
theorem spatialSubsetConfiguration_measurable  (s : Finset (Fin k)) :
    Measurable (spatialSubsetConfiguration (d := d) s) := by
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply _
theorem finite_pi_reindex_integral  [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (e : I ≃ J) (f : (J → E) → ℝ) :
    (∫ U : I → E, f (fun j => U (e.symm j)) ∂Measure.pi (fun _ : I => μ)) =
      ∫ V, f V ∂Measure.pi (fun _ : J => μ) := by
  have h := (measurePreserving_piCongrLeft (fun _ : J => μ) e).integral_comp' f
  have he (U : I → E) : (Equiv.piCongrLeft (fun _ : J => E) e) U =
      fun j => U (e.symm j) := by
    funext j
    simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  simp only [MeasurableEquiv.coe_piCongrLeft] at h
  simp_rw [he] at h
  exact h
theorem spatial_subset_square_integral_enumerated  (s : Finset (Fin k))
    (f : (Fin s.card → Covariate d) → ℝ) :
    (∫ U : Fin k → Covariate d, f (spatialSubsetConfiguration s U) ^ 2
      ∂fullSpatialPatchDesign d k) = ↑2 ^ (d * (k - s.card)) *
        ∫ V, f V ^ 2 ∂fullSpatialPatchDesign d s.card := by
  let e : s ≃ Fin s.card := (Fintype.equivFin s).trans (finCongr (Fintype.card_coe s))
  have he (U : Fin k → Covariate d) : spatialSubsetConfiguration s U =
      fun j => (fun l => U l.val) (e.symm j) := by
    funext j
    rfl
  simp_rw [he]
  have h_spatial_subset_square_integral {d} (f : (s → Covariate d) → ℝ) : (∫ U : Fin k → Covariate d, f (fun j : s => U j.val) ^ 2 ∂fullSpatialPatchDesign d k) =
      ↑2 ^ (d * (k - s.card)) *
        ∫ V, f V ^ 2 ∂Measure.pi (fun _ : s => volume.restrict (spatialPatchBox d)) := by
    rw [fullSpatialPatchDesign, finite_pi_subset_integral
      (volume.restrict (spatialPatchBox d)) s (fun V => f V ^ 2)]
    simp only [measureReal_def, Measure.restrict_apply_univ, Fintype.card_fin]
    change (volume.real (spatialPatchBox d)) ^ (k - s.card) * _ = _
    rw [spatialPatchBox_real_volume, ← pow_mul]
  rw [h_spatial_subset_square_integral (fun V => f (fun j => V (e.symm j))), finite_pi_reindex_integral (volume.restrict (spatialPatchBox d)) e (fun V => f V ^ 2)]
  rfl
end NearlyMinimax
