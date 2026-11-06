module
public import NearlyMinimax.SpatialCardinalCovariance
@[expose] public section
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable {n d D : ℕ}
abbrev SpatialScaleIndex {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i}
abbrev SpatialScaleVector {n : ℕ} (i : Fin n) := SpatialScaleIndex i → ℝ
def spatialScaleExtend  (i : Fin n) (t : SpatialScaleVector i) (j : Fin n) : ℝ :=
  if h : j ≠ i then t ⟨j, h⟩ else 0
def spatialScaleLogSum  (i : Fin n) (t : SpatialScaleVector i) : ℝ :=
  ∑ j, Real.log (1 + max 0 (t j))
def spatialScaleDomain  (i : Fin n) (T : ℝ) : Set (SpatialScaleVector i) :=
  Ici 0 ∩ {t | spatialScaleLogSum i t ≤ 2 * Real.log T}
theorem spatial_scale_domain_isClosed  (i : Fin n) (T : ℝ) :
    IsClosed (spatialScaleDomain i T) :=
  isClosed_Ici.inter (isClosed_le (by apply continuous_finsetSum; intro j _; exact (continuous_const.add (continuous_const.max (continuous_apply j))).log (by intro t; positivity)) continuous_const)
theorem spatial_scale_domain_subset_box  (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    spatialScaleDomain i T ⊆ Icc 0 (fun _ => T ^ 2 - 1) := by
  intro t ht
  refine ⟨ht.1, fun j => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog0 (j : SpatialScaleIndex i) : 0 ≤ Real.log (1 + max 0 (t j)) :=
    Real.log_nonneg (by linarith [le_max_left ↑0 (t j)])
  have hlogj := (Finset.single_le_sum (fun j _ => hlog0 j) (Finset.mem_univ j)).trans ht.2
  have htj : 0 ≤ t j := ht.1 j
  rw [max_eq_right htj] at hlogj
  have he := Real.exp_le_exp.mpr hlogj
  rw [Real.exp_log (by linarith)] at he
  have hpow : Real.exp (2 * Real.log T) = T ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hT0] using Real.exp_nat_mul (Real.log T) 2
  rw [hpow] at he
  linarith
theorem spatial_scale_domain_isCompact  (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    IsCompact (spatialScaleDomain i T) :=
  isCompact_Icc.of_isClosed_subset (spatial_scale_domain_isClosed i T)
    (spatial_scale_domain_subset_box i T hT)
def spatialScaleMeasure  (i : Fin n) (T : ℝ) : Measure (SpatialScaleVector i) :=
  volume.restrict (spatialScaleDomain i T)
theorem spatial_scale_measure_finite  (i : Fin n) (T : ℝ) (hT : 1 ≤ T) :
    IsFiniteMeasure (spatialScaleMeasure i T) := by
  apply isFiniteMeasure_restrict.mpr
  exact (spatial_scale_domain_isCompact i T hT).measure_ne_top
def spatialCenteredCardinalMatrix  (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) (β β' : HighFrameIndex d D) : ℝ :=
  spatialCardinalScale lam (spatialScaleExtend i t) U i *
    highFrameCoefficients (spatialCardinalPolynomial U i) β *
    highFrameCoefficients (spatialCardinalPolynomial U i) β'
theorem spatial_centered_cardinal_scale_continuous 
    (i : Fin n) (lam : ℝ) (U : Fin n → Covariate d) :
    Continuous (fun t : SpatialScaleVector i => spatialCardinalScale lam (spatialScaleExtend i t) U i) := by
  apply continuous_finsetProd
  intro j _
  have h_spatial_scale_extend_continuous : Continuous (spatialScaleExtend i) := by
    apply continuous_pi
    intro j
    by_cases hji : j ≠ i
    · simpa only [spatialScaleExtend, dite_eq_left hji] using continuous_apply (⟨j, hji⟩ : SpatialScaleIndex i)
    · simp only [spatialScaleExtend, dite_eq_right hji]; exact continuous_const
  have hj := (continuous_apply j).comp h_spatial_scale_extend_continuous
  exact (hj.mul continuous_const).mul
    (Real.continuous_exp.comp ((hj.neg.mul continuous_const).mul continuous_const))
theorem spatial_centered_cardinal_matrix_integrable 
    (i : Fin n) (lam T : ℝ) (hT : 1 ≤ T) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) :
    Integrable (fun t => spatialCenteredCardinalMatrix i lam U t β β') (spatialScaleMeasure i T) := by
  apply ContinuousOn.integrableOn_compact (spatial_scale_domain_isCompact i T hT)
  exact (((spatial_centered_cardinal_scale_continuous i lam U).mul continuous_const).mul
    continuous_const).continuousOn
def integratedCardinalMatrix  (lam T : ℝ) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) : ℝ :=
  ∑ i, ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T
def integratedCardinalWeight  (lam T : ℝ) (U : Fin n → Covariate d) (i : Fin n) : ℝ :=
  ∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i ∂spatialScaleMeasure i T
theorem spatial_frame_covariance_integral  [Fintype κ] [DecidableEq κ]
    [MeasurableSpace α]  (μ : Measure α) (A : α → κ → κ → ℝ)
    (hA : ∀ β β', Integrable (fun t => A t β β') μ)
    (φ : Fin n → κ → ℝ) (i l : Fin n) :
    spatialFrameCovariance (fun β β' => ∫ t, A t β β' ∂μ) φ i l =
      ∫ t, spatialFrameCovariance (A t) φ i l ∂μ := by
  unfold spatialFrameCovariance
  rw [integral_finsetSum _ (fun β _ => integrable_finsetSum _
    (fun β' _ => (hA β β').const_mul (φ i β * φ l β')))]
  apply Finset.sum_congr rfl
  intro β _
  rw [integral_finsetSum _ (fun β' _ => (hA β β').const_mul (φ i β * φ l β'))]
  apply Finset.sum_congr rfl
  intro β' _
  rw [integral_const_mul]
theorem integrated_cardinal_response_heat  (hn : n ≤ D) (q C a V η lam T) (hC : C ≠ 0) (hT : 1 ≤ T) (U g w) (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    responseMatrixAction q C (integratedCardinalMatrix lam T U) c
      (fun c => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * integratedCardinalWeight lam T U i *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i +
      highResponseDefect q C a V η (integratedCardinalMatrix lam T U) g w
        (fun i => highFrameFeature (U i)) c y := by
  apply high_response_matrix_heat_with_defect q C a V η _ hC
  have h_integrated_cardinal_matrix_symmetric (β : HighFrameIndex d D) (β' : HighFrameIndex d D) : integratedCardinalMatrix lam T U β β' = integratedCardinalMatrix lam T U β' β := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with t
    unfold spatialCenteredCardinalMatrix
    ring
  · exact h_integrated_cardinal_matrix_symmetric
  have h_integrated_cardinal_matrix_diagonal (i : Fin n) (l : Fin n) : spatialFrameCovariance (integratedCardinalMatrix (D := D) lam T U)
      (fun j => highFrameFeature (U j)) i l =
      if i = l then integratedCardinalWeight lam T U i else 0 := by
    unfold integratedCardinalMatrix
    have h_spatial_centered_cardinal_matrix_diagonal (j : Fin n) lam (U : Fin n → Covariate d) (t : SpatialScaleVector j) (i : Fin n) (l : Fin n) : spatialFrameCovariance (spatialCenteredCardinalMatrix (D := D) j lam U t)
        (fun r => highFrameFeature (U r)) i l =
        if j = i ∧ i = l then spatialCardinalWeight lam (spatialScaleExtend j t) U j else 0 := by
      unfold spatialCenteredCardinalMatrix
      rw [spatial_frame_covariance_rank_one]
      have hdegree := (spatial_cardinal_polynomial_degree U j).trans (Nat.sub_le_sub_right hn 1)
      rw [← high_frame_polynomial_evaluation _ hdegree, ← high_frame_polynomial_evaluation _ hdegree]
      by_cases hji : j = i
      · subst j
        by_cases hil : i = l
        · subst l
          have h_spatial_cardinal_weight_product (t : Fin n → ℝ) (U : Fin n → Covariate d) (i : Fin n) : spatialCardinalScale lam t U i *
      (eval (fun r => U i r / 8) (spatialCardinalPolynomial U i)) ^ 2 =
      spatialCardinalWeight lam t U i := by
            have h_spatial_cardinal_polynomial_eval_center : eval (fun r => U i r / 8) (spatialCardinalPolynomial U i) =
                ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, spatialSquaredDistance (U i) (U j) := by
              simp only [spatialCardinalPolynomial, map_prod, spatial_cardinal_affine_eval_center]
            rw [h_spatial_cardinal_polynomial_eval_center, ← Finset.prod_pow]
            unfold spatialCardinalScale spatialCardinalWeight
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro j _
            unfold spatialUnaryWeight
            ring
          rw [ite_eq_left ⟨rfl, rfl⟩, ← h_spatial_cardinal_weight_product]
          ring
        · rw [ite_eq_right (by tauto), spatial_cardinal_polynomial_eval_neighbor U i l (Ne.symm hil), mul_zero]
      · rw [ite_eq_right (by tauto), spatial_cardinal_polynomial_eval_neighbor U j i (Ne.symm hji),
          mul_zero, zero_mul]
    rw [spatial_frame_covariance_sum]
    simp_rw [spatial_frame_covariance_integral _ _
      (fun β β' => spatial_centered_cardinal_matrix_integrable _ lam T hT U β β')]
    simp_rw [h_spatial_centered_cardinal_matrix_diagonal]
    rw [Finset.sum_eq_single i]
    · by_cases hil : i = l
      · subst l
        simp only [and_self, ite_true, integratedCardinalWeight]
      · simp only [hil, and_false, ite_false, integral_zero]
    · intro j _ hji
      simp only [hji, false_and, ite_false, integral_zero]
    · simp
  · exact h_integrated_cardinal_matrix_diagonal
def unaryScaleDensity (alpha t : ℝ) : ℝ := t * alpha ^ 2 * Real.exp (-(alpha * t))
theorem unary_scale_density_integrable (alpha ) (ha : 0 ≤ alpha) :
    IntegrableOn (unaryScaleDensity alpha) (Ici 0) := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst alpha
    change Integrable (fun t => t * 0 ^ 2 * Real.exp (-(0 * t))) (volume.restrict (Ici 0))
    simp
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := alpha)
      (by norm_num) (by norm_num) hpos).const_mul (alpha ^ 2)
    change Integrable (fun t => t * alpha ^ 2 * Real.exp (-(alpha * t))) (volume.restrict (Ioi 0))
    convert h using 1
    funext t
    simp only [Real.rpow_one]
    ring
theorem unary_scale_density_integral (alpha ) (ha : 0 ≤ alpha) :
    (∫ t in Ici 0, unaryScaleDensity alpha t) = if alpha = 0 then 0 else 1 := by
  by_cases hzero : alpha = 0
  · simp [unaryScaleDensity, hzero]
  · have hpos  := lt_of_le_of_ne ha (Ne.symm hzero)
    have hGamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := alpha)
      (by norm_num) hpos
    have he : (unaryScaleDensity alpha) = fun t => alpha ^ 2 * (t * Real.exp (-(alpha * t))) := by
      funext t
      unfold unaryScaleDensity
      ring
    rw [he, integral_Ici_eq_integral_Ioi, integral_const_mul, ite_eq_right hzero]
    norm_num only [show 2 - 1 = 1 by norm_num, Real.rpow_one] at hGamma
    have hG2 : Real.Gamma 2 = 1 := by
      simp
    rw [hGamma, hG2, mul_one, Real.rpow_two]
    field_simp
theorem spatial_cardinal_weight_scale_product  (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialCardinalWeight lam (spatialScaleExtend i t) U i =
      ∏ j : SpatialScaleIndex i, spatialUnaryWeight lam (t j) (U i) (U j.val) := by
  unfold spatialCardinalWeight
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun j => by simp) (fun j : Fin n => spatialUnaryWeight lam (spatialScaleExtend i t j) (U i) (U j))]
  apply Finset.prod_congr rfl
  intro j _
  simp only [spatialScaleExtend, dite_eq_left j.property]
theorem spatial_scale_orthant_measure  (i : Fin n) :
    (volume : Measure (SpatialScaleVector i)).restrict (Ici 0) =
      Measure.pi (fun _j : SpatialScaleIndex i => volume.restrict (Ici ↑0)) := by
  have hset : Ici (0 : SpatialScaleVector i) = Set.univ.pi (fun _ => Ici ↑0) := by
    ext t
    simp only [mem_Ici, mem_pi, mem_univ, forall_true_left]
    rfl
  rw [hset]
  exact Measure.restrict_pi_pi (μ := fun _j => (volume : Measure ℝ)) _
theorem spatial_cardinal_weight_orthant_integrable  (i : Fin n)
    (lam : ℝ) (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    Integrable (fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i)
      (volume.restrict (Ici (0 : SpatialScaleVector i))) := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure]
  have h_spatial_unary_scale_integrable {d : ℕ} (x : Covariate d) (y : Covariate d) : IntegrableOn (fun t => spatialUnaryWeight lam t x y) (Ici ↑0) := by
    have hdist : 0 ≤ spatialSquaredDistance x y := Finset.sum_nonneg (fun r _ => sq_nonneg _)
    have he : (fun t => spatialUnaryWeight lam t x y) = unaryScaleDensity (lam * spatialSquaredDistance x y) := by
      funext t
      unfold spatialUnaryWeight unaryScaleDensity
      congr 1
      ring
    rw [he]
    exact unary_scale_density_integrable _ (mul_nonneg hlam hdist)
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (j : SpatialScaleIndex i) t => spatialUnaryWeight lam t (U i) (U j.val))
    (μ := fun _j => volume.restrict (Ici 0))
    (fun j => (h_spatial_unary_scale_integrable (U i) (U j.val)))
theorem spatial_cardinal_weight_orthant_nonnegative  (i : Fin n)
    (lam : ℝ) (U : Fin n → Covariate d) :
    0 ≤ᵐ[volume.restrict (Ici (0 : SpatialScaleVector i))]
      (fun t => spatialCardinalWeight lam (spatialScaleExtend i t) U i) := by
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [spatial_cardinal_weight_scale_product]
  apply Finset.prod_nonneg
  intro j _
  have : ↑0 ≤ t j := ht j
  unfold spatialUnaryWeight
  positivity
theorem spatial_cardinal_weight_orthant_integral_le_one  (i : Fin n)
    (lam : ℝ) (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    (∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) ≤ 1 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod
    (μ := fun _j => volume.restrict (Ici 0))
    (fun (j : SpatialScaleIndex i) t => spatialUnaryWeight lam t (U i) (U j.val))]
  have h_spatial_unary_scale_integral_le_one {d : ℕ} (x : Covariate d) (y : Covariate d) : (∫ t in Ici ↑0, spatialUnaryWeight lam t x y) ≤ 1 := by
    have hdist : 0 ≤ spatialSquaredDistance x y := Finset.sum_nonneg (fun r _ => sq_nonneg _)
    have he : (fun t => spatialUnaryWeight lam t x y) = unaryScaleDensity (lam * spatialSquaredDistance x y) := by
      funext t
      unfold spatialUnaryWeight unaryScaleDensity
      congr 1
      ring
    rw [he, unary_scale_density_integral _ (mul_nonneg hlam hdist)]
    split_ifs <;> norm_num
  apply (Finset.prod_le_prod₀ _ (fun j _ => (h_spatial_unary_scale_integral_le_one (U i) (U j.val)))).trans_eq
  · exact Finset.prod_const_one
  · intro j _
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have : 0 ≤ t := ht
    unfold spatialUnaryWeight
    positivity
theorem integrated_cardinal_weight_mem_unit  (i : Fin n)
    (lam T : ℝ) (hlam : 0 ≤ lam) (U : Fin n → Covariate d) :
    integratedCardinalWeight lam T U i ∈ Icc ↑0 1 := by
  have hnn := spatial_cardinal_weight_orthant_nonnegative i lam U
  have hint := spatial_cardinal_weight_orthant_integrable i lam hlam U
  have h_spatial_scale_measure_le_orthant : spatialScaleMeasure i T ≤ volume.restrict (Ici (0 : SpatialScaleVector i)) := Measure.restrict_mono_set _ (fun _ ht => ht.1)
  have hμ := h_spatial_scale_measure_le_orthant
  refine ⟨integral_nonneg_of_ae (hnn.filter_mono (ae_mono hμ)), ?_⟩
  exact (integral_mono_measure hμ hnn hint).trans
    (spatial_cardinal_weight_orthant_integral_le_one i lam hlam U)
theorem integrated_cardinal_matrix_one_eq_zero  (hn : 2 ≤ n)
    (lam : ℝ) (U : Fin n → Covariate d) : integratedCardinalMatrix (D := D) lam 1 U = 0 := by
  funext β β'
  have h_spatial_scale_measure_one_eq_zero (i : Fin n) : spatialScaleMeasure i 1 = 0 := by
    have hni  := Fin.nontrivial_iff_two_le.mpr hn
    letI := hni
    obtain ⟨j, hji⟩ := exists_ne i
    letI : Nonempty (SpatialScaleIndex i) := ⟨⟨j, hji⟩⟩
    unfold spatialScaleMeasure
    have h_spatial_scale_domain_one : spatialScaleDomain i 1 = {0} := by
      ext t
      constructor
      · intro ht
        apply mem_singleton_iff.mpr
        funext j
        have hsub := spatial_scale_domain_subset_box i 1 (by norm_num) ht
        have hlow : 0 ≤ t j := hsub.1 j
        have hhigh : t j ≤ ↑1 ^ 2 - 1 := hsub.2 j
        norm_num at hhigh
        exact le_antisymm hhigh hlow
      · rintro rfl
        constructor
        · change (0 : SpatialScaleVector i) ≤ 0; exact le_rfl
        · simp [spatialScaleLogSum]
    rw [h_spatial_scale_domain_one]
    exact Measure.restrict_eq_zero.mpr (measure_singleton (0 : SpatialScaleVector i))
  unfold integratedCardinalMatrix
  simp_rw [h_spatial_scale_measure_one_eq_zero, integral_zero_measure]
  exact Finset.sum_const_zero
theorem integrated_cardinal_weight_defect_eq_complement  (i lam T) (hlam : 0 < lam) (U : Fin n → Covariate d)
    (hU : ∀ j, j ≠ i → U i ≠ U j) :
    1 - integratedCardinalWeight lam T U i =
      ∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
        ∂volume.restrict ((Ici (0 : SpatialScaleVector i)) \ spatialScaleDomain i T) := by
  have hdom := (spatial_scale_domain_isClosed i T).measurableSet
  have h := integral_add_compl hdom (spatial_cardinal_weight_orthant_integrable i lam hlam.le U)
  have hright : (volume.restrict (Ici (0 : SpatialScaleVector i))).restrict (spatialScaleDomain i T)ᶜ =
      volume.restrict ((Ici (0 : SpatialScaleVector i)) \ spatialScaleDomain i T) := by
    rw [Measure.restrict_restrict hdom.compl]
    congr 1
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]
    tauto
  have h_spatial_cardinal_weight_orthant_integral_eq_one : (∫ t, spatialCardinalWeight lam (spatialScaleExtend i t) U i
      ∂volume.restrict (Ici (0 : SpatialScaleVector i))) = 1 := by
    simp_rw [spatial_cardinal_weight_scale_product]
    rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod
      (μ := fun _j => volume.restrict (Ici 0))
      (fun (j : SpatialScaleIndex i) t => spatialUnaryWeight lam t (U i) (U j.val))]
    apply Finset.prod_eq_one
    intro j _
    have hxy  := hU j.val j.property
    have he : ∃ r, (U i) r ≠ (U j.val) r := by
      by_contra hn
      push Not at hn
      exact hxy (funext hn)
    obtain ⟨r, hr⟩ := he
    have ha : 0 < lam * spatialSquaredDistance (U i) (U j.val) := mul_pos hlam (by apply Finset.sum_pos' (fun _ _ => sq_nonneg _); exact ⟨r, Finset.mem_univ r, sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hr))⟩)
    have he : (fun t => spatialUnaryWeight lam t (U i) (U j.val)) = unaryScaleDensity (lam * spatialSquaredDistance (U i) (U j.val)) := by
      funext t
      unfold spatialUnaryWeight unaryScaleDensity
      congr 1
      ring
    rw [he, unary_scale_density_integral _ ha.le, ite_eq_right ha.ne']
  rw [(Measure.restrict_restrict_of_subset (fun _ ht => ht.1)), hright, h_spatial_cardinal_weight_orthant_integral_eq_one] at h
  change integratedCardinalWeight lam T U i + _ = 1 at h
  linarith
theorem radial_gaussian_factorization  (b : ℝ) (x y : Covariate d) :
    Real.exp (-b * spatialSquaredDistance x y) =
      ∏ r, Real.exp (-b * (y r - x r) ^ 2) := by
  unfold spatialSquaredDistance
  rw [Finset.mul_sum, Real.exp_sum]
theorem radial_gaussian_integrable  (b : ℝ) (hb : 0 < b) (x : Covariate d) :
    Integrable (fun y => Real.exp (-b * spatialSquaredDistance x y)) volume := by
  simp_rw [radial_gaussian_factorization]
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (r : Fin d) y => Real.exp (-b * (y - x r) ^ 2))
    (μ := fun _ => (volume : Measure ℝ))
    (fun r => (integrable_exp_neg_mul_sq hb).comp_sub_right (x r))
theorem radial_gaussian_integral  (b : ℝ) (x : Covariate d) :
    (∫ y, Real.exp (-b * spatialSquaredDistance x y)) = (Real.sqrt (Real.pi / b)) ^ d := by
  simp_rw [radial_gaussian_factorization]
  rw [integral_fintype_prod_volume_eq_prod
    (fun (r : Fin d) y => Real.exp (-b * (y - x r) ^ 2))]
  simp_rw [integral_sub_right_eq_self (μ := volume) (fun y => Real.exp (-b * y ^ 2)), integral_gaussian]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
theorem unary_scale_density_gaussian_domination (alpha t )
    (ha : 0 ≤ alpha) (haHalf : alpha ≤ 1 / 2) (ht : 0 ≤ t) :
    unaryScaleDensity alpha t ≤
      (8 * Real.exp (1 / 2) / (1 + t)) * Real.exp (-((1 + t) * alpha / 2)) := by
  have hs : 0 < 1 + t := by linarith
  let z := (1 + t) * alpha / 2
  have h_quadratic_exp_absorption : z ^ 2 * Real.exp (-2 * z) ≤ 2 * Real.exp (-z) := by
    have h := Real.pow_div_factorial_le_exp z (by dsimp [z]; positivity) 2
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at h
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-2 * z))
    rw [← Real.exp_add, show z + -2 * z = -z by ring] at hmul
    linarith
  have hAbs := h_quadratic_exp_absorption
  have he : Real.exp (-(alpha * t)) = Real.exp alpha * Real.exp (-((1 + t) * alpha)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hez : -2 * z = -((1 + t) * alpha) := by dsimp [z]; ring
  rw [hez] at hAbs
  have hαexp  := Real.exp_le_exp.mpr haHalf
  have hscaled := mul_le_mul_of_nonneg_left hAbs (by positivity : 0 ≤ 4 / (1 + t) ^ 2)
  have hmain : alpha ^ 2 * Real.exp (-((1 + t) * alpha)) ≤
      8 / (1 + t) ^ 2 * Real.exp (-z) := by
    have hleft : 4 / (1 + t) ^ 2 * (z ^ 2 * Real.exp (-((1 + t) * alpha))) =
        alpha ^ 2 * Real.exp (-((1 + t) * alpha)) := by
      field_simp
      ring
    rw [hleft] at hscaled
    apply hscaled.trans_eq
    ring
  unfold unaryScaleDensity
  rw [he]
  have : 0 ≤ t * alpha ^ 2 := by positivity
  calc
    _ = t * Real.exp alpha * (alpha ^ 2 * Real.exp (-((1 + t) * alpha))) := by ring
    _ ≤ t * Real.exp (1 / 2) * (8 / (1 + t) ^ 2 * Real.exp (-z)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hαexp ht) hmain (by positivity) (by positivity)
    _ ≤ (8 * Real.exp (1 / 2) / (1 + t)) * Real.exp (-z) := by
      have hratio : t / (1 + t) ^ 2 ≤ 1 / (1 + t) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hs) hs).mpr
        nlinarith
      have h := mul_le_mul_of_nonneg_right hratio
        (by positivity : 0 ≤ 8 * Real.exp (1 / 2) * Real.exp (-z))
      convert h using 1 <;> ring
    _ = _ := rfl
def spatialPatchBox (d ) : Set (Covariate d) := Icc (fun _ => -1) (fun _ => 1)
def spatialInterpolationLambda (d : ℕ) : ℝ := 1 / (8 * d)
theorem spatial_patch_alpha_bounds  (hd : 0 < d) (x y )
    (hx : x ∈ spatialPatchBox d) (hy : y ∈ spatialPatchBox d) :
    0 ≤ spatialInterpolationLambda d * spatialSquaredDistance x y ∧
      spatialInterpolationLambda d * spatialSquaredDistance x y ≤ 1 / 2 := by
  have : 0 ≤ spatialSquaredDistance x y := Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have : spatialSquaredDistance x y ≤ 4 * d := by
    unfold spatialSquaredDistance
    calc
      _ ≤ ∑ _r : Fin d, ↑4 := by
        apply Finset.sum_le_sum
        intro r _
        have : |x r| ≤ 1 := abs_le.mpr ⟨hx.1 r, hx.2 r⟩
        have : |y r| ≤ 1 := abs_le.mpr ⟨hy.1 r, hy.2 r⟩
        have hsub : |y r - x r| ≤ 2 := (abs_sub _ _).trans (by linarith)
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hsub 2
        simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq
      _ = _ := by simp [mul_comm]
  constructor
  · unfold spatialInterpolationLambda
    positivity
  · unfold spatialInterpolationLambda
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 8 * (d : ℝ))]
    linarith
theorem radial_gaussian_scale_normalization (d : ℕ) (lam t : ℝ)
    (hlam : 0 < lam) (ht : 0 ≤ t) :
    (Real.sqrt (Real.pi / (lam * (1 + t) / 2))) ^ d =
      (Real.sqrt (2 * Real.pi / lam)) ^ d * (1 + t) ^ (-(d : ℝ) / 2) := by
  have hs : 0 < 1 + t := by linarith
  have harg : Real.pi / (lam * (1 + t) / 2) = (2 * Real.pi / lam) / (1 + t) := by
    field_simp
  rw [harg, Real.sqrt_div (by positivity), div_pow]
  have hden : (Real.sqrt (1 + t)) ^ d = (1 + t) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + t) ^ (1 / 2 : ℝ)) d,
      ← Real.rpow_mul hs.le]
    congr 1
    ring
  rw [hden, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le, div_eq_mul_inv]
def spatialUnaryIntegralConstant (d : ℕ) : ℝ :=
  8 * Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d
end NearlyMinimax
