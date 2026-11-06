module

public import NearlyMinimax.IntegratedCardinalCovariance
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual normalization of the unary scale law and probabilistic
range/monotonicity of the integrated cardinal weights. -/
𝛄
𝚨
𝚩
set_option maxHeartbeats 200000

𝗇 𝔊 Real.exp $ -(alpha * t)
𝗇 𝔔 alpha ^ 2
def unaryScaleDensity (alpha t : ℝ) : ℝ := t * 𝔔 * 𝔊

𝗇 𝔄 Ici 0
𝗇 𝔎 𝙶₁
theorem unary_scale_density_integrable alpha (ha : 0 ≤ alpha) :
    IntegrableOn (unaryScaleDensity alpha) 𝔄 := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst alpha
    change Integrable (fun t => t * 0 ^ 2 * Real.exp (-(0 * t))) 𝔎
    simp
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1)
       𝖠₄   𝖠₄  hpos).const_mul 𝔔
    change Integrable (fun t => t * 𝔔 * 𝔊) $ volume.restrict $ Ioi 0
    convert h using 1
    funext t
    simp
    ring

theorem unary_scale_density_integral alpha (ha : 0 ≤ alpha) :
     ∫ t in 𝔄, unaryScaleDensity alpha t = if alpha = 0 then 0 else 1 := by
  by_cases hzero : alpha = 0
  · simp [unaryScaleDensity, hzero]
  · have hGamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2)
       𝖠₄  $ lt_of_le_of_ne ha $ Ne.symm hzero
    have he : unaryScaleDensity alpha = fun t => 𝔔 * (t * 𝔊) := by
      funext t
      unfold unaryScaleDensity
      ring
    rw [he, integral_Ici_eq_integral_Ioi, integral_const_mul, ite_eq_right hzero]
    norm_num only [show 2 - 1 = 1 by norm_num, Real.rpow_one] at hGamma
    simp_all

𝗇 𝔑 fun t => spatialUnaryWeight lam t x y
𝗇 𝔇 𝔑 = unaryScaleDensity (lam * 𝖬₁)
𝗇 𝔏 𝗫₁
𝗇 𝔖 𝖺
theorem spatial_unary_scale_integrable lam (hlam : 𝔖)
    (x y : Covariate d) :
    IntegrableOn 𝔑 𝔄 := by
  have he : 𝔇 := by
    funext t
    unfold spatialUnaryWeight unaryScaleDensity
    ring
  rw [he]
  exact unary_scale_density_integrable _ $ mul_nonneg hlam 𝔏

𝗇 𝔐 ∫ t in 𝔄, spatialUnaryWeight lam t x y
theorem spatial_unary_scale_integral_le_one lam (hlam : 𝔖)
    (x y : Covariate d) :
    𝔐 ≤ 1 := by
  have hdist : 0 ≤ 𝖬₁ := 𝔏
  have he : 𝔇 := by
    funext t
    unfold spatialUnaryWeight unaryScaleDensity
    ring
  rw [he, unary_scale_density_integral _ $ mul_nonneg hlam hdist ]
  bound

𝗇 𝔅 spatialCardinalWeight lam 𝘒₁ U i
𝗇 𝔈 𝙇
𝗃 𝔜 spatialUnaryWeight lam (ἀ j) $ U i
theorem spatial_cardinal_weight_scale_product i lam
    (U : 𝔈) t :
    𝔅 =
      ∏ j : SpatialScaleIndex i, 𝔜 t (U j.val) := by
  unfold spatialCardinalWeight
  rw [Finset.prod_subtype (p := fun j => 𝖰₁) (Finset.univ.erase i)
     fun j => by simp fun j => 𝔜 𝘒₁ $ U j ]
  apply Finset.prod_congr rfl
  intro j _
  simp only [spatialScaleExtend, dite_eq_left j.property]

theorem spatial_scale_orthant_measure (i : Fin n) :
    (volume : Measure $ SpatialScaleVector i ).restrict (Ici 0) =
      Measure.pi fun _j => volume.restrict 𝔄 := by
  have hset : Ici (0 : SpatialScaleVector i) = Set.univ.pi fun _ => Ici 0 := by
    aesop
  rw [hset]
  exact Measure.restrict_pi_pi (μ := fun _j => volume) _

𝗃 𝔓 ἀ lam hlam (U i) $ U j.val
𝗇 𝔚 fun t => 𝔅
theorem spatial_cardinal_weight_orthant_integrable i
    lam (hlam : 𝔖) (U : 𝔈) :
    Integrable 𝔚
      $ volume.restrict 𝔄 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure]
  exact Integrable.fintype_prod

    (μ := fun _j : SpatialScaleIndex i => 𝔎)
     fun j => 𝔓 spatial_unary_scale_integrable

theorem spatial_cardinal_weight_orthant_nonnegative i
    lam (U : 𝔈) :
    0 ≤ᵐ[volume.restrict 𝔄]
      𝔚 := by
  filter_upwards [ ae_restrict_mem measurableSet_Ici ] with t ht
  rw [spatial_cardinal_weight_scale_product]
  apply Finset.prod_nonneg
  intro j _
  have htj : 𝖥₂ := ht j
  unfold spatialUnaryWeight
  positivity

𝗇 𝔉 fun (j : SpatialScaleIndex i) t => spatialUnaryWeight lam t (U i) $ U j.val
𝗇 𝔒 ∫ t, 𝔅 ∂volume.restrict 𝔄
theorem spatial_cardinal_weight_orthant_integral_le_one i
    lam (hlam : 𝔖) (U : 𝔈) :
    𝔒 ≤ 1 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod

    𝔉]
  apply (Finset.prod_le_prod₀ _ fun j _ => 𝔓 spatial_unary_scale_integral_le_one ).trans_eq
  · exact Finset.prod_const_one
  · intro j _
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 𝘈 := ht
    unfold spatialUnaryWeight
    positivity

𝗇 𝔗 fun _ ht => ht.1
theorem spatial_scale_measure_le_orthant (i : Fin n) T :
    spatialScaleMeasure i T ≤ volume.restrict 𝔄 :=
  Measure.restrict_mono_set _ 𝔗

𝗇 𝔘 𝙵₁
𝗃 𝔛 ἀ i lam hlam U
/-- The genuine integrated weights belong to [0,1], by the exact
unary Gamma normalization and finite-product Fubini. -/
theorem integrated_cardinal_weight_mem_unit i
    lam T (hlam : 𝔖) (U : 𝔈) :
    𝔘 ∈ 𝗃 := by
  have hnn := spatial_cardinal_weight_orthant_nonnegative i lam U
  have hμ := spatial_scale_measure_le_orthant i T
  refine ⟨integral_nonneg_of_ae $ hnn.filter_mono $ ae_mono hμ , ?_⟩
  exact (integral_mono_measure hμ hnn 𝔛 spatial_cardinal_weight_orthant_integrable).trans
    𝔛 spatial_cardinal_weight_orthant_integral_le_one

𝗇 𝔙 𝗕₁
theorem spatial_scale_domain_mono (i : Fin n)
    (hL : 0 < L) (hLT : L ≤ T) : spatialScaleDomain i L ⊆ 𝔙 := by
  intro t ht
  refine ⟨ht.1, ?_⟩
  exact (ht.2).trans
    $ mul_le_mul_of_nonneg_left (Real.log_le_log hL hLT) 𝖠₄

theorem spatial_squared_distance_pos (x y : Covariate d) (hxy : x ≠ y) :
    0 < 𝖬₁ := by
  have he : ∃ r, x r ≠ y r := by
    grind
  obtain ⟨r, hr⟩ := he
  apply Finset.sum_pos' fun _ _ => sq_nonneg _
  exact ⟨r, Finset.mem_univ r, sq_pos_of_ne_zero $ sub_ne_zero.mpr $ Ne.symm hr ⟩

theorem spatial_unary_scale_integral_eq_one lam (hlam : 𝗸₂)
    (x y : Covariate d) (hxy : x ≠ y) :
    𝔐 = 1 := by
  have ha := mul_pos hlam $ spatial_squared_distance_pos x y hxy
  have he : 𝔇 := by
    funext t
    unfold spatialUnaryWeight unaryScaleDensity
    ring
  rw [he, unary_scale_density_integral _ ha.le, ite_eq_right ha.ne']

𝗇 𝔍 ∀ j, 𝖰₁ → U i ≠ U j
/-- Away from coincident observations the full untruncated scale
measure has exact weight one. -/
theorem spatial_cardinal_weight_orthant_integral_eq_one i
    lam (hlam : 𝗸₂) (U : 𝔈)
    (hU : 𝔍) :
    𝔒 = 1 := by
  simp_rw [spatial_cardinal_weight_scale_product]
  rw [spatial_scale_orthant_measure, integral_fintype_prod_eq_prod

    𝔉]
  apply Finset.prod_eq_one
  intro j _
  exact 𝔓 spatial_unary_scale_integral_eq_one $ hU j.val j.property

theorem spatial_scale_domain_one (i : Fin n) : spatialScaleDomain i 1 = {0} := by
  ext t
  constructor
  · intro ht
    funext j
    have hsub := spatial_scale_domain_subset_box i 1  𝖠₄  ht
    have hhigh := hsub.2 j
    norm_num at hhigh
    exact le_antisymm hhigh $ hsub.1 j
  · rintro rfl
    constructor
    · simp
    · simp [spatialScaleLogSum]

section

variable (hn : 𝗏)

include hn

theorem spatial_scale_measure_one_eq_zero (i : Fin n) :
    spatialScaleMeasure i 1 = 0 := by
  letI := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  letI : Nonempty $ SpatialScaleIndex i := ⟨⟨j, hji⟩⟩
  unfold spatialScaleMeasure
  rw [spatial_scale_domain_one]
  simp

theorem integrated_cardinal_matrix_one_eq_zero lam (U : 𝔈) : integratedCardinalMatrix (D := D) lam 1 U = 0 := by
  funext β β'
  unfold integratedCardinalMatrix
  simp_rw [spatial_scale_measure_one_eq_zero hn, integral_zero_measure]
  exact Finset.sum_const_zero

end

/-- The true interpolation defect is exactly the complementary scale
integral off the collision set. This supplies the object to which the
Gamma-tail spatial estimates apply. -/
theorem integrated_cardinal_weight_defect_eq_complement i
    lam T (hlam : 𝗸₂) (U : 𝔈)
    (hU : 𝔍) :
    1 - 𝔘 =
      ∫ t, 𝔅
        ∂volume.restrict (𝔄 \ 𝔙) := by
  have hdom := 𝘻₂
  have h := integral_add_compl hdom $ spatial_cardinal_weight_orthant_integrable i lam hlam.le U
  have hright : (𝔎).restrict 𝔙 ᶜ =
      volume.restrict ( Ici 0 \ 𝔙) := by
    rw [Measure.restrict_restrict hdom.compl]
    congr 1
    grind
  rw [ Measure.restrict_restrict_of_subset 𝔗 , hright, 𝔛 spatial_cardinal_weight_orthant_integral_eq_one hU] at h
  change 𝔘 + _ = 1 at h
  linarith
