module

public import NearlyMinimax.CardinalCoefficientBounds
public import NearlyMinimax.CardinalWeightedBounds
public import NearlyMinimax.CardinalSeparatedBand
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual scale-band spatial integrals used in the interpolation matrix
squared-norm bound. -/
𝚫
𝚨
𝚩
set_option maxHeartbeats 900000

𝗇 𝔓 anchoredPatchConfiguration i x Y
𝗇 𝔔 𝗖₁
def anchoredCardinalScale (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : 𝔔) : ℝ :=
  spatialCardinalScale lam 𝘒₁ 𝔓 i

𝗇 𝔚 anchoredCardinalScale i lam x
𝗇 𝔍 𝔚 t Y
𝗇 𝔖 lam ^ 2
theorem anchored_cardinal_scale_product_actual (i : Fin n) lam (x : Covariate d)
    t Y :
    𝔍 = ∏ j : SpatialScaleIndex i,
      t j * 𝔖 * Real.exp (-(𝘺₂ * spatialSquaredDistance x (Y j))) := by
  unfold anchoredCardinalScale
  rw [spatial_cardinal_scale_product]
  simp_rw [anchored_configuration_same, anchored_configuration_other]

theorem anchored_cardinal_scale_continuous_actual (i : Fin n) lam x :
    Continuous fun z : SpatialScaleVector i × 𝔔 =>
      𝔚 z.1 z.2 := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialSquaredDistance
  fun_prop

theorem anchored_cardinal_scale_nonnegative_actual (i : Fin n) lam (x : Covariate d)
    t (ht : 𝘩₁) Y :
    0 ≤ 𝔍 :=
  spatial_cardinal_scale_nonnegative i lam 𝔓 t ht

𝗇 𝔊 (𝖫₁ * lam ^ 2) ^ 𝖪₁
𝗃 𝔛 ἀ i T
theorem anchored_cardinal_scale_upper_bound (i : Fin n)
    (hlam : 𝖺) (hT : 𝖹) (x : Covariate d) t
    (ht : t ∈ 𝔛 spatialScaleDomain) Y :
    |𝔍| ≤ 𝔊 := by
  rw [abs_of_nonneg $ anchored_cardinal_scale_nonnegative_actual i lam x t ht.1 Y ,
    anchored_cardinal_scale_product_actual]
  calc
    _ ≤ ∏ _j : SpatialScaleIndex i, 𝖫₁ * 𝔖 := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact mul_nonneg (mul_nonneg (ht.1 j) $ sq_nonneg _ ) 𝙫
      · intro j hj
        have htj := ht.1 j
        have hdist : 0 ≤ spatialSquaredDistance x (Y j) := 𝗫₁
        have hsmall := (𝔛 spatial_scale_domain_subset_box hT ht).2 j
        exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr $ neg_nonpos.mpr $ mul_nonneg (mul_nonneg htj hlam) hdist ) $ mul_nonneg htj $ sq_nonneg _ ).trans
          𝖥₃
    𝘿 := 𝖢₄

𝗇 𝔄 𝔛 spatialScaleDomain \ spatialScaleDomain i L
𝗇 𝔎 (𝔛 spatial_scale_domain_isClosed).measurableSet.diff 𝘷₂
𝗇 𝔑 𝘓₁
𝗇 𝔒 (volume.restrict 𝔄).prod 𝔑
theorem anchored_cardinal_band_scale_joint_integrable (i : Fin n)
    (hlam : 𝖺) (hT : 𝖹) L x :
    Integrable (fun z =>
      𝔚 z.1 z.2)
      𝔒 := by
  letI := 𝔛 spatial_scale_measure_finite hT
  have hμ : volume.restrict 𝔄 ≤ 𝔛 spatialScaleMeasure :=
    Measure.restrict_mono_set volume Set.diff_subset
  letI :=
    isFiniteMeasure_of_le 𝔛 spatialScaleMeasure hμ
  apply Integrable.of_bound (anchored_cardinal_scale_continuous_actual i lam x).aestronglyMeasurable
    𝔊
  have hae : ∀ᵐ z ∂𝔒, z.1 ∈ 𝔛 spatialScaleDomain := by
    apply (Measure.ae_prod_iff_ae_ae $ (𝔛 spatial_scale_domain_isClosed).measurableSet.preimage measurable_fst ).mpr
    filter_upwards [ae_restrict_mem 𝔎] with t ht
    simp_all
  filter_upwards [hae] with z hz
  exact anchored_cardinal_scale_upper_bound i hlam hT x z.1 hz z.2

𝗇 𝔗 𝙖
def spatialScaleIntegralConstant (d : ℕ) : ℝ :=
   spatialInterpolationLambda d ^ 2 * Real.exp 𝔗 *
     Real.sqrt (2 * Real.pi / spatialInterpolationLambda d) ^ d

𝗇 𝔏 -(𝘺₂ * 𝖬₁)
theorem anchored_cardinal_scale_spatial_integral_product (i : Fin n) lam
    x t :
     ∫ Y, 𝔍 ∂𝔑 =
      ∏ j : SpatialScaleIndex i, 𝔖 * ∫ y in spatialPatchBox d,
        t j * Real.exp 𝔏 := by
  simp_rw [anchored_cardinal_scale_product_actual]
  unfold spatialPatchDesignMeasure
  rw [integral_fintype_prod_eq_prod
     fun j y =>
      t j * 𝔖 * Real.exp 𝔏 ]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← integral_const_mul]
  ring

𝗇 𝔇 spatialScaleIntegralConstant d ^ 𝖪₁
𝗇 𝔘 anchoredCardinalScale i (spatialInterpolationLambda d) x t Y
𝗇 𝔈 ∫ Y, 𝔘 ∂𝘓₁
𝗇 𝔙 𝗴₂
𝗇 𝔉 𝔙 ^ (1 - 𝙊 / 2)
theorem anchored_cardinal_scale_spatial_integral_decay (hd : 𝗆) (i : Fin n)
    x (hx : 𝘸₂) t (ht : 𝘩₁) :
    𝔈 ≤
      𝔇 *
        ∏ j, 𝔉 := by
  rw [anchored_cardinal_scale_spatial_integral_product]
  have h : ∏ j : SpatialScaleIndex i, spatialInterpolationLambda d ^ 2 *
      ∫ y in spatialPatchBox d, t j * Real.exp (-(t j * spatialInterpolationLambda d * 𝖬₁)) ≤
      ∏ j : SpatialScaleIndex i, spatialScaleIntegralConstant d * 𝔉 := by
    apply Finset.prod_le_prod₀
    · intro j hj
      apply 𝖧₁
      apply integral_nonneg
      intro y
      exact mul_nonneg (ht j) 𝙫
    · intro j hj
      have hdec := mul_le_mul_of_nonneg_left
        (spatial_scale_exponential_patch_integral_decay hd (t j) (ht j) x hx)
        $ sq_nonneg $ spatialInterpolationLambda d
      simpa only [spatialScaleIntegralConstant, mul_assoc] using hdec
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using h

𝗇 𝔅 𝔙 ^ (-b - 1)
𝗇 𝔐 Ici 0 \ spatialScaleDomain i L
/-- The actual squared-kernel spatial decay integrated over a true
truncated scale band, with every Fubini exchange justified. -/
theorem anchored_cardinal_band_scale_spatial_integral_bound (hd : 𝘚) (hn : 𝗏)
    (i : Fin n) x (hx : 𝘸₂) (hL : 𝚛₂) (hT : 𝖹) :
     ∫ Y, (∫ t : SpatialScaleVector i in 𝔄,
      𝔘) ∂𝔑 ≤
      (16 * spatialScaleIntegralConstant d) ^ 𝗈 *
        L ^ (4 - 𝙊) * (1 + Real.log L) ^ 𝗥 := by
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  let b : ℝ := 𝗗₁ / 2
  have hb : 𝔗 ≤ b := 𝖥₄
  have hpos : 𝙴₁ := 𝖡₄
  have hlam : 𝘹₂ := by unfold spatialInterpolationLambda; positivity
  have hjoint := anchored_cardinal_band_scale_joint_integrable i hlam hT L x
  have hfub :=
    (integral_prod_symm _ hjoint).symm.trans $ integral_prod _ hjoint
  rw [hfub]
  have hsub : 𝔄 ⊆ 𝔐 :=
    fun t ht => ⟨ht.1.1, ht.2⟩
  have hμ := Measure.restrict_mono_set volume hsub
  have hpowint := spatial_scale_complement_power_integrable hn i hpos L
  have hpowint' : Integrable (fun t => ∏ j, 𝔅)
      $ volume.restrict 𝔐 := hpowint
  have hpowband := hpowint'.mono_measure hμ
  have hdom : (fun t =>
      𝔈) ≤ᵐ[
        volume.restrict 𝔄]
       fun t => 𝔇 *
        ∏ j, 𝔅 := by
    filter_upwards [ae_restrict_mem 𝔎] with t ht
    have h := anchored_cardinal_scale_spatial_integral_decay  𝖡₃  i x hx t ht.1.1
    grind
  have hnn : ∀ᵐ t ∂volume.restrict 𝔐,
      0 ≤ ∏ j : SpatialScaleIndex i, 𝔅 := by
    filter_upwards [ae_restrict_mem $ measurableSet_Ici.diff 𝘷₂ ] with t ht
    apply Finset.prod_nonneg
    intro j hj
    exact Real.rpow_nonneg (by have htj : 𝖥₂ := ht.1 j; linarith) _
  have hC : 0 ≤ 𝔇 := by
    unfold spatialScaleIntegralConstant
    positivity
  have hfirst := integral_mono_ae hjoint.integral_prod_left (hpowband.const_mul _) hdom
  rw [integral_const_mul] at hfirst
  have hmiddle := integral_mono_measure hμ hnn hpowint
  have htail := spatial_scale_complement_power_integral_le hn i hb hL
  have hfull := hfirst.trans $ (mul_le_mul_of_nonneg_left hmiddle hC).trans $ mul_le_mul_of_nonneg_left htail hC
  rw [spatial_scale_index_card, show -2 * b = 𝚜₂ by ring] at hfull
  simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hfull
