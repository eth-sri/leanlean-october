module

public import NearlyMinimax.CardinalBandSpatial
public import NearlyMinimax.SpatialCardinalContinuity
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! True squared coefficient norm of actual centered interpolation bands.
The estimates are derived from cardinal polynomial coefficients, Gamma
normalization, weighted Cauchy--Schwarz and Gaussian spatial decay. -/
𝚫
𝚨
𝚩
𝚭

𝗇 𝔅 𝗕₁ \ spatialScaleDomain i L
𝗇 𝔐 𝙇
𝗇 𝔑 𝙮
𝗃 𝔘 ἀ i lam
𝗃 𝔥 𝔘 ἀ U
def centeredCardinalBandMatrix (i : Fin n) (lam L T : ℝ)
    (U : 𝔐) (β β' : 𝔑) : ℝ :=
  ∫ t : SpatialScaleVector i in 𝔅,
    𝔥 spatialCenteredCardinalMatrix t β β'

𝗇 𝔣 100 * d
𝗇 𝔄 𝔣 ^ (2 * 𝖪₁)
𝗇 𝔒 𝗖₁
𝗃 𝔗 ἀ (D := D) i
𝗇 𝔚 𝖹
𝗇 𝔛 anchoredPatchConfiguration i x
section

𝛔

include i

𝗇 𝔇 spatialMatrixL1 $ 𝔗 spatialCenteredCardinalMatrix lam U t
𝗇 𝔞 spatialScaleMeasure i T
𝗇 𝔟 𝔘 spatial_centered_cardinal_matrix_integrable T hT U β β'
theorem spatial_centered_matrix_cost_integrable lam
    (hT : 𝔚) (U : 𝔐) :
    Integrable (fun t => 𝔇)
      𝔞 := integrable_finsetSum _ fun β _ => integrable_finsetSum _
     fun β' _ => (𝔟).abs

𝗇 𝔍 spatialMatrixL1 $ 𝔗 centeredCardinalBandMatrix lam L T U
𝗇 𝔏 fun β' _ => (hi β β').abs
𝗃 𝔧 ∫ t : SpatialScaleVector i in 𝔅, ἀ
theorem spatial_centered_band_cost_le_integral_cost lam L
    (hT : 𝔚) (U : 𝔐) :
    𝔍 ≤
      𝔧 𝔇 := by
  have hμ : volume.restrict 𝔅 ≤ 𝔞 :=
    Measure.restrict_mono_set volume Set.sdiff_subset
  have hi (β β' : 𝔑) :=
    (𝔟).mono_measure hμ
  unfold spatialMatrixL1 centeredCardinalBandMatrix
  rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ 𝔏 ]
  apply Finset.sum_le_sum
  intro β hβ
  rw [integral_finsetSum _ 𝔏]
  exact Finset.sum_le_sum fun β' _ => by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
       fun t => 𝔥 spatialCenteredCardinalMatrix t β β'

𝗇 𝔤 𝘒₁
𝗇 𝔈 spatialCardinalScale lam 𝔤 U i
𝗇 𝔎 (spatial_scale_domain_isClosed i T).measurableSet.diff 𝘷₂
𝗇 𝔔 Measure.restrict_mono_set volume hs
𝗇 𝔜 fun t => 𝔈
𝗃 𝔦 𝔘 ἀ hlam U
/-- The squared actual centered band matrix is bounded by its actual
scale kernel integral; no desired norm bound is a premise. -/
theorem centered_cardinal_band_matrix_l1_square_le (hlam : 𝖺) L (hT : 𝔚)
    (U : 𝔐) (hU : ∀ l r, |𝚚₂| ≤ 2) :
    𝔍 ^ 2 ≤
      𝔄 *
        𝔧 𝔈 := by
  let s := 𝔅
  let C : ℝ := 𝔄
  have hs : s ⊆ Ici 0 := fun t ht => ht.1.1
  have hμ : volume.restrict s ≤ 𝔞 := Measure.restrict_mono_set volume Set.sdiff_subset
  have hw :=
    (𝔦 spatial_cardinal_weight_orthant_integrable).mono_measure
      𝔔
  have hscale : Integrable 𝔜 $ volume.restrict s := by
    have hi : IntegrableOn 𝔜
        𝗕₁ :=
      (𝔥 spatial_centered_cardinal_scale_continuous).continuousOn.integrableOn_compact
        $ spatial_scale_domain_isCompact i T hT
    exact hi.mono_set Set.sdiff_subset
  have hnn : ∀ᵐ t ∂volume.restrict s, 0 ≤ 𝔈 := by
    filter_upwards [ae_restrict_mem 𝔎] with t ht
    exact 𝔥 spatial_cardinal_scale_nonnegative t ht.1.1
  have hwn :=
    (𝔥 spatial_cardinal_weight_orthant_nonnegative).filter_mono
      $ ae_mono 𝔔
  have hdom : ∀ᵐ t ∂volume.restrict s,
      𝔇 ^ 2 ≤
        spatialCardinalWeight lam 𝔤 U i *
          (C * 𝔈) := by
    filter_upwards [ae_restrict_mem 𝔎] with t ht
    exact 𝔥 spatial_centered_matrix_l1_square_le_weight_scale hU t ht.1.1
  have hcs := integral_square_le_weight_mass_mul (volume.restrict s) _ _ _ ((𝔗 spatial_centered_matrix_cost_integrable lam hT U).mono_measure hμ) hw (hscale.const_mul C)
    hwn (hnn.mono fun t ht => mul_nonneg  𝖠₃  ht ) hdom
  have hmass :=
    (integral_mono_measure 𝔔
      𝔥 spatial_cardinal_weight_orthant_nonnegative
      𝔦 spatial_cardinal_weight_orthant_integrable).trans
        𝔦 spatial_cardinal_weight_orthant_integral_le_one
  have hbound := hcs.trans $ by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass $ integral_nonneg_of_ae $ hnn.mono fun t ht => mul_nonneg  𝖠₃  ht
  have hnCost : 0 ≤ ∫ t in s, 𝔇 :=
    integral_nonneg fun _ => spatial_matrix_l1_nonnegative _
  have htriangle := (sq_le_sq₀ (spatial_matrix_l1_nonnegative _) hnCost).mpr
    $ 𝔘 spatial_centered_band_cost_le_integral_cost L hT U
  exact htriangle.trans $ by simpa only [integral_const_mul] using hbound

theorem anchored_patch_configuration_continuous (x : Covariate d) :
    Continuous 𝔛 := by
  apply continuous_pi
  intro l
  unfold anchoredPatchConfiguration
  split_ifs <;> fun_prop

theorem anchored_centered_matrix_entry_joint_continuous lam
    x (β β' : 𝔑) :
    Continuous fun z : SpatialScaleVector i × 𝔒 =>
      𝔘 spatialCenteredCardinalMatrix (𝔛 z.2) z.1 β β' := by
  have hc (γ : 𝔑) :
      Continuous fun z : SpatialScaleVector i × 𝔒 =>
        highFrameCoefficients (spatialCardinalPolynomial (𝔛 z.2) i) γ :=
    (spatial_cardinal_polynomial_coefficients_continuous i $ polynomialBoxExponent γ.val ).comp
      $ (anchored_patch_configuration_continuous i x).comp continuous_snd
  exact ((𝔘 anchored_cardinal_scale_continuous_actual x).mul $ hc β ).mul $ hc β'

end

𝗇 𝔓 anchoredPatchConfiguration i x Y
def anchoredCenteredCardinalBandMatrix (i : Fin n) (lam L T : ℝ) (x : Covariate d)
    (Y : 𝔒) : 𝔑 → 𝔑 → ℝ :=
  𝔘 centeredCardinalBandMatrix L T 𝔓

𝗇 𝔖 𝘓₁
𝗇 𝔙 (anchored_cardinal_band_scale_joint_integrable i hlam hT L x).integral_prod_right.const_mul 𝔄
𝗇 𝔠 𝘸₂
𝗇 𝔡 centered_cardinal_band_matrix_l1_square_le i hlam L hT 𝔓 hY
section

𝛔

include i

theorem anchored_centered_band_matrix_entry_measurable lam L T
    x (β β' : 𝔑) :
    Measurable fun Y => 𝔘 anchoredCenteredCardinalBandMatrix L T x Y β β' := by
  have h := (𝔘 anchored_centered_matrix_entry_joint_continuous x β β').stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict 𝔅)
  exact h.measurable

theorem anchored_patch_configuration_in_box_ae x
    (hx : 𝔠) :
    ∀ᵐ Y ∂ 𝔖, ∀ l r, |𝔛 Y l r| ≤ 2 := by
  have hae : ∀ᵐ Y ∂ 𝔖, ∀ j , Y j ∈ spatialPatchBox d := by
    apply ae_all_iff.mpr
    intro j
    exact (Measure.tendsto_eval_ae_ae
      ).eventually $ ae_restrict_mem measurableSet_Icc
  filter_upwards [hae] with Y hY
  intro l r
  by_cases hl : l ≠ i
  · have hh := hY ⟨l, hl⟩
    simp only [anchoredPatchConfiguration, dite_eq_left hl]
    apply (abs_le.mpr ⟨hh.1 r, hh.2 r⟩).trans
    norm_num
  · have hli := not_ne_iff.mp hl
    subst l
    rw [anchored_configuration_same]
    exact (abs_le.mpr ⟨hx.1 r, hx.2 r⟩).trans 𝖠₄

𝗇 𝔉 fun Y => spatialMatrixL1 (𝔗 anchoredCenteredCardinalBandMatrix lam L T x Y) ^ 2
theorem anchored_centered_band_matrix_l1_square_measurable lam L T (x : Covariate d) :
    Measurable 𝔉 := (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _
     fun β' _ => (𝔘 anchored_centered_band_matrix_entry_measurable L T x β β').abs ).pow_const 2

theorem anchored_centered_band_matrix_l1_square_integrable (hlam : 𝖺) (hT : 𝔚) L x (hx : 𝔠) :
    Integrable 𝔉
      𝔖 := by
  have hi := 𝔙
  apply hi.mono' (𝔘 anchored_centered_band_matrix_l1_square_measurable L T x).aestronglyMeasurable
  filter_upwards [anchored_patch_configuration_in_box_ae i x hx] with Y hY
  rw [Real.norm_eq_abs, 𝗤]
  exact 𝔡

end

𝗇 𝔊 spatialMatrixL1 (𝔗 anchoredCenteredCardinalBandMatrix (spatialInterpolationLambda d) L T x Y) ^ 2
𝗇 𝔢 𝗈
/-- Actual fixed-head spatial L² bound for the centered cardinal band.
The constant is explicit and depends only on dimension. -/
theorem anchored_centered_band_matrix_l1_square_integral_le (hd : 𝘚) (hn : 𝗏)
    (i : Fin n) x (hx : 𝔠) (hL : 𝚛₂) (hT : 𝔚) :
     ∫ Y, 𝔊
      ∂ 𝔖 ≤
      (𝔣 ^ 2 * 16 * spatialScaleIntegralConstant d) ^ 𝔢 *
        L ^ (4 - 𝙊) * (1 + Real.log L) ^ 𝗥 := by
  have hlam : 𝘹₂ := by unfold spatialInterpolationLambda; positivity
  have hi := 𝔙
  have hdom : (fun Y => 𝔊)
      ≤ᵐ[𝔖]
       fun Y => 𝔄 *
        ∫ t in 𝔅,
          anchoredCardinalScale i (spatialInterpolationLambda d) x t Y := by
    filter_upwards [anchored_patch_configuration_in_box_ae i x hx] with Y hY
    exact 𝔡
  have hfirst := integral_mono_ae (anchored_centered_band_matrix_l1_square_integrable i hlam hT L x hx) hi hdom
  rw [integral_const_mul, spatial_scale_index_card] at hfirst
  have htail := mul_le_mul_of_nonneg_left (anchored_cardinal_band_scale_spatial_integral_bound hd hn i x hx hL hT)
    (by positivity : 0 ≤ (100 * 𝙊) ^ (2 * 𝔢))
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm, mul_assoc, mul_comm, mul_left_comm] using hfirst.trans htail
