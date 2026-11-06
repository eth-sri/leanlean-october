module

public import NearlyMinimax.CardinalProductDesign
public import NearlyMinimax.ExponentialSpatialKernels
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! True full-product spatial L2 bounds for the actual interpolation bands. -/
𝚫
𝚨
𝚩
𝚾

𝗇 𝔊 𝖹
𝗇 𝔧 centeredCardinalBandMatrix i lam L T U
𝗇 𝔍 𝔧 β β'
𝗇 𝔏 𝚛₂
𝗇 𝔐 L ≤ T
𝗇 𝔑 𝙮
𝗃 𝔡 ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i ἀ
theorem centeredCardinalBandMatrix_eq_difference (i : Fin n) lam
    (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐)
    U (β β' : 𝔑) :
    𝔍 =
      𝔡 T -
      𝔡 L := setIntegral_sdiff 𝘷₂
    (spatial_centered_cardinal_matrix_integrable i lam T hT U β β')
    $ spatial_scale_domain_mono i (lt_of_lt_of_le  𝖠₄  hL) hLT

𝗇 𝔢 spatial_centered_cardinal_matrix_joint_continuous i lam β β'
𝗃 𝔨 fun U => ἀ
𝗃 𝔬 ἀ i lam hL hT hLT
theorem centeredCardinalBandMatrix_continuous (i : Fin n) lam
    (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) (β β' : 𝔑) :
    Continuous 𝔨 𝔍 := by
  simp_rw [𝔬 centeredCardinalBandMatrix_eq_difference]
  exact (continuous_parametric_integral_of_continuous
    𝔢
    $ spatial_scale_domain_isCompact i T hT ).sub
      $ continuous_parametric_integral_of_continuous
        𝔢
        $ spatial_scale_domain_isCompact i L hL

𝗇 𝔅 𝙇
𝗃 𝔠 ἀ (D := D)
𝗇 𝔇 𝔠 centeredCardinalBandMatrix i lam L T U
theorem centeredCardinalBandMatrix_l1_square_measurable (i : Fin n) lam
    (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) :
    Measurable fun U : 𝔅 => spatialMatrixL1 𝔇 ^ 2 := (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _
     fun β' _ => (𝔬 centeredCardinalBandMatrix_continuous β β').measurable.abs ).pow_const 2

𝗇 𝔥 𝗈
def cardinalBandSquareBudget (d n : ℕ) (L : ℝ) : ℝ :=
  ((100 * 𝙊) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ 𝔥 *
    L ^ (4 - 𝙊) * (1 + Real.log L) ^ 𝗥

𝗇 𝔔 𝖮₁
𝗇 𝔗 cardinalBandSquareBudget d n L
𝗇 𝔣 𝖥
𝗃 𝔩 ∫ U, ἀ ∂ 𝔔
section

variable (hd : 𝘚)
    (hn : 𝗏)

include hd hn

𝗃 𝔯 𝔠 ἀ i (spatialInterpolationLambda d) L T
𝗇 𝔛 𝔯 anchoredCenteredCardinalBandMatrix
𝗇 𝔈 fun z => spatialMatrixL1 (𝔛 z.1 z.2) ^ 2
𝗇 𝔒 𝖪
𝗇 𝔚 Covariate d × 𝗖₁
𝗇 𝔜 (𝔒).prod 𝘓₁
𝗇 𝔤 anchored_centered_band_matrix_l1_square_integral_le hd hn i x hx hL hT
theorem centeredCardinalBandMatrix_joint_integrable (i : Fin n) (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) :
    Integrable 𝔈
      𝔜 := by
  let f : 𝔚 → ℝ := 𝔈
  have hm : Measurable f := (centeredCardinalBandMatrix_l1_square_measurable
     i (spatialInterpolationLambda d) hL hT hLT).comp (cardinalHeadSplit i).symm.measurable
  have hx : ∀ᵐ x ∂ 𝔒, 𝘸₂ :=
    ae_restrict_mem measurableSet_Icc
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hx.mono fun x hx => anchored_centered_band_matrix_l1_square_integrable i
    (by unfold spatialInterpolationLambda; positivity) hT L x hx , ?_⟩
  apply (integrable_const 𝔗).mono' hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  filter_upwards [hx] with x hx
  rw [Real.norm_eq_abs, 𝗪]
  simp only [f, Real.norm_eq_abs, abs_sq]
  exact 𝔤

𝗇 𝔓 spatialMatrixL1 (𝔯 centeredCardinalBandMatrix U) ^ 2
𝗇 𝔙 centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT
theorem centeredCardinalBandMatrix_full_integrable i (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) :
    Integrable 𝔨 𝔓 𝔔 := by
  have hp := (cardinalHeadSplit_measurePreserving i 𝔒).symm
  exact (hp.integrable_comp_emb (cardinalHeadSplit i).symm.measurableEmbedding).mp
      𝔙

theorem centeredCardinalBandMatrix_full_integral_le i (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) :
    𝔩 𝔓 ≤
      𝔣 * 𝔗 := by
  rw [fullSpatialPatchDesign_split i _]
  change ∫ z : 𝔚,
    spatialMatrixL1 (anchoredCenteredCardinalBandMatrix i
      (spatialInterpolationLambda d) L T z.1 z.2) ^ 2
      ∂ 𝔜 ≤ _
  rw [integral_prod _ 𝔙]
  have hb : (fun x => ∫ Y, spatialMatrixL1 (𝔛 x Y) ^ 2 ∂𝘓₁) ≤ᵐ[
      𝔒] fun _ => 𝔗 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact 𝔤
  apply (integral_mono_ae (𝔠 centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT).integral_prod_left (integrable_const _) hb).trans_eq
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ]
  change 𝗮₁ * 𝔗 = _
  rw [spatialPatchBox_real_volume]

end

def globalCardinalBandMatrix (lam L T : ℝ) (U : 𝔅)
    (β β' : 𝔑) : ℝ :=
  𝖯₁ β β' - integratedCardinalMatrix lam L U β β'

theorem globalCardinalBandMatrix_eq_sum lam
    (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐)
    (U : 𝔅) (β β' : 𝔑) :
    globalCardinalBandMatrix lam L T U β β' = ∑ i, 𝔍 := by
  simp only [globalCardinalBandMatrix, integratedCardinalMatrix, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    (𝔬 centeredCardinalBandMatrix_eq_difference U β β').symm

𝗇 𝔦 A i β β'
𝗃 𝔭 fun β β' => ∑ i, ἀ
theorem cardinal_matrix_l1_sum_le [Fintype I]
    (A : I → 𝔑 → 𝔑 → ℝ) :
    spatialMatrixL1 𝔭 𝔦 ≤ ∑ i, spatialMatrixL1 (A i) := by
  calc
    _ ≤ ∑ β : 𝔑, ∑ β' : 𝔑, ∑ i : I, |𝔦| :=
      Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun β' _ => Finset.abs_sum_le_sum_abs ..
    _ = ∑ β : 𝔑, ∑ i : I, ∑ β' : 𝔑, |𝔦| := by
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.sum_comm]
    𝘿 := Finset.sum_comm

𝗇 𝔞 𝔠 globalCardinalBandMatrix
𝗇 𝔘 𝔞 lam L T U
theorem globalCardinalBandMatrix_square_le_sum lam
    (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) (U : 𝔅) :
    spatialMatrixL1 𝔘 ^ 2 ≤
      n * ∑ i, spatialMatrixL1 𝔇 ^ 2 := by
  have he : 𝔘 =
      𝔭 𝔍 := by
    funext β β'
    exact globalCardinalBandMatrix_eq_sum lam hL hT hLT U β β'
  rw [he]
  have hsum := cardinal_matrix_l1_sum_le fun i =>
    𝔇
  apply ((sq_le_sq₀ (spatial_matrix_l1_nonnegative _)
    $ Finset.sum_nonneg fun i _ => spatial_matrix_l1_nonnegative _ ).mpr hsum).trans
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      𝙃 fun i => spatialMatrixL1 𝔧

section

variable (hd : 𝘚)
    (hn : 𝗏)

include hd hn

𝗃 𝔫 ἀ $ spatialInterpolationLambda d
𝗇 𝔄 spatialMatrixL1 (𝔫 𝔞 L T U) ^ 2
𝗃 𝔪 fun i _ => 𝔠 ἀ hd hn i hL hT hLT
𝗇 𝔉 (integrable_finsetSum Finset.univ 𝔪 centeredCardinalBandMatrix_full_integrable).const_mul n
𝗇 𝔟 𝔫 globalCardinalBandMatrix_square_le_sum hL hT hLT
theorem globalCardinalBandMatrix_square_integrable (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) :
    Integrable 𝔨 𝔄
      𝔔 := by
  have hi := 𝔉
  have hm : Measurable fun U : 𝔅 =>
      𝔄 := (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _
       fun β' _ => (𝔫 integrated_cardinal_band_continuous hL hT β β').measurable.abs ).pow_const 2
  apply hi.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    exact 𝔟 U

theorem globalCardinalBandMatrix_square_integral_le (hL : 𝔏) (hT : 𝔊) (hLT : 𝔐) :
    𝔩 𝔄 ≤ 𝚍 * 𝔣 * 𝔗 := by
  have hi := 𝔉
  have hh := integral_mono (globalCardinalBandMatrix_square_integrable hd hn hL hT hLT)
    hi 𝔟
  rw [integral_const_mul, integral_finsetSum _ fun i _ =>
    centeredCardinalBandMatrix_full_integrable hd hn i hL hT hLT ] at hh
  apply hh.trans
  have hs := 𝗣₁ 𝔪 centeredCardinalBandMatrix_full_integral_le
  convert mul_le_mul_of_nonneg_left hs $ Nat.cast_nonneg n using 1 <;> simp <;> ring

𝗇 𝔎 𝔫 𝔞 1 T U = 𝔫 integratedCardinalMatrix T U
𝗇 𝔖 spatialMatrixL1 (𝔠 integratedCardinalMatrix (spatialInterpolationLambda d) T U) ^ 2
𝗃 𝔮 𝔠 ἀ hd hn (le_refl 1) hT hT
theorem integratedCardinalMatrix_full_square_integrable (hT : 𝔊) :
    Integrable 𝔨 𝔖 𝔔 := by
  have he (U : 𝔅) : 𝔎 := by
    unfold globalCardinalBandMatrix
    rw [integrated_cardinal_matrix_one_eq_zero hn]
    simp
  have hi := 𝔮 globalCardinalBandMatrix_square_integrable
  simp_all

theorem integratedCardinalMatrix_full_square_integral_le (hT : 𝔊) :
    𝔩 𝔖 ≤ 𝚍 * 𝔣 *
      𝗬₁ ^ 𝔥 := by
  have he (U : 𝔅) : 𝔎 := by
    unfold globalCardinalBandMatrix
    rw [integrated_cardinal_matrix_one_eq_zero hn]
    simp
  have hb := 𝔮 globalCardinalBandMatrix_square_integral_le
  simp_rw [he] at hb
  simpa only [cardinalBandSquareBudget, Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one] using hb
