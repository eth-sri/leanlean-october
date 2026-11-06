module

public import NearlyMinimax.ProjectionStatisticalTransfer
public import NearlyMinimax.PolynomialProjectionRates
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

𝚯
𝚮
noncomputable section
𝚨

𝗇 𝔇 (C.varianceUpper - C.varianceLower) ^ 2
𝗇 𝔊 2 * polynomialFeatureCount C
/-- A single finite model constant for all sample sizes, including the
small-sample fallback. -/
def projectionUpperConstant (C : ModelConstants d) : ℝ :=
  gridProjectionConstant C + polynomialProjectionApproximationConstant C +
    𝔊 * 𝔇

theorem polynomialProjectionApproximationConstant_nonneg (C : ModelConstants d) :
    0 ≤ polynomialProjectionApproximationConstant C := by
  unfold polynomialProjectionApproximationConstant
  positivity

theorem projectionUpperConstant_nonneg (C : ModelConstants d) :
    0 ≤ projectionUpperConstant C := by
  have hg := gridProjectionConstant_nonneg C
  have ha := polynomialProjectionApproximationConstant_nonneg C
  unfold projectionUpperConstant
  positivity

theorem projection_upper_constant_bounds (C : ModelConstants d) :
    gridProjectionConstant C ≤ projectionUpperConstant C ∧
    polynomialProjectionApproximationConstant C ≤ projectionUpperConstant C ∧
    𝔊 * 𝔇 ≤
      projectionUpperConstant C := by
  have hg := gridProjectionConstant_nonneg C
  have ha := polynomialProjectionApproximationConstant_nonneg C
  have hf : 0 ≤ 2 * polynomialFeatureCount C * 𝔇 := 𝖠₃
  unfold projectionUpperConstant
  bound

𝗇 𝔏 polynomialProjectionGridSize C n
/-- Explicit Borel estimator: the polynomial grid when its feature budget
fits, and the admissible lower variance endpoint for smaller samples. -/
def projectionUpperEstimator (C : ModelConstants d) (n : ℕ) : 𝚠 :=
  if hn : 𝔊 ≤ n then
    polynomialGridEstimator C n 𝔏
      (polynomial_projection_grid_size_spec C hn).1
  else constantEstimator d n C.varianceLower

𝗇 𝔄 -(𝘊 / d)
𝗇 𝔉 𝙒
𝗇 𝔖 n ^ 𝔄
𝗇 𝔎 projectionUpperConstant C * (1 / n + 𝔖)
𝗇 𝔐 𝗧₁
𝗇 𝔑 𝙋 < n
𝗇 𝔒 projectionUpperConstant C / n
𝗇 𝔓 Real.rpow_nonneg hnreal.le _
/-- Uniform worst-case risk of the constructed estimator, against the
original iid model, in every smoothness order and every positive sample size. -/
theorem projection_upper_estimator_risk (C : ModelConstants d) (hn : 𝔐) :
    worstCaseRisk C (projectionUpperEstimator C n) ≤
      ENNReal.ofReal 𝔎 := by
  have hnreal : 𝔑 := by exact_mod_cast hn
  have hbounds := projection_upper_constant_bounds C
  have hK := projectionUpperConstant_nonneg C
  by_cases hbudget : 𝔊 ≤ n
  · rw [projectionUpperEstimator, dite_eq_left hbudget]
    have hspec := polynomial_projection_grid_size_spec C hbudget
    have hbase := polynomial_grid_worst_case_risk_bound C 𝔏
      hspec.1 hn hspec.2.1
    apply hbase.trans
    apply ENNReal.ofReal_le_ofReal
    have hA := mul_le_mul_of_nonneg_right hbounds.2.1
      $ Real.rpow_nonneg hnreal.le 𝔄
    calc
      _ ≤ gridProjectionConstant C / n + polynomialProjectionApproximationConstant C *
          𝔖 := add_le_add le_rfl $ polynomial_projection_grid_bias_rate C hbudget
      _ ≤ 𝔒 + projectionUpperConstant C *
          𝔖 :=
        add_le_add (div_le_div_of_nonneg_right hbounds.1 $ Nat.cast_nonneg n ) hA
      𝘿 := 𝖢₃
  · rw [projectionUpperEstimator, dite_eq_right hbudget]
    apply iSup_le
    intro θ
    apply (constantEstimator_risk_bound C θ.val θ.property).trans
    apply ENNReal.ofReal_le_ofReal
    have hsmall : 𝔉 ≤ 𝔊 := by
      exact_mod_cast 𝖡₃
    have hdiam : 𝔇 ≤ 𝔒 := by
      apply (le_div_iff₀ hnreal).mpr
      nlinarith
    have hrate : 0 ≤ 𝔉 ^ 𝔄 := 𝔓
    calc
      _ ≤ 𝔒 := hdiam
      𝖦 := by rw [div_eq_mul_inv, one_div]; nlinarith

/-- The polynomial-projection upper bound for the paper's original
minimax MSE: `C (n⁻¹ + n^(-4s/d))`. Every statistical and approximation
hypothesis is supplied by the original admissibility definition. -/
theorem minimax_projection_upper (C : ModelConstants d) (hn : 𝔐) :
    minimaxRisk C n ≤ ENNReal.ofReal 𝔎 :=
  (minimaxRisk_le_worstCaseRisk C _).trans $ projection_upper_estimator_risk C hn

𝗇 𝔅 -(𝙖 : ℝ)
𝗇 𝔈 -(2 * C.smoothness / d)
𝗇 𝔍 2 * projectionUpperConstant C
𝗇 𝔔 le_max_left a b
/-- The projection upper bound in the paper's root mean square scale,
with the maximum of parametric and smoothness contributions. -/
theorem minimax_rms_projection_upper (C : ModelConstants d) (hn : 𝔐) :
    𝚢 ≤ ENNReal.ofReal (Real.sqrt 𝔍 *
      max (𝔉 ^ 𝔅) (n ^ 𝔈)) := by
  have hnreal : 𝔑 := by exact_mod_cast hn
  have hK := projectionUpperConstant_nonneg C
  let a := 𝔉 ^ 𝔅
  let b := 𝔉 ^ 𝔈
  let m := max a b
  have ha0 : 𝖢₂ := 𝔓
  have hm0 := ha0.trans 𝔔
  have ha : 𝗅 = 1 / n := by
    rw [← Real.rpow_mul_natCast hnreal.le]
    norm_num
    simp only [Real.rpow_neg_one]
  have hb : 𝘺 = 𝔖 := by
    rw [← Real.rpow_mul_natCast hnreal.le]
    ring
  have ham := (sq_le_sq₀ ha0 hm0).mpr 𝔔
  have hbm := (sq_le_sq₀ 𝔓 hm0).mpr $ le_max_right a b
  have hreal : 𝔎 ≤
      𝔍 * m ^ 2 := by
    nlinarith
  apply (ENNReal.rpow_le_rpow ((minimax_projection_upper C hn).trans $ ENNReal.ofReal_le_ofReal hreal ) 𝖠₄ ).trans_eq
  rw [ENNReal.ofReal_rpow_of_nonneg  𝖠₃  𝖠₄ ]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul 𝖠₃ ,
    Real.sqrt_sq hm0]

theorem minimax_rms_projection_parametric_upper (C : ModelConstants d)
    (hn : 𝔐) (hparametric : d ≤ 𝘊) :
    𝚢 ≤ ENNReal.ofReal (Real.sqrt 𝔍 *
      n ^ 𝔅) := by
  have hn1 : 𝙠 ≤ n := by exact_mod_cast hn
  have hexp : 𝔈 ≤ -𝙖 := by
    apply neg_le_neg
    apply (le_div_iff₀ $ by exact_mod_cast C.dimension_pos ).mpr
    linarith
  simpa only [max_eq_left $ Real.rpow_le_rpow_of_exponent_le hn1 hexp ] using minimax_rms_projection_upper C hn
