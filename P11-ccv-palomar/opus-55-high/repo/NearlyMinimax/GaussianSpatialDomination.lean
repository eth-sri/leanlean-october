module

public import NearlyMinimax.CardinalScaleWeights
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual Gaussian spatial domination for the cardinal scale kernels. -/
𝛄
𝚨
𝚩
set_option maxHeartbeats 300000

𝗇 𝔅 Real.exp $ -b * 𝖬₁
𝗇 𝔠 𝗵₂
𝗃 𝔬 -b * ἀ ^ 2
theorem radial_gaussian_factorization b (x y : Covariate d) :
    𝔅 =
      ∏ r, Real.exp 𝔬 𝔠 := by
  unfold spatialSquaredDistance
  rw [Finset.mul_sum, Real.exp_sum]

theorem radial_gaussian_integrable b (hb : 𝙴₁) (x : Covariate d) :
    Integrable (fun y => 𝔅) volume := by
  simp_rw [radial_gaussian_factorization]
  exact Integrable.fintype_prod


     fun r => (integrable_exp_neg_mul_sq hb).comp_sub_right $ x r

𝗃 𝔭 Real.sqrt (Real.pi / ἀ) ^ d
𝗇 𝔓 𝔭 b
/-- Exact finite-dimensional Gaussian normalization, including arbitrary
spatial center. -/
theorem radial_gaussian_integral b (x : Covariate d) :
     ∫ y, 𝔅 = 𝔓 := by
  simp_rw [radial_gaussian_factorization]
  rw [integral_fintype_prod_volume_eq_prod
     fun r y => Real.exp $ -b * (y - x r) ^ 2 ]
  simp_rw [integral_sub_right_eq_self fun y => Real.exp 𝔬 y , integral_gaussian]
  simp

𝗇 𝔏 Real.exp $ -z
𝗇 𝔑 -2 * z
/-- A second-order exponential-series term absorbs the squared radial
factor at every nonnegative argument. -/
theorem quadratic_exp_absorption z (hz : 0 ≤ z) :
    z ^ 2 * Real.exp 𝔑 ≤ 2 * 𝔏 := by
  have hmul := mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp z hz 2) $ Real.exp_nonneg 𝔑
  rw [← Real.exp_add, show z + 𝔑 = -z by ring] at hmul
  linarith

𝗇 𝔄 1 + t
𝗇 𝔇 𝙖
𝗇 𝔖 -(𝔄 * alpha)
𝗇 𝔪 8 * Real.exp 𝔇
𝗇 𝔗 𝔪 / 𝔄
𝗇 𝔚 alpha ^ 2 * Real.exp 𝔖
𝗇 𝔛 𝘈
𝗇 𝔜 𝔄 ^ 2
𝗇 𝔡 𝔄 * alpha / 2
𝗇 𝔫 8 / 𝔜 * 𝔏
𝗃 𝔮 t * Real.exp ἀ
/-- The actual unary scale density has the spatial decay factor
(1+t)^-1 before Gaussian integration. -/
theorem unary_scale_density_gaussian_domination alpha t
    (ha : 0 ≤ alpha) (haHalf : alpha ≤ 𝔇) (ht : 𝔛) :
    unaryScaleDensity alpha t ≤
      𝔗 * Real.exp (-𝔡) := by
  have hs : 0 < 𝔄 := 𝖡₄
  let z := 𝔡
  have hAbs := quadratic_exp_absorption z 𝖠₃
  have he : Real.exp (-(alpha * t)) = Real.exp alpha * Real.exp 𝔖 := by
    rw [← Real.exp_add]
    ring
  have hez : 𝔑 = 𝔖 := 𝖢₃
  have hscaled := mul_le_mul_of_nonneg_left hAbs (by positivity : 0 ≤ 4 / 𝔜)
  have hmain : 𝔚 ≤
      𝔫 := by
    have hleft : 4 / 𝔜 * (z ^ 2 * Real.exp 𝔖) =
        𝔚 := by
      field_simp
      ring
    grind
  unfold unaryScaleDensity
  rw [he]
  calc
    _ = 𝔮 alpha * 𝔚 := 𝖢₃
    _ ≤ 𝔮 𝔇 * 𝔫 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr haHalf) ht) hmain  𝖠₃  𝖠₃
    _ ≤ 𝔗 * 𝔏 := by
      have hratio : t / 𝔜 ≤ 1 / 𝔄 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hs) hs).mpr
        nlinarith
      have h := mul_le_mul_of_nonneg_right hratio
        (by positivity : 0 ≤ 𝔪 * 𝔏)
      grind
    𝘿 := rfl

def spatialPatchBox (d : ℕ) : 𝘶 := Icc (fun _ => -1) 𝙃

𝗇 𝔨 𝙊
def spatialInterpolationLambda (d : ℕ) : ℝ := 1 / (8 * 𝔨)

𝗇 𝔐 𝖬₁
𝗇 𝔔 𝘸₂
𝗇 𝔢 𝗆
𝗇 𝔣 y ∈ spatialPatchBox d
theorem spatial_patch_alpha_bounds (hd : 𝔢) x y
    (hx : 𝔔) (hy : 𝔣) :
    0 ≤ spatialInterpolationLambda d * 𝔐 ∧
      spatialInterpolationLambda d * 𝔐 ≤ 𝔇 := by
  have hdist : 0 ≤ 𝔐 := 𝗫₁
  have hdistUpper : 𝔐 ≤ 4 * d := by
    calc
      _ ≤ ∑ _r : Fin d, 𝗦 := by
        apply Finset.sum_le_sum
        intro r _
        have hxr := abs_le.mpr ⟨hx.1 r, hx.2 r⟩
        have hyr := abs_le.mpr ⟨hy.1 r, hy.2 r⟩
        have hsub : |𝔠| ≤ 2 := (abs_sub ..).trans $ by linarith
        simpa only [sq_abs, show 𝙉 ^ 2 = 4 by norm_num] using 𝗂 hsub 2
      𝘿 := by simp [mul_comm]
  constructor
  · unfold spatialInterpolationLambda
    positivity
  · unfold spatialInterpolationLambda
    rw [one_div_mul_eq_div, div_le_iff₀ 𝖠₃ ]
    linarith

𝗇 𝔞 spatialUnaryWeight lam t x y
theorem spatial_unary_patch_integrable lam t x :
    IntegrableOn (fun y => 𝔞) $ spatialPatchBox d := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  unfold spatialUnaryWeight spatialSquaredDistance
  fun_prop

𝗇 𝔎 ∫ y in spatialPatchBox d, spatialUnaryWeight (spatialInterpolationLambda d) t x y
𝗇 𝔘 lam * 𝔄 / 2
𝗇 𝔙 A * 𝔅
𝗇 𝔟 _ ≤ ∫ y in spatialPatchBox d, 𝔙
𝗇 𝔤 lam * 𝔐
/-- The paper's unary spatial integral bound, before rewriting the
Gaussian normalization as its (1+t)^(-d/2) power. -/
theorem spatial_unary_patch_integral_bound (hd : 𝔢)
    t (ht : 𝔛) x (hx : 𝔔) :
    𝔎 ≤
      𝔗 *
         Real.sqrt (Real.pi / (spatialInterpolationLambda d * 𝔄 / 2)) ^ d := by
  let lam := spatialInterpolationLambda d
  let b := 𝔘
  let A := 𝔗
  have hlam : 𝗸₂ := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hInt := (radial_gaussian_integrable b  𝖠₃  x).const_mul A
  have hbound y (hy : 𝔣) :
      𝔞 ≤ 𝔙 := by
    obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd x y hx hy
    have h := unary_scale_density_gaussian_domination 𝔤 t ha haHalf ht
    have he : 𝔞 = unaryScaleDensity 𝔤 t := by
      unfold spatialUnaryWeight unaryScaleDensity
      ring
    grind
  calc
    𝔟 :=
      setIntegral_mono_on (spatial_unary_patch_integrable lam t x) hInt.integrableOn
        measurableSet_Icc hbound
    _ ≤ ∫ y, 𝔙 :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun y => 𝖠₃ ) hInt
    𝘿 := by rw [integral_const_mul, radial_gaussian_integral]

𝗇 𝔈 𝔨 / 2
𝗇 𝔩 2 * Real.pi / lam
𝗇 𝔉 Real.sqrt 𝔩 ^ d
𝗇 𝔍 -𝔨 / 2
𝗇 𝔥 𝔉 * 𝔄 ^ 𝔍
𝗇 𝔦 -d / 2 = -𝔈
theorem radial_gaussian_scale_normalization (d : ℕ) lam t
    (hlam : 𝗸₂) (ht : 𝔛) :
    𝔭 𝔘 =
      𝔥 := by
  have hs : 0 < 𝔄 := 𝖡₄
  have harg : Real.pi / 𝔘 = 𝔩 / 𝔄 := by
    field_simp
  rw [harg, Real.sqrt_div 𝖠₃ , div_pow]
  have hden : Real.sqrt 𝔄 ^ d = 𝔄 ^ 𝔈 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (𝔄 ^ 𝔇) d,
      ← Real.rpow_mul hs.le]
    ring
  rw [hden, show 𝔦 by ring, Real.rpow_neg hs.le, div_eq_mul_inv]

𝗇 𝔒 Real.sqrt (2 * Real.pi / spatialInterpolationLambda d) ^ d
def spatialUnaryIntegralConstant (d : ℕ) : ℝ :=
  𝔪 * 𝔒

/-- Exact power-form unary spatial decay in Appendix A, proved from
actual Gaussian normalization and exponential-series domination. -/
theorem spatial_unary_patch_integral_decay (hd : 𝔢)
    t (ht : 𝔛) x (hx : 𝔔) :
    𝔎 ≤
      spatialUnaryIntegralConstant d * 𝔄 ^ (𝔍 - 1) := by
  have hlam : 0 < spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  apply (spatial_unary_patch_integral_bound hd t ht x hx).trans_eq
  rw [radial_gaussian_scale_normalization d _ _ hlam ht]
  unfold spatialUnaryIntegralConstant
  rw [Real.rpow_sub 𝖡₄ , Real.rpow_one]
  ring

𝗇 𝔊 𝙡
𝗇 𝔧 𝔄 ^ (1 - 𝔈)
𝗃 𝔯 Real.exp 𝔇 * ἀ
/-- The other unary spatial estimate used in the L² covariance bound. -/
theorem spatial_scale_exponential_patch_integral_decay (hd : 𝔢)
    t (ht : 𝔛) x (hx : 𝔔) :
     ∫ y in spatialPatchBox d,
      t * Real.exp (-(t * spatialInterpolationLambda d * 𝔐)) ≤
      𝔯 𝔒 *
        𝔧 := by
  let lam := spatialInterpolationLambda d
  let b := 𝔘
  let A := 𝔮 𝔇
  have hlam : 𝗸₂ := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hs : 0 < 𝔄 := 𝖡₄
  have hInt := (radial_gaussian_integrable b  𝖠₃  x).const_mul A
  have hActual : IntegrableOn (fun y => 𝔮 𝔊)
      $ spatialPatchBox d := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    unfold spatialSquaredDistance
    fun_prop
  have hBound y (hy : 𝔣) :
      𝔮 𝔊 ≤
      𝔙 := by
    obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd x y hx hy
    have he : 𝔊 ≤
        𝔇 + -b * 𝔐 := by
      dsimp [b]
      nlinarith
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) ht
    rw [Real.exp_add] at h
    linarith
  calc
    𝔟 :=
      setIntegral_mono_on hActual hInt.integrableOn measurableSet_Icc hBound
    _ ≤ ∫ y, 𝔙 :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun y => 𝖠₃ ) hInt
    _ = A * 𝔓 := by rw [integral_const_mul, radial_gaussian_integral]
    _ = A * 𝔥 := by
      rw [radial_gaussian_scale_normalization d lam t hlam ht]
    _ ≤ 𝔯 𝔉 *
        𝔧 := by
      rw [Real.rpow_sub hs, Real.rpow_one]
      have h := mul_le_mul_of_nonneg_right (show t ≤ 𝔄 by linarith)
        (by positivity : 0 ≤ 𝔯 𝔉 /
          𝔄 ^ 𝔈)
      rw [show 𝔦 by ring, Real.rpow_neg hs.le]
      grind
