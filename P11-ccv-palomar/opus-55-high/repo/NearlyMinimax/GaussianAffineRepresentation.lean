module

public import NearlyMinimax.GaussianSeparatedCharacteristic
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual Gaussian affine building block of the cardinal covariance,
including its genuine Gaussian coefficient cost. -/
𝚴
𝚳
𝚨
𝚩
𝚽

𝗇 𝔉 Z a * Z b
def gaussianHermite (a b : Fin d) (Z : Covariate d) : ℝ :=
  (if a = b then 1 else 0) - 𝔉

𝗇 𝔊 𝖾
𝗃 𝔏 Integrable (fun Z => ἀ) $ standardGaussianPi d
theorem standardGaussian_cross_integrable a b :
    𝔏 𝔉 := by
  simpa [gaussianPhase, Complex.mul_re] using (gaussian_cross_complex_characteristic_integrable 𝔊 a b).re

𝗃 𝔐 Z ἀ ^ 2
𝗇 𝔇 𝔐 a
theorem standardGaussian_coordinate_square_integral a :
     ∫ Z : Covariate d, 𝔇 ∂standardGaussianPi d = 1 := by
  have h := standardGaussian_cross_complex_characteristic 𝔊 a a
  simp [gaussianPhase] at h
  have he : (fun Z => (Z a : ℂ) * Z a) =
       fun Z : Covariate d => ((𝔇 : ℝ) : ℂ) := by
    funext Z
    simp [pow_two]
  rw [he, integral_complex_ofReal] at h
  exact_mod_cast h

𝗇 𝔍 gaussianHermite a b
theorem gaussianHermite_integrable a b :
    Integrable 𝔍 $ standardGaussianPi d :=
  (integrable_const _).sub $ standardGaussian_cross_integrable a b

𝗇 𝔄 𝔐 a + 𝔐 b
/-- Genuine uniform Gaussian coefficient cost: the Hermite amplitude has
L1 norm at most two, independently of the spatial scale and observations. -/
theorem standardGaussian_hermite_abs_integral_le_two a b :
     ∫ Z, |𝔍 Z| ∂standardGaussianPi d ≤ 2 := by
  have ha : 𝔏 𝔇 := by
    simpa only [pow_two] using standardGaussian_cross_integrable a a
  have hb : Integrable (fun Z => 𝔐 b) $ standardGaussianPi d := by
    simpa only [pow_two] using standardGaussian_cross_integrable b b
  have hi : Integrable (fun Z => 1 + 𝔄 / 2)
      $ standardGaussianPi d := (integrable_const 1).add $ (ha.add hb).div_const 2
  have hab : 𝔏 𝔄 := ha.add hb
  have hm := integral_mono (gaussianHermite_integrable a b).abs hi fun Z => by
    have hcross : |𝔉| ≤ 𝔄 / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg $ |Z a| - |Z b| , sq_abs $ Z a , sq_abs $ Z b ]
    exact (abs_sub _ _).trans $ add_le_add  𝖥₄  hcross
  rw [integral_add (integrable_const 1) $ hab.div_const 2 , integral_div,
    integral_add ha hb, standardGaussian_coordinate_square_integral,
    standardGaussian_coordinate_square_integral] at hm
  norm_num at hm
  exact hm

𝗇 𝔈 2 * lam * t
def gaussianSpatialFrequency (lam t : ℝ) (x y : Covariate d) : Covariate d :=
  fun l => Real.sqrt 𝔈 * (y l - x l)

theorem gaussianSpatialFrequency_squared lam t (hlam : 𝖺) (ht : 𝘈)
    (x y : Covariate d) :
     ∑ l, gaussianSpatialFrequency lam t x y l ^ 2 =
      𝔈 * 𝖬₁ := by
  unfold gaussianSpatialFrequency spatialSquaredDistance
  simp_rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 𝔈)]
  rw [Finset.mul_sum]

𝗇 𝔎 gaussianPhase w Z
𝗇 𝔅 gaussianHermite a b Z * α * β * Real.cos 𝔎
theorem standardGaussian_hermite_cos_integral_const w
    a b α β :
     ∫ Z, 𝔅
      ∂standardGaussianPi d =
      α * β * (w a * w b) * Real.exp 𝙻₂ := by
  have he : (fun Z => 𝔅) =
       fun Z => α * β * (𝔍 Z * Real.cos 𝔎) := by
    funext Z
    ring
  rw [he, integral_const_mul]
  unfold gaussianHermite
  rw [standardGaussian_hermite_cos_characteristic]
  ring
