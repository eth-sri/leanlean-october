module

public import NearlyMinimax.GaussianSeparatedCharacteristic

@[expose] public section

/-! The actual Gaussian affine building block of the cardinal covariance,
including its genuine Gaussian coefficient cost. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def gaussianHermite {d : ℕ} (a b : Fin d) (Z : Covariate d) : ℝ :=
  (if a = b then 1 else 0) - Z a * Z b

theorem standardGaussian_cross_integrable {d : ℕ} (a b : Fin d) :
    Integrable (fun Z : Covariate d => Z a * Z b) (standardGaussianPi d) := by
  have h := (gaussian_cross_complex_characteristic_integrable (fun _ => 0) a b).re
  simpa [gaussianPhase, Complex.mul_re] using h

theorem standardGaussian_coordinate_square_integral {d : ℕ} (a : Fin d) :
    (∫ Z : Covariate d, (Z a) ^ 2 ∂standardGaussianPi d) = 1 := by
  have h := standardGaussian_cross_complex_characteristic (fun _ => 0) a a
  simp [gaussianPhase] at h
  have he : (fun Z : Covariate d => (Z a : ℂ) * Z a) =
      (fun Z : Covariate d => (((Z a) ^ 2 : ℝ) : ℂ)) := by
    funext Z
    simp [pow_two]
  rw [he, integral_complex_ofReal] at h
  exact_mod_cast h

theorem gaussianHermite_integrable {d : ℕ} (a b : Fin d) :
    Integrable (gaussianHermite a b) (standardGaussianPi d) :=
  (integrable_const _).sub (standardGaussian_cross_integrable a b)

/-- Genuine uniform Gaussian coefficient cost: the Hermite amplitude has
L1 norm at most two, independently of the spatial scale and observations. -/
theorem standardGaussian_hermite_abs_integral_le_two {d : ℕ} (a b : Fin d) :
    (∫ Z, |gaussianHermite a b Z| ∂standardGaussianPi d) ≤ 2 := by
  have ha : Integrable (fun Z : Covariate d => (Z a) ^ 2) (standardGaussianPi d) := by
    simpa only [pow_two] using standardGaussian_cross_integrable a a
  have hb : Integrable (fun Z : Covariate d => (Z b) ^ 2) (standardGaussianPi d) := by
    simpa only [pow_two] using standardGaussian_cross_integrable b b
  have hi : Integrable (fun Z : Covariate d => 1 + ((Z a) ^ 2 + (Z b) ^ 2) / 2)
      (standardGaussianPi d) := (integrable_const 1).add ((ha.add hb).div_const 2)
  have hab : Integrable (fun Z : Covariate d => (Z a) ^ 2 + (Z b) ^ 2)
      (standardGaussianPi d) := ha.add hb
  have hdiv : Integrable (fun Z : Covariate d => ((Z a) ^ 2 + (Z b) ^ 2) / 2)
      (standardGaussianPi d) := hab.div_const 2
  have hm := integral_mono (gaussianHermite_integrable a b).abs hi (fun Z => by
    have hcross : |Z a * Z b| ≤ ((Z a) ^ 2 + (Z b) ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|Z a| - |Z b|), sq_abs (Z a), sq_abs (Z b)]
    have hδ : |(if a = b then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    exact (abs_sub _ _).trans (add_le_add hδ hcross))
  rw [integral_add (integrable_const 1) hdiv, integral_div,
    integral_add ha hb, standardGaussian_coordinate_square_integral,
    standardGaussian_coordinate_square_integral] at hm
  norm_num at hm
  exact hm

def gaussianSpatialFrequency {d : ℕ} (lam t : ℝ) (x y : Covariate d) : Covariate d :=
  fun l => Real.sqrt (2 * lam * t) * (y l - x l)

theorem gaussianSpatialFrequency_squared {d : ℕ} (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) :
    (∑ l, (gaussianSpatialFrequency lam t x y l) ^ 2) =
      2 * lam * t * spatialSquaredDistance x y := by
  unfold gaussianSpatialFrequency spatialSquaredDistance
  simp_rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)]
  rw [Finset.mul_sum]

theorem standardGaussian_hermite_cos_integral_const {d : ℕ} (w : Covariate d)
    (a b : Fin d) (α β : ℝ) :
    (∫ Z, gaussianHermite a b Z * α * β * Real.cos (gaussianPhase w Z)
      ∂standardGaussianPi d) =
      α * β * (w a * w b) * Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
  have he : (fun Z => gaussianHermite a b Z * α * β * Real.cos (gaussianPhase w Z)) =
      (fun Z => α * β * (gaussianHermite a b Z * Real.cos (gaussianPhase w Z))) := by
    funext Z
    ring
  rw [he, integral_const_mul]
  unfold gaussianHermite
  rw [standardGaussian_hermite_cos_characteristic]
  ring

end NearlyMinimax
