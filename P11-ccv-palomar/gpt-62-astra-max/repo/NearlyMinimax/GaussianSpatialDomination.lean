module

public import NearlyMinimax.CardinalScaleWeights


@[expose] public section

/-! Actual Gaussian spatial domination for the cardinal scale kernels. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

section
variable {d : ℕ} (b : ℝ) (x : Covariate d)

theorem radial_gaussian_integrable {b : ℝ} (hb : 0 < b) (x : Covariate d) :
    Integrable (fun y => Real.exp (-b * spatialSquaredDistance x y)) volume := by
  simp_rw [spatialSquaredDistance, Finset.mul_sum, Real.exp_sum]
  exact Integrable.fintype_prod
    (fun r => (integrable_exp_neg_mul_sq hb).comp_sub_right (x r))

/-- Exact finite-dimensional Gaussian normalization, including arbitrary
spatial center. -/
theorem radial_gaussian_integral :
    (∫ y, Real.exp (-b * spatialSquaredDistance x y)) = (Real.sqrt (Real.pi / b)) ^ d := by
  simp_rw [spatialSquaredDistance, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_volume_eq_prod
    (fun r y => Real.exp (-b * (y - x r) ^ 2))]
  simp_rw [integral_sub_right_eq_self (fun y => Real.exp (-b * y ^ 2)), integral_gaussian]
  simp

end

/-- A second-order exponential-series term absorbs the squared radial
factor at every nonnegative argument. -/
theorem quadratic_exp_absorption {z : ℝ} (hz : 0 ≤ z) :
    z ^ 2 * Real.exp (-2 * z) ≤ 2 * Real.exp (-z) := by
  have h := Real.pow_div_factorial_le_exp z hz 2
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-2 * z))
  rw [← Real.exp_add, show z + -2 * z = -z by ring] at hmul
  linarith

/-- The actual unary scale density has the spatial decay factor
(1+t)^-1 before Gaussian integration. -/
theorem unary_scale_density_gaussian_domination {alpha t : ℝ}
    (ha : 0 ≤ alpha) (haHalf : alpha ≤ 1 / 2) (ht : 0 ≤ t) :
    unaryScaleDensity alpha t ≤
      (8 * Real.exp (1 / 2) / (1 + t)) * Real.exp (-((1 + t) * alpha / 2)) := by
  have hs : 0 < 1 + t := by linarith
  let z := (1 + t) * alpha / 2
  have hz : 0 ≤ z := by positivity
  have hAbs := quadratic_exp_absorption hz
  let expScale := Real.exp (-((1 + t) * alpha))
  have he : Real.exp (-(alpha * t)) = Real.exp alpha * expScale := by
    rw [← Real.exp_add]
    ring
  have hez : -2 * z = -((1 + t) * alpha) := by ring
  rw [hez] at hAbs
  have hscaled := mul_le_mul_of_nonneg_left hAbs (by positivity : 0 ≤ 4 / (1 + t) ^ 2)
  let ratio := 8 / (1 + t) ^ 2 * Real.exp (-z)
  have hmain : alpha ^ 2 * expScale ≤
      ratio := by
    have hleft : 4 / (1 + t) ^ 2 * (z ^ 2 * expScale) =
        alpha ^ 2 * expScale := by
      dsimp [z]
      field_simp
      ring
    rw [hleft] at hscaled
    apply hscaled.trans_eq
    ring
  unfold unaryScaleDensity
  rw [he]
  calc
    _ = t * Real.exp alpha * (alpha ^ 2 * expScale) := by ring
    _ ≤ t * Real.exp (1 / 2) * (ratio) :=
      by bound
    _ ≤ _ := by
      have hratio : t / (1 + t) ^ 2 ≤ 1 / (1 + t) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hs) hs).mpr
        nlinarith
      grind [mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 8 * Real.exp (1 / 2) * Real.exp (-z))]
    _ = _ := rfl

def spatialPatchBox (d : ℕ) : Set (Covariate d) := Icc (fun _ => -1) (fun _ => 1)

def spatialInterpolationLambda (d : ℕ) : ℝ := 1 / (8 * d)

section
variable {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {x : Covariate d} (hx : x ∈ spatialPatchBox d)

include hd in
theorem spatial_patch_alpha_bounds {y : Covariate d}
    (hx : x ∈ spatialPatchBox d) (hy : y ∈ spatialPatchBox d) :
    0 ≤ spatialInterpolationLambda d * spatialSquaredDistance x y ∧
      spatialInterpolationLambda d * spatialSquaredDistance x y ≤ 1 / 2 := by
  have hdist : 0 ≤ spatialSquaredDistance x y := Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have hdistUpper : spatialSquaredDistance x y ≤ 4 * d := by
    calc
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro r _
        have hxr : |x r| ≤ 1 := abs_le.mpr ⟨hx.1 r, hx.2 r⟩
        have hyr : |y r| ≤ 1 := abs_le.mpr ⟨hy.1 r, hy.2 r⟩
        have hsub : |y r - x r| ≤ 2 := (abs_sub _ _).trans (by linarith)
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hsub 2
        simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq
      _ = _ := by simp [mul_comm]
  constructor
  · unfold spatialInterpolationLambda
    positivity
  · unfold spatialInterpolationLambda
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith

include hd ht hx in
/-- The paper's unary spatial integral bound, before rewriting the
Gaussian normalization as its (1+t)^(-d/2) power. -/
theorem spatial_unary_patch_integral_bound :
    (∫ y in spatialPatchBox d, spatialUnaryWeight (spatialInterpolationLambda d) t x y) ≤
      (8 * Real.exp (1 / 2) / (1 + t)) *
        (Real.sqrt (Real.pi / (spatialInterpolationLambda d * (1 + t) / 2))) ^ d := by
  let lam := spatialInterpolationLambda d
  let b := lam * (1 + t) / 2
  let A := 8 * Real.exp (1 / 2) / (1 + t)
  have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hb : 0 < b := by positivity
  have hInt := (radial_gaussian_integrable hb x).const_mul A
  have hbound y (hy : y ∈ spatialPatchBox d) :
      spatialUnaryWeight lam t x y ≤ A * Real.exp (-b * spatialSquaredDistance x y) := by
    obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd hx hy
    have h := unary_scale_density_gaussian_domination ha haHalf ht
    grind [spatialUnaryWeight, unaryScaleDensity]
  calc
    _ ≤ _ :=
      setIntegral_mono_on (by apply ContinuousOn.integrableOn_compact isCompact_Icc; unfold spatialUnaryWeight spatialSquaredDistance; fun_prop) hInt.integrableOn
        measurableSet_Icc hbound
    _ ≤ _ :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun y => by positivity)) hInt
    _ = _ := by rw [integral_const_mul, radial_gaussian_integral]

theorem radial_gaussian_scale_normalization (d : ℕ) {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t) :
    (Real.sqrt (Real.pi / (lam * (1 + t) / 2))) ^ d =
      (Real.sqrt (2 * Real.pi / lam)) ^ d * (1 + t) ^ (-(d : ℝ) / 2) := by
  have hs : 0 < 1 + t := by linarith
  have harg : Real.pi / (lam * (1 + t) / 2) = (2 * Real.pi / lam) / (1 + t) := by
    field_simp
  rw [harg, Real.sqrt_div (by positivity), div_pow]
  have hden : (Real.sqrt (1 + t)) ^ d = (1 + t) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + t) ^ (1 / 2)) d,
      ← Real.rpow_mul hs.le]
    ring
  rw [hden, show -d / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le, div_eq_mul_inv]

def spatialUnaryIntegralConstant (d : ℕ) : ℝ :=
  8 * Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d

include hd in
/-- Exact power-form unary spatial decay in Appendix A, proved from
actual Gaussian normalization and exponential-series domination. -/
theorem spatial_unary_patch_integral_decay
    (t : ℝ) (ht : 0 ≤ t) (x : Covariate d) (hx : x ∈ spatialPatchBox d) :
    (∫ y in spatialPatchBox d, spatialUnaryWeight (spatialInterpolationLambda d) t x y) ≤
      spatialUnaryIntegralConstant d * (1 + t) ^ (-(d : ℝ) / 2 - 1) := by
  apply (spatial_unary_patch_integral_bound hd ht hx).trans_eq
  rw [radial_gaussian_scale_normalization d (by unfold spatialInterpolationLambda; positivity) ht]
  unfold spatialUnaryIntegralConstant
  rw [Real.rpow_sub (by linarith), Real.rpow_one]
  ring

include hd ht hx in
/-- The other unary spatial estimate used in the L² covariance bound. -/
theorem spatial_scale_exponential_patch_integral_decay :
    (∫ y in spatialPatchBox d,
      t * Real.exp (-(t * spatialInterpolationLambda d * spatialSquaredDistance x y))) ≤
      (Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / spatialInterpolationLambda d)) ^ d) *
        (1 + t) ^ (1 - (d : ℝ) / 2) := by
  let lam := spatialInterpolationLambda d
  let b := lam * (1 + t) / 2
  let A := t * Real.exp (1 / 2)
  have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hs : 0 < 1 + t := by linarith
  have hb : 0 < b := by positivity
  have hInt := (radial_gaussian_integrable hb x).const_mul A
  have hBound y (hy : y ∈ spatialPatchBox d) :
      t * Real.exp (-(t * lam * spatialSquaredDistance x y)) ≤
      A * Real.exp (-b * spatialSquaredDistance x y) := by
    obtain ⟨ha, haHalf⟩ := spatial_patch_alpha_bounds hd hx hy
    have he : -(t * lam * spatialSquaredDistance x y) ≤
        1 / 2 + -b * spatialSquaredDistance x y := by
      dsimp [b]
      nlinarith
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) ht
    rw [Real.exp_add] at h
    linarith
  calc
    _ ≤ _ :=
      setIntegral_mono_on (by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        unfold spatialSquaredDistance
        fun_prop) hInt.integrableOn measurableSet_Icc hBound
    _ ≤ _ :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun y => by positivity)) hInt
    _ = _ := by rw [integral_const_mul, radial_gaussian_integral]
    _ = _ := by
      rw [radial_gaussian_scale_normalization d hlam ht]
    _ ≤ _ := by
      rw [Real.rpow_sub hs, Real.rpow_one]
      have h := mul_le_mul_of_nonneg_right (show t ≤ 1 + t by linarith)
        (by positivity : 0 ≤ Real.exp (1 / 2) * (Real.sqrt (2 * Real.pi / lam)) ^ d /
          (1 + t) ^ ((d : ℝ) / 2))
      rw [show -d / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hs.le]
      convert h using 1 <;> ring

end

end NearlyMinimax
