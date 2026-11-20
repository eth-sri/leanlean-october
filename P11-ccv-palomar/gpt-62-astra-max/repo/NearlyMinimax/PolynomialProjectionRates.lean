module

public import NearlyMinimax.PolynomialGridProjection
public import NearlyMinimax.ProjectionStatistical


@[expose] public section

open scoped ENNReal
noncomputable section
namespace NearlyMinimax

section
variable {d : ℕ} (C : ModelConstants d)

/-- Number of rectangular monomial features per grid cell. -/
def polynomialFeatureCount : ℕ := (C.order + 1) ^ d

theorem polynomialFeatureCount_pos :
    0 < polynomialFeatureCount C := by
  unfold polynomialFeatureCount
  positivity

/-- The actual root-floor grid uses half the sample as its feature budget. -/
def polynomialProjectionGridSize (n : ℕ) : ℕ :=
  ⌊((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)⌋₊

end

variable {d n : ℕ} {C : ModelConstants d} (hn : 2 * polynomialFeatureCount C ≤ n)

include hn in
theorem polynomial_projection_grid_size_spec :
    0 < polynomialProjectionGridSize C n ∧
    (polynomialProjectionGridSize C n) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2 ∧
    ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹) ≤
      2 * polynomialProjectionGridSize C n := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast C.dimension_pos
  have hqreal : 0 < polynomialFeatureCount C := by exact_mod_cast polynomialFeatureCount_pos C
  have hnreal : 2 * (polynomialFeatureCount C : ℝ) ≤ n := by exact_mod_cast hn
  let r := ((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)
  have hk : 0 < polynomialProjectionGridSize C n := Nat.floor_pos.mpr (Real.one_le_rpow (by
    apply (le_div_iff₀ (by positivity)).mpr
    bound) (inv_nonneg.mpr hdreal.le))
  have hkle : (polynomialProjectionGridSize C n) ≤ r := Nat.floor_le (by positivity)
  have hbudget := (pow_le_pow_left₀ (Nat.cast_nonneg _) hkle d).trans_eq (Real.rpow_inv_natCast_pow (by positivity) C.dimension_pos.ne')
  have hbudget' := (le_div_iff₀ (by positivity)).mp hbudget
  have hfeature : ((C.order + 1 : ℕ) : ℝ) ^ d = polynomialFeatureCount C := by
    simp [polynomialFeatureCount]
  have hcolumns : (polynomialProjectionGridSize C n) ^ d * (C.order + 1 : ℕ) ^ d ≤ (n : ℝ) / 2 := by
    rw [hfeature]
    nlinarith
  have hfloor : r < (polynomialProjectionGridSize C n) + 1 := Nat.lt_floor_add_one r
  have hk1 : (1 : ℝ) ≤ polynomialProjectionGridSize C n := by exact_mod_cast hk
  grind

include hn in
/-- Floor rounding changes inverse cell width by a fixed model factor. -/
theorem polynomial_projection_grid_inverse_width_bound :
    1 / (polynomialProjectionGridSize C n) ≤
      (2 * (2 * polynomialFeatureCount C) ^ ((d : ℝ)⁻¹)) *
        (n : ℝ) ^ (-((d : ℝ)⁻¹)) := by
  have hqreal : 0 < polynomialFeatureCount C := by exact_mod_cast polynomialFeatureCount_pos C
  have hnreal : (0 : ℝ) < n := by
    bound [polynomialFeatureCount_pos C]
  have hspec := polynomial_projection_grid_size_spec hn
  have hi : 1 / (polynomialProjectionGridSize C n) ≤
      2 / (((n : ℝ) / (2 * polynomialFeatureCount C)) ^ ((d : ℝ)⁻¹)) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hspec.1) (by positivity)).mpr
    linarith
  apply hi.trans_eq
  rw [Real.div_rpow hnreal.le (by positivity), Real.rpow_neg hnreal.le]
  field_simp

/-- Explicit full-smoothness approximation constant, independent of sample size. -/
def polynomialProjectionApproximationConstant (C : ModelConstants d) : ℝ :=
  4 * (taylorErrorFactor C * C.holderBound *
    (2 * (2 * polynomialFeatureCount C) ^ ((d : ℝ)⁻¹)) ^ C.smoothness) ^ 4

include hn in
/-- The constructed full-order projection bias has rate `n^(-4s/d)`. -/
theorem polynomial_projection_grid_bias_rate :
    polynomialGridBias C (polynomialProjectionGridSize C n) ≤
      polynomialProjectionApproximationConstant C * n ^ (-(4 * C.smoothness / d)) := by
  have hnreal : (0 : ℝ) < n := by
    bound [polynomialFeatureCount_pos C]
  have hcoef  :=
    mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le
  have hpow := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (polynomial_projection_grid_inverse_width_bound hn) C.smoothness_pos.le) hcoef) 4
  unfold polynomialGridBias polynomialProjectionApproximationConstant
  apply (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have hpower : ((n ^ (-((d : ℝ)⁻¹))) ^ C.smoothness) ^ 4 =
      (n : ℝ) ^ (-(4 * C.smoothness / d)) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hnreal.le]
    ring
  grind

end NearlyMinimax
