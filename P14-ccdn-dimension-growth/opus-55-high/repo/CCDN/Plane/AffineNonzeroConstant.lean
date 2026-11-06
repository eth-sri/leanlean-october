/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.ScalingPrime
import CCDN.Determinant.HeightDeterminant
import CCDN.Height.CountingHypotheses
import CCDN.Height.PrimitiveIntegerPolynomial
import CCDN.Statements
import CCDN.Plane.AffineBoxRanges
import CCDN.Plane.ScaledBoxExponent
import CCDN.Plane.UnscaledModelCount

/-!
Combining the scaling-prime, large-coefficient and small-box branches.
The plane theorem assumes the sharp finite-field count and a nonzero
constant term; a later translation removes the second hypothesis.

The affine exponent 1/d with the scaling prime constructed from Mertens.
This branch assumes a nonzero constant coefficient of small logarithmic height;
the sharp finite-field count is an explicit geometric hypothesis.
-/

namespace CCDN
noncomputable section
open MvPolynomial Real

/-- The threshold constant `(12 * scalingPrimeRatio) ^ 2` separating small boxes
`B ≤ affineSmallBoxScale * d ^ 2` from large boxes in the affine plane count. -/
def affineSmallBoxScale : ℝ := (12 * scalingPrimeRatio) ^ 2

lemma affineSmallBoxScale_one_le : 1 ≤ affineSmallBoxScale := by
  have h := scalingPrimeRatio_one_le
  unfold affineSmallBoxScale
  nlinarith

section
variable (C : ℝ)

/-- The constant of `plane_finite_count_nonzero_constant` for residue constant `C`, the sum of
the constants of its regimes, with `E = heightDeterminantError C`: the scaled small-coefficient
regime (`plane_finite_count_small_constant_coefficient`) costs
`38 + 8 exp (E + 20) + 2 exp (E + 23) e¹⁴ e² · scalingPrimeRatio`, and the small-box regime
(`small_box_unscaled_degree_bound`) costs `log S + 6 + 2 exp (E + 23) e¹⁴ exp (2 log S + 6)`
with `S = affineSmallBoxScale`. The large-coefficient constant `34 + 8 exp (E + 20)` is
dominated by the first. The numerical constants are explained in
`projectivePlaneAbsoluteConstant`. -/
def affineNonzeroConstantBound : ℝ :=
  (38 + 8 * Real.exp (heightDeterminantError C + 20) +
    2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * scalingPrimeRatio) +
  (Real.log affineSmallBoxScale + 6 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 *
    Real.exp (2 * Real.log affineSmallBoxScale + 6))

/-- The constant `affineNonzeroConstantBound C` is positive. -/
lemma affineNonzeroConstantBound_pos : 0 < affineNonzeroConstantBound C := by
  have hA := zero_lt_one.trans_le scalingPrimeRatio_one_le
  have hS := Real.log_nonneg affineSmallBoxScale_one_le
  unfold affineNonzeroConstantBound
  positivity

end

/-- For `d ≥ 1` and `B ≥ 1`, the curve bound `curveBound d B` is at least `d ^ 4`. -/
lemma degree_four_le_curveBound {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    (d : ℝ) ^ 4 ≤ curveBound d B := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hlog := Real.log_nonneg hB
  have hp : 1 ≤ B ^ (1 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hh : (d : ℝ) ≤ B ^ (1 / (d : ℝ)) * (Real.log B + d) := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hh (pow_nonneg hd0.le 3)
  unfold curveBound
  nlinarith

/-- Coefficient-uniform affine plane count for nonzero constant term and every
B>=1. -/
theorem plane_finite_count_nonzero_constant
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) (hf0 : f.coeff 0 ≠ 0)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z) {B C : ℝ} (hzB : IsBoxZeroFamily f B z)
    (hC : 0 ≤ C) (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤ affineNonzeroConstantBound C * curveBound f.totalDegree B := by
  obtain ⟨hB, hz, hbox⟩ := hzB
  let d := f.totalDegree
  let K₁ := 38 + 8 * Real.exp (heightDeterminantError C + 20) +
    2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 * scalingPrimeRatio
  let K₂ := Real.log affineSmallBoxScale + 6 +
    2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 *
      Real.exp (2 * Real.log affineSmallBoxScale + 6)
  let K₃ := 34 + 8 * Real.exp (heightDeterminantError C + 20)
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by
    have := Real.log_nonneg affineSmallBoxScale_one_le
    positivity
  have hK₃ : 0 ≤ K₃ := by positivity
  have h31 : K₃ ≤ K₁ := by
    have hh : 0 ≤ 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 *
        scalingPrimeRatio := by positivity
    grind
  have hpow := degree_four_le_curveBound hd hB
  have hG := (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4).trans hpow
  have hsum : affineNonzeroConstantBound C = K₁ + K₂ := rfl
  rw [hsum]
  have hone := scaled_plane_finite_count f hir hd le_rfl z ⟨hB, hz, hbox⟩ (by simpa using hB) hC
    (fun M a g hg => unscaled_positioned_points_card_le f hprim
      (rational_irreducible_of_charZero_map f hir) a z hinj hz g hg) hcount
  by_cases hsmallB : B ≤ affineSmallBoxScale * (d : ℝ) ^ 2
  · have hh := hone.1
    simp only [Nat.cast_one] at hh
    have hs := small_box_unscaled_degree_bound hd affineSmallBoxScale_one_le hB hsmallB (C := C)
    apply hh.trans
    apply max_le
    · nlinarith
    nlinarith
  · have hlargeB : (12 * scalingPrimeRatio) ^ 2 * (d : ℝ) ^ 2 ≤ B := (lt_of_not_ge hsmallB).le
    by_cases hsmallH : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio
    · have hBA : scalingPrimeRatio ≤ B := by
        have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        nlinarith
      obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hBA hf0 hsmallH
      have hBp : B ≤ scalingPrimeRatio * p := by
        have h := (div_lt_iff₀ hA0).mp hlo
        nlinarith
      let Q := B ^ (1 / (d : ℝ))
      let U := Real.log B + d
      let K₄ := 4 + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * Real.exp 2 *
        scalingPrimeRatio
      have hdR : (0 : ℝ) < d := mod_cast hd
      have hlog := Real.log_nonneg hB
      have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
      have hU : (d : ℝ) ≤ U := by grind
      have hK₄ : 0 ≤ K₄ := by positivity
      have hrest : (0 : ℝ) ≤ d ^ 3 * Q * U := by positivity
      have hlarge : K₃ * d ^ 4 ≤ K₃ * (d ^ 3 * Q * U) := by
        apply mul_le_mul_of_nonneg_left _ hK₃
        have hh : d ≤ Q * U := by nlinarith
        nlinarith
      have hsmall := scaled_auxiliary_degree_bound_le hd hA hB
        (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le) hhi hBp (C := C)
      have hcount' := (scaled_plane_finite_count f hir hd hp.one_lt.le z ⟨hB, hz, hbox⟩ hhi hC
        (fun M a g hg => scaled_positioned_points_card_le f hprim
          (rational_irreducible_of_charZero_map f hir) hp hnd a z hinj hz g hg) hcount).1
      have hb : t ≤ (K₄ + K₃) * (d ^ 3 * Q * U) := by
        apply hcount'.trans
        apply max_le
        · nlinarith
        nlinarith
      have ht : t ≤ K₁ * curveBound d B := by
        convert hb using 1
        simp only [K₁, K₃, K₄, Q, U, curveBound, d]
        ring
      exact ht.trans (mul_le_mul_of_nonneg_right (by linarith) hG)
    · have hheight := (large_box_height_threshold hd hA hlargeB).trans (le_of_not_gt hsmallH)
      have hh := hone.2 0 hf0 hheight
      nlinarith

