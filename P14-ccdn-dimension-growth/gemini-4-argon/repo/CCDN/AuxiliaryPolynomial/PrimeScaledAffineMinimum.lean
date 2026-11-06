/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.PrimeScaledAffineHeight
public import CCDN.AuxiliaryPolynomial.ScalingPrime
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.PrimeScaledAffineAuxiliary
import CCDN.AuxiliaryPolynomial.PrimeScaledAffineHeight
import CCDN.AuxiliaryPolynomial.ScaledHypersurfaceBadPrimes
import CCDN.Height.ScaledHypersurfaceHeight

/-! Both bounds for the bad-prime factor apply to the same homogeneous
auxiliary. Their minimum therefore survives the affine exponent saving. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine auxiliary degree bound in which the coefficient-sensitive main term involves the
minimum of `log L + d log B + d²` and `d² b`, where `L` is the height of the leading form and
`b` a bad-prime factor, with box exponent `1 / d^(1/(n+1))` up to the factor `A`. -/
def affineMinimumAuxiliaryBound (n d : ℕ) (A B L b : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n *
    (max (affineHeightTransferConstant n) (Real.exp 1) * A *
        (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
          L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)))

/-- If the constant coefficient `c` of a primitive irreducible integer polynomial `f` is nonzero
and `log |c| < B / scalingPrimeRatio`, with `B ≥ scalingPrimeRatio`, then `f` has a box
auxiliary polynomial of degree at most `affineMinimumAuxiliaryBound`, with ratio
`scalingPrimeRatio` and the bad-prime factor of the homogenization of `f`. -/
theorem affine_auxiliary_minimum_of_small_constant_coefficient {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    (hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree scalingPrimeRatio B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨p, hp, hlo, hpB, hp0⟩ := exists_scaling_prime hB hc hheight
  have hA := scalingPrimeRatio_one_le
  have hB1 : 1 ≤ B := hA.trans hB
  have hBp : B / scalingPrimeRatio ≤ p := hlo.le
  have hf := hir.ne_zero
  obtain ⟨g, hg, hgdegree⟩ := prime_scaled_affine_auxiliary f hprim hir hd hp hp0 hB1 hpB
  refine ⟨g, hg, hgdegree.trans ?_⟩
  let A := scalingPrimeRatio
  let d := f.totalDegree
  let F := scaledHomogenize d (p : ℤ) f
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let H := (integerCoefficientHeight F : ℝ)
  let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
  let c := hypersurfaceBadPrimeFactor F
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hT : 0 ≤ T := add_nonneg
    (add_nonneg (Real.log_nonneg hL) (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB1)))
    (sq_nonneg _)
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
  have hc0 : 0 ≤ c := hypersurfaceBadPrimeFactor_nonneg _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  by_cases hmin : T ≤ (d : ℝ) ^ 2 * b
  · refine (scaled_hypersurface_auxiliary_bound f hf hd
      (by exact_mod_cast hp.one_lt.le : (1 : ℤ) ≤ p) hA hB1
      (by simpa only [Int.cast_natCast] using hpB)
      (by simpa only [Int.cast_natCast] using hBp)).trans ?_
    change affineLogarithmicAuxiliaryBound n d A B L ≤ affineMinimumAuxiliaryBound n d A B L b
    unfold affineLogarithmicAuxiliaryBound affineMinimumAuxiliaryBound
    rw [min_eq_left hmin]
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0) (by positivity)) hT)
          (by positivity)) (by positivity)) le_rfl) le_rfl)
      (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  · let Y := (p : ℝ) ^ d * L
    let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
    let β := 1 / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
    let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
    have hd0 : (0 : ℝ) < d := mod_cast hd
    have hp0R : (0 : ℝ) < p := mod_cast hp.pos
    have hL0 : 0 < L := by linarith
    have hY0 : 0 < Y := mul_pos (pow_pos hp0R _) hL0
    have hYH : Y ≤ H := by
      simpa only [Int.cast_natCast] using
        scaledHomogenize_leading_height_lower f (by exact_mod_cast hp.one_lt.le : (1 : ℤ) ≤ p)
    have hYpow : Y ^ q = (p : ℝ) ^ β * L ^ q := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        scaled_height_rpow (r := n + 1) (by omega) hd hp0R hL0
    have hdenom : Y ^ q ≤ H ^ q := Real.rpow_le_rpow hY0.le hYH (by dsimp [q]; positivity)
    have hpower : B ^ α / (p : ℝ) ^ β ≤ A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
      simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
        affine_scaling_box_power (r := n + 1) (by omega) hd hB1 hA hp0R hBp
    have hbad := hypersurfaceBadPrimeFactor_scaledHomogenize_le f hf hp
    have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / H ^ q ≤
        Real.exp 1 * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) *
          B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) / L ^ q := calc
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / Y ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * (Real.exp 1 * b) * B ^ α / Y ^ q :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hbad (by positivity)) (by positivity)) (by positivity)
      _ = (Real.exp 1 * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) * (B ^ α / (p : ℝ) ^ β) := by
        rw [hYpow]; ring
      _ ≤ (Real.exp 1 * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) *
          (A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by rw [rpow_four_sub_eq_mul_sq hd0 n]; ring
    change hypersurfaceAuxiliaryDegreeBound n d B c H ≤ affineMinimumAuxiliaryBound n d A B L b
    unfold hypersurfaceAuxiliaryDegreeBound affineMinimumAuxiliaryBound
    rw [min_eq_right (le_of_not_ge hmin)]
    refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hmain.trans ?_) le_rfl) le_rfl)
      (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0) (by positivity)) (by positivity))
        (by positivity)) (by positivity)

end
end CCDN
