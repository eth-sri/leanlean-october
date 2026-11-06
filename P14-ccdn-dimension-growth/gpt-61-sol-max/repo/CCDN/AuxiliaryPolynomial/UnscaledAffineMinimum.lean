/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib.Tactic

public import CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Height.ScaledHypersurfaceHeight

/-! The ordinary homogenization attains the affine box exponent on every
polynomial range in the degree, with both terms of the minimum retained. -/

public section
namespace CCDN
open MvPolynomial

/-- The coefficient height of the leading homogeneous component of an integer polynomial is at most
the coefficient height of the polynomial itself. -/
lemma leading_height_le_coefficient_height {n : ℕ}
    (f : CCDN.IntegerPolynomial n) :
    (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ≤
      (integerCoefficientHeight f : ℝ) := by
  simpa only [Int.cast_one, one_pow, one_mul,
    integerCoefficientHeight_scaledHomogenize_one] using
      scaledHomogenize_leading_height_lower f  le_rfl

/-- Both coefficient-sensitive branches hold for the unscaled model itself.
This estimate preserves their minimum before applying the box estimate. -/
private theorem unscaled_hypersurface_minimum_height_bound {n : ℕ}
    (f : CCDN.IntegerPolynomial (n + 2)) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {B : ℝ} (hB : 1 ≤ B) :
    ↑f.totalDegree ^ (4 - 1 / (n + 1 : ℝ)) *
        hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) /
          (integerCoefficientHeight f : ℝ) ^
            (heightExponent n f.totalDegree) ≤
      max (affineHeightTransferConstant n) (Real.exp 1) *
        ↑f.totalDegree ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) +
          f.totalDegree * Real.log B + ↑f.totalDegree ^ 2)
          (↑f.totalDegree ^ 2 *
            hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) /
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ^
          (heightExponent n f.totalDegree) := by
  let d := f.totalDegree
  let F := scaledHomogenize d 1 f
  let H := (integerCoefficientHeight f : ℝ)
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor F
  let K := max (affineHeightTransferConstant n) (Real.exp 1)
  let T := Real.log L + d * Real.log B + ↑d ^ 2
  let q := heightExponent n d
  have hd0 : (0 : ℝ) < d := by positivity
  have hL := leading_height_one_le f hf
  have hLH := leading_height_le_coefficient_height f
  have hL0 : 0 < L := by linarith
  have hb := hypersurfaceBadPrimeFactor_nonneg F
  have hF0 := scaledHomogenize_ne_zero d one_ne_zero hf
  have hFdegree :=
    (scaledHomogenize_homogeneous 1 f le_rfl).totalDegree hF0
  have hKheight : affineHeightTransferConstant n ≤ K := le_max_left _ _
  have hK1 : 1 ≤ K := by
    aesop
  have hlog : ↑d ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * ↑d ^ (2 - 1 / (n + 1 : ℝ)) * T / L ^ q := by
    have htransfer := hypersurface_badPrime_height_transfer F hFdegree hd hL
      (by simpa only [F, integerCoefficientHeight_scaledHomogenize_one] using hLH)
    have ht : Real.log L + ↑d ^ 2 ≤ T := by
      dsimp only [T]
      have hh := mul_nonneg hd0.le (Real.log_nonneg hB)
      linarith
    calc
      _ ≤ affineHeightTransferConstant n *
          ↑d ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log L + ↑d ^ 2) / L ^ q := by
        simpa only [F, b, H, q, affineHeightTransferConstant,
          integerCoefficientHeight_scaledHomogenize_one] using htransfer
      _ ≤ K * ↑d ^ (2 - 1 / (n + 1 : ℝ)) * T / L ^ q := by
        bound
  have hfactor : ↑d ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * ↑d ^ (2 - 1 / (n + 1 : ℝ)) * (↑d ^ 2 * b) / L ^ q := by
    have hpow : L ^ q ≤ H ^ q :=
      Real.rpow_le_rpow hL0.le hLH (by dsimp [q]; positivity)
    have he :=
      rpow_four_sub_eq_mul_sq hd0 n
    calc
      _ ≤ ↑d ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = ↑d ^ (2 - 1 / (n + 1 : ℝ)) * (↑d ^ 2 * b) / L ^ q := by
        rw [he]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hK1
          (show 0 ≤ ↑d ^ (2 - 1 / (n + 1 : ℝ)) * (↑d ^ 2 * b) / L ^ q by positivity)
        simpa only [one_mul, mul_assoc, mul_div_assoc] using hh
  rcases le_total T (↑d ^ 2 * b) with h | h
  · rw [min_eq_left h]
    exact hlog
  · rw [min_eq_right h]
    exact hfactor

variable {n k : ℕ} (f : CCDN.IntegerPolynomial (n + 2))


/-- An affine auxiliary with the minimum degree bound in the
polynomial box range. The constant coefficient is arbitrary. -/
theorem unscaled_affine_auxiliary_minimum  (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {S B : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * (↑f.totalDegree + 1) ^ k) :
    ∃ g, IsBoxAuxiliary f g B ∧
      ↑g.totalDegree ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (Real.exp (Real.log S + ↑k * (n + 2 : ℝ))) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨g, hg, hgdeg⟩ := unscaled_affine_auxiliary f hprim hir hd hB
  exact ⟨g, hg, hgdeg.trans
    ((by
       let inline_hf := Irreducible.ne_zero hir
       let d := f.totalDegree
       let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
       let H := (integerCoefficientHeight f : ℝ)
       let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
       let K := max (affineHeightTransferConstant n) (Real.exp 1)
       let E := Real.exp (Real.log S + ↑k * (n + 2 : ℝ))
       let T := min (Real.log L + d * Real.log B + ↑d ^ 2) (↑d ^ 2 * b)
       let α := boxExponent n d
       let β := 1 / degreeRoot n d
       let q := heightExponent n d
       have hcoef :=
         unscaled_hypersurface_minimum_height_bound f inline_hf hd hB
       have hpower := by
         have hh := polynomial_box_projective_power_bound (r := n + 1) (by omega) hd hS hB hbound
         simpa only [dimensionRoot, Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using hh
       have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
       have hcoefficient : 0 ≤ ↑d ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q :=
         div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) hb)
           (Real.rpow_nonneg (Nat.cast_nonneg _) _)
       have hmain : ↑d ^ (4 - 1 / (n + 1 : ℝ)) * b * B ^ α / H ^ q ≤
           K * E * ↑d ^ (2 - 1 / (n + 1 : ℝ)) * T * B ^ β / L ^ q := by
         convert mul_le_mul hcoef hpower (Real.rpow_nonneg (by linarith : 0 ≤ B) α)
           (hcoefficient.trans hcoef) using 1 <;> ring
       exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain le_rfl) le_rfl)
         (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le))⟩

end CCDN
