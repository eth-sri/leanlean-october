/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Height.ScaledHypersurfaceHeight

/-! The ordinary homogenization attains the affine box exponent on every
polynomial range in the degree, with both terms of the minimum retained. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/- The coefficient height of the leading homogeneous component of an integer polynomial is at most
the coefficient height of the polynomial itself. -/

/-- An affine auxiliary with the minimum degree bound in the
polynomial box range. The constant coefficient is arbitrary. -/
theorem unscaled_affine_auxiliary_minimum {n k : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {S B : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B)
    (hbound : B ≤ S * ((f.totalDegree : ℝ) + 1) ^ k) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨g, hg, hgdeg⟩ := unscaled_affine_auxiliary f hprim hir hd hB
  refine ⟨g, hg, hgdeg.trans ?_⟩
  have hf := hir.ne_zero
  let d := f.totalDegree
  let F := scaledHomogenize d 1 f
  let b := hypersurfaceBadPrimeFactor F
  let H := (integerCoefficientHeight f : ℝ)
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let K := max (affineHeightTransferConstant n) (Real.exp 1)
  let E := Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ))
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  let M_min := min T ((d : ℝ) ^ 2 * b)
  let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let β := 1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hLH : L ≤ H := by
    simpa only [Int.cast_one, one_pow, one_mul, integerCoefficientHeight_scaledHomogenize_one] using
      scaledHomogenize_leading_height_lower f (h := 1) le_rfl
  have hL0 : 0 < L := by linarith
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg F
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero d one_ne_zero hf
  have hK1 : 1 ≤ K := (Real.one_le_exp (by norm_num)).trans (le_max_right _ _)
  have hlog : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * T / L ^ q := by
    have htransfer := hypersurface_badPrime_height_transfer F hF0
      ((scaledHomogenize_homogeneous (1 : ℤ) f le_rfl).totalDegree hF0) hd hL
      (by simpa only [F, integerCoefficientHeight_scaledHomogenize_one] using hLH)
    have ht : Real.log L + (d : ℝ) ^ 2 ≤ T := by
      dsimp only [T]; linarith [mul_nonneg hd0.le (Real.log_nonneg hB)]
    have hheight0 : 0 ≤ affineHeightTransferConstant n := by
      unfold affineHeightTransferConstant
      exact mul_nonneg (by positivity) (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
    exact (by simpa only [F, b, H, q, affineHeightTransferConstant,
      integerCoefficientHeight_scaledHomogenize_one] using htransfer :
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
          affineHeightTransferConstant n * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
            (Real.log L + (d : ℝ) ^ 2) / L ^ q).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          ht (by positivity) (by positivity)) (by positivity))
  have hfactor : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / L ^ q := by
    calc (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (Real.rpow_le_rpow hL0.le hLH (by dsimp [q]; positivity))
      _ = (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / L ^ q := by
        rw [rpow_four_sub_eq_mul_sq hd0 n]; ring
      _ ≤ _ := by
        simpa only [one_mul, mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_right hK1
          (show 0 ≤ (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / L ^ q by positivity)
  have hcoef : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * M_min / L ^ q := by
    dsimp only [M_min]
    rcases le_total T ((d : ℝ) ^ 2 * b) with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hpower : B ^ α ≤ E * B ^ β := by
    simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
      polynomial_box_projective_power_bound (r := n + 1) (by omega) hd hS hB hbound
  have hcoefficient : 0 ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / H ^ q := by positivity
  have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b * B ^ α / H ^ q ≤
      K * E * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * M_min * B ^ β / L ^ q := by
    convert mul_le_mul hcoef hpower (Real.rpow_nonneg (by linarith : 0 ≤ B) α)
      (hcoefficient.trans hcoef) using 1 <;> ring
  unfold hypersurfaceAuxiliaryDegreeBound affineMinimumAuxiliaryBound
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain le_rfl) le_rfl)
    (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le

end
end CCDN
