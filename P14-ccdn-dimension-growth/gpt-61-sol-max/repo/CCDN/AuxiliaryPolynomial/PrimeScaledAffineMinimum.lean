/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

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
open MvPolynomial

/-- The affine auxiliary degree bound in which the coefficient-sensitive main term involves the
minimum of `log L + d log B + d²` and `d² b`, where `L` is the height of the leading form and
`b` a bad-prime factor, with box exponent `1 / d^(1/(n+1))` up to the factor `A`. -/
noncomputable def affineMinimumAuxiliaryBound (n d : ℕ) (A B L b : ℝ)  :=
  hypersurfaceAbsoluteAuxiliaryConstant n *
    (max (affineHeightTransferConstant n) (Real.exp 1) * A *
        ↑d ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log L + d * Real.log B + ↑d ^ 2) (↑d ^ 2 * b) *
        B ^ (1 / degreeRoot n d) /
          L ^ (heightExponent n d) +
      ↑d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        ↑d ^ (4 - 1 / (n + 1 : ℝ)))

variable {n : ℕ} (f : CCDN.IntegerPolynomial (n + 2)) (hf : f ≠ 0) (hd : 0 < f.totalDegree) {p : ℕ} (hp : p.Prime) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)

include hf hd hp hA hB in
/-- The scaled auxiliary degree bound for any bad-prime factor `c` with
`c ≤ Real.exp 1 * b` and `0 ≤ b`. -/
theorem scaled_hypersurface_auxiliary_bound_of_badPrime_le 
    (hBp : B / A ≤ p) {c b : ℝ} (hFbad : 0 ≤ c) (hb : 0 ≤ b)
    (hbad : c ≤ Real.exp 1 * b) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B c
        (integerCoefficientHeight (scaledHomogenize f.totalDegree ↑p f) : ℝ) ≤
      hypersurfaceAbsoluteAuxiliaryConstant n *
        (Real.exp 1 * A * ↑f.totalDegree ^ (2 - 1 / (n + 1 : ℝ)) *
            (↑f.totalDegree ^ 2 *
              b) *
            B ^ (1 / degreeRoot n f.totalDegree) /
              (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ^
                (heightExponent n f.totalDegree) +
          ↑f.totalDegree ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
            ↑f.totalDegree ^ (4 - 1 / (n + 1 : ℝ))) := by
  let d := f.totalDegree
  let F := scaledHomogenize d ↑p f
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let H := (integerCoefficientHeight F : ℝ)
  let Y := ↑p ^ d * L
  let α := boxExponent n d
  let β := 1 / ((n + 1 : ℝ) * degreeRoot n d)
  let q := heightExponent n d
  have hd0 : (0 : ℝ) < d := by positivity
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL := leading_height_one_le f hf
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := mul_pos (pow_pos hp0 _) hL0
  have hYH := by
    simpa only [Int.cast_natCast] using scaledHomogenize_leading_height_lower f hpZ
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hYpow := by
    simpa only [dimensionRoot, Nat.cast_add, Nat.cast_one] using
      scaled_height_rpow (r := n + 1) (by omega) hd hp0 hL0
  have hdenom := Real.rpow_le_rpow hY0.le hYH hq
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hpower := by
    simpa only [dimensionRoot, Nat.cast_add, Nat.cast_one, hnR] using
      affine_scaling_box_power (r := n + 1) (by omega) hd hB hA hp0 hBp
  have hpowers :=
    rpow_four_sub_eq_mul_sq hd0 n
  have hmain : ↑d ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / H ^ q ≤
      Real.exp 1 * A * ↑d ^ (2 - 1 / (n + 1 : ℝ)) * (↑d ^ 2 * b) *
        B ^ (1 / degreeRoot n d) / L ^ q := by
    calc
      _ ≤ ↑d ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / Y ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
      _ ≤ ↑d ^ (4 - 1 / (n + 1 : ℝ)) * (Real.exp 1 * b) * B ^ α / Y ^ q := by
        bound
      _ = (Real.exp 1 * ↑d ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) *
          (B ^ α / ↑p ^ β) := by rw [hYpow]; ring
      _ ≤ (Real.exp 1 * ↑d ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) *
          (A * B ^ (1 / degreeRoot n d)) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by rw [hpowers]; ring
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain le_rfl) le_rfl)
    (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le

include hf hd hp hA hB in
private theorem scaled_hypersurface_auxiliary_badPrime_bound 
    (hBp : B / A ≤ p) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree ↑p f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree ↑p f) : ℝ) ≤
      hypersurfaceAbsoluteAuxiliaryConstant n *
        (Real.exp 1 * A * ↑f.totalDegree ^ (2 - 1 / (n + 1 : ℝ)) *
            (↑f.totalDegree ^ 2 *
              hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) *
            B ^ (1 / degreeRoot n f.totalDegree) /
              (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ^
                (heightExponent n f.totalDegree) +
          ↑f.totalDegree ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
            ↑f.totalDegree ^ (4 - 1 / (n + 1 : ℝ))) := by
  grind [hypersurfaceBadPrimeFactor_scaledHomogenize_le, scaled_hypersurface_auxiliary_bound_of_badPrime_le, hypersurfaceBadPrimeFactor_nonneg]


/-- If the constant coefficient `c` of a primitive irreducible integer polynomial `f` is nonzero
and `log |c| < B / scalingPrimeRatio`, with `B ≥ scalingPrimeRatio`, then `f` has a box
auxiliary polynomial of degree at most `affineMinimumAuxiliaryBound`, with ratio
`scalingPrimeRatio` and the bad-prime factor of the homogenization of `f`. -/
theorem affine_auxiliary_minimum_of_small_constant_coefficient {n : ℕ}
    (f : CCDN.IntegerPolynomial (n + 2)) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    (hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio) :
    ∃ g, IsBoxAuxiliary f g B ∧
      ↑g.totalDegree ≤ affineMinimumAuxiliaryBound n f.totalDegree scalingPrimeRatio B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hB hc hheight
  exact (by
          let inline_hB := LE.le.trans scalingPrimeRatio_one_le hB
          let inline_hBp := LT.lt.le hlo
          obtain ⟨g, hg, hgdegree⟩ := prime_scaled_affine_auxiliary f hprim hir hd hp hnd inline_hB hhi
          exact ⟨g, hg, hgdegree.trans
            ((by
               let inline_hf := Irreducible.ne_zero hir
               let scalingPrimeRatio_one_le := scalingPrimeRatio_one_le
               let d := f.totalDegree
               let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
               let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
               let T := Real.log L + d * Real.log B + ↑d ^ 2
               have hL := leading_height_one_le f inline_hf
               have hT : 0 ≤ T := add_nonneg
                 (add_nonneg (Real.log_nonneg hL) (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg inline_hB)))
                 (sq_nonneg _)
               have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
               have hA0 := zero_le_one.trans scalingPrimeRatio_one_le
               by_cases hmin : T ≤ ↑d ^ 2 * b
               · apply (scaled_hypersurface_auxiliary_bound f inline_hf hd
                   (by exact_mod_cast hp.one_lt.le : (1 : ℤ) ≤ p) scalingPrimeRatio_one_le inline_hB
                   (by simp_all)
                   (by simp_all)).trans
                 unfold affineLogarithmicAuxiliaryBound affineMinimumAuxiliaryBound
                 rw [min_eq_left hmin]
                 apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
                 apply add_le_add _ le_rfl
                 apply add_le_add _ le_rfl
                 apply div_le_div_of_nonneg_right _ (by positivity)
                 exact mul_le_mul_of_nonneg_right
                   (mul_le_mul_of_nonneg_right
                     (mul_le_mul_of_nonneg_right
                       (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0) (by positivity)) hT) (by positivity)
               · apply (scaled_hypersurface_auxiliary_badPrime_bound f inline_hf hd hp scalingPrimeRatio_one_le inline_hB inline_hBp).trans
                 unfold affineMinimumAuxiliaryBound
                 rw [min_eq_right (le_of_not_ge hmin)]
                 apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
                 apply add_le_add _ le_rfl
                 apply add_le_add _ le_rfl
                 apply div_le_div_of_nonneg_right _ (by positivity)
                 exact mul_le_mul_of_nonneg_right
                   (mul_le_mul_of_nonneg_right
                     (mul_le_mul_of_nonneg_right
                       (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0) (by positivity)) (by positivity))
                     (by positivity)))⟩)

end CCDN
