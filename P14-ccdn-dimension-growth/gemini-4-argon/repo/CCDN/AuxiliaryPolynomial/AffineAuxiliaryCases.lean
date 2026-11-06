/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.UnscaledAffineMinimum
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Height.ScaledHypersurfaceHeight

/-! All box and coefficient cases for the affine auxiliary theorem when
the constant coefficient is nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The scale $4 R^2$, with `R = scalingPrimeRatio`, of the small-box threshold
`affineAuxiliaryBoxScale * (d + 1) ^ affineAuxiliaryBoxExponent n` separating the unscaled
case of the affine auxiliary theorem from the prime-scaled cases. -/
def affineAuxiliaryBoxScale : ℝ := 4 * scalingPrimeRatio ^ 2

/-- The exponent $4(n + 2) + 2$ of `d + 1` in the small-box threshold of the affine
auxiliary theorem for equations in `n + 2` variables. -/
def affineAuxiliaryBoxExponent (n : ℕ) : ℕ := 4 * (n + 2) + 2

/-- The comparison constant used uniformly over all box radii in the affine auxiliary
theorem: the larger of `scalingPrimeRatio` and the small-box scale times
$e^{(4(n + 2) + 2)(n + 2)}$. -/
def affineAuxiliaryComparisonConstant (n : ℕ) : ℝ :=
  max scalingPrimeRatio
    (Real.exp (Real.log affineAuxiliaryBoxScale + (affineAuxiliaryBoxExponent n : ℝ) * (n + 2 : ℝ)))

/-- The comparison constant `affineAuxiliaryComparisonConstant n` is at least `1`. -/
lemma affineAuxiliaryComparisonConstant_one_le (n : ℕ) :
    1 ≤ affineAuxiliaryComparisonConstant n :=
  scalingPrimeRatio_one_le.trans (le_max_left _ _)

/-- Every primitive irreducible equation with nonzero constant coefficient
has the affine auxiliary, uniformly over all box radii. -/
theorem affine_auxiliary_minimum_nonzero_constant {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree
        (affineAuxiliaryComparisonConstant n) B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor f) := by
  /- The affine auxiliary degree bound `affineMinimumAuxiliaryBound` is monotone in the
  comparison constant `A`, for `1 ≤ B`, `1 ≤ L` and `0 ≤ b`. -/
  /- The affine auxiliary degree bound `affineMinimumAuxiliaryBound` is monotone in the
  bad-prime factor `b`, for `0 ≤ A`, `1 ≤ B` and `1 ≤ L`. -/
  /- The affine auxiliary degree bound is at least the degree `d` whenever `0 < d`, so the
  equation itself always meets it. -/
  /- The small-box scale `affineAuxiliaryBoxScale` is at least `1`. -/
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
  have hL : 1 ≤ L := leading_height_one_le f hir.ne_zero
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
  have hb' : b ≤ hypersurfaceBadPrimeFactor f :=
    hypersurfaceBadPrimeFactor_unscaledHomogenize_le f hir.ne_zero
  have hA : 1 ≤ affineAuxiliaryComparisonConstant n := affineAuxiliaryComparisonConstant_one_le n
  have hT : 0 ≤ Real.log L + d * Real.log B + (d : ℝ) ^ 2 :=
    add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB))) (sq_nonneg _)
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
    (Real.exp_pos 1).le.trans (le_max_right _ _)
  have hC := (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  have hmono {A : ℝ} (hA0 : 0 ≤ A) (hAle : A ≤ affineAuxiliaryComparisonConstant n) :
      affineMinimumAuxiliaryBound n d A B L b ≤
        affineMinimumAuxiliaryBound n d (affineAuxiliaryComparisonConstant n) B L
          (hypersurfaceBadPrimeFactor f) := by
    have hmin := le_min hT (mul_nonneg (sq_nonneg (d : ℝ)) hb)
    unfold affineMinimumAuxiliaryBound
    gcongr
  have hS1 : 1 ≤ affineAuxiliaryBoxScale := by
    have := scalingPrimeRatio_one_le; unfold affineAuxiliaryBoxScale; nlinarith
  by_cases hsmall : B ≤ affineAuxiliaryBoxScale * ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n
  · obtain ⟨g, hg, hgdeg⟩ := unscaled_affine_auxiliary_minimum f hprim hir hd hS1 hB hsmall
    exact ⟨g, hg, hgdeg.trans (hmono (Real.exp_pos _).le (le_max_right _ _))⟩
  · have hBA : scalingPrimeRatio ≤ B := by
      have hS : scalingPrimeRatio ≤ affineAuxiliaryBoxScale := by
        have := scalingPrimeRatio_one_le; unfold affineAuxiliaryBoxScale; nlinarith
      have hpow : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n :=
        one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) d])
      exact (hS.trans (le_mul_of_one_le_right (zero_le_one.trans hS1) hpow)).trans
        (le_of_not_ge hsmall)
    by_cases hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio
    · obtain ⟨g, hg, hgdeg⟩ := affine_auxiliary_minimum_of_small_constant_coefficient
        f hprim hir hd hc hBA hheight
      exact ⟨g, hg, hgdeg.trans (hmono (zero_le_one.trans scalingPrimeRatio_one_le) (le_max_left _ _))⟩
    · rcases affine_coefficient_height_dichotomy f hir.ne_zero hprim hB with hh | ⟨g, hg, hgdeg⟩
      · have hcoef : Real.log |(f.coeff 0 : ℝ)| ≤ Real.log (integerCoefficientHeight f : ℝ) :=
          Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc))
            (coefficient_abs_le_integerCoefficientHeight f 0)
        exact (hsmall (affine_coefficient_height_cutoff (n + 2) d scalingPrimeRatio_one_le hB
          ((le_of_not_gt hheight).trans (hcoef.trans hh)))).elim
      · refine ⟨g, hg, ((mod_cast hgdeg : (g.totalDegree : ℝ) ≤ d).trans
          (le_rpow_four_sub_inv (n := n) hd)).trans ?_⟩
        have hbf := hypersurfaceBadPrimeFactor_nonneg f
        have hmin := le_min hT (mul_nonneg (sq_nonneg (d : ℝ)) hbf)
        have hlog := Real.log_nonneg hB
        have hA0 := zero_le_one.trans hA
        let E := max (affineHeightTransferConstant n) (Real.exp 1) *
            affineAuxiliaryComparisonConstant n * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
            min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * hypersurfaceBadPrimeFactor f) *
            B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
              L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
            (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
        have hE : 0 ≤ E := by dsimp only [E]; positivity
        unfold affineMinimumAuxiliaryBound
        exact (le_add_of_nonneg_left hE).trans
          (le_mul_of_one_le_left (by positivity) (hypersurfaceAbsoluteAuxiliaryConstant_one_le n))

end
end CCDN
