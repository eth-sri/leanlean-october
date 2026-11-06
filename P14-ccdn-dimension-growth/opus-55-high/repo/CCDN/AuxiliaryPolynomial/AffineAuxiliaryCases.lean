/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.UnscaledAffineMinimum
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Height.ScaledHypersurfaceHeight

/-! All box and coefficient cases for the affine auxiliary theorem when
the constant coefficient is nonzero. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable (n d : ℕ)

/-- The affine auxiliary degree bound `affineMinimumAuxiliaryBound` is monotone in the
comparison constant `A` and the bad-prime factor `b`. -/
lemma affineMinimumAuxiliaryBound_mono {A A' B L b b' : ℝ}
    (hA : A ≤ A') (hA' : 0 ≤ A') (hB : 1 ≤ B) (hL : 1 ≤ L) (hb0 : 0 ≤ b) (hb : b ≤ b') :
    affineMinimumAuxiliaryBound n d A B L b ≤ affineMinimumAuxiliaryBound n d A' B L b' := by
  have hT : 0 ≤ Real.log L + d * Real.log B + (d : ℝ) ^ 2 := by bound
  have hmin := le_min hT (mul_nonneg (sq_nonneg (d : ℝ)) hb0)
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
    (Real.exp_pos 1).le.trans (le_max_right _ _)
  have hC := (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold affineMinimumAuxiliaryBound
  gcongr

end

/-- The affine auxiliary degree bound is at least the degree `d` whenever `0 < d`, so the
equation itself always meets it. -/
lemma degree_le_affineMinimumAuxiliaryBound (n : ℕ) {d : ℕ} (hd : 0 < d)
    {A B L b : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    (d : ℝ) ≤ affineMinimumAuxiliaryBound n d A B L b := by
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hn1 : (1 : ℝ) ≤ n + 1 := by grind
  have hdD : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
  have hT : 0 ≤ Real.log L + d * Real.log B + (d : ℝ) ^ 2 :=
    add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB))) (sq_nonneg _)
  have hmin := le_min hT (mul_nonneg (sq_nonneg (d : ℝ)) hb)
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) :=
    (Real.exp_pos 1).le.trans (le_max_right _ _)
  have hlog := Real.log_nonneg hB
  have hC := hypersurfaceAbsoluteAuxiliaryConstant_one_le n
  let E := max (affineHeightTransferConstant n) (Real.exp 1) * A *
      (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
      min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
      B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
        L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  exact (hdD.trans (le_add_of_nonneg_left (by positivity))).trans
    (le_mul_of_one_le_left (by positivity) hC)

/-- The scale $4 R^2$, with `R = scalingPrimeRatio`, of the small-box threshold
`affineAuxiliaryBoxScale * (d + 1) ^ affineAuxiliaryBoxExponent n` separating the unscaled
case of the affine auxiliary theorem from the prime-scaled cases. -/
def affineAuxiliaryBoxScale : ℝ := 4 * scalingPrimeRatio ^ 2

section
variable (n : ℕ)

/-- The exponent $4(n + 2) + 2$ of `d + 1` in the small-box threshold of the affine
auxiliary theorem for equations in `n + 2` variables. -/
def affineAuxiliaryBoxExponent : ℕ := 4 * (n + 2) + 2

/-- The comparison constant used uniformly over all box radii in the affine auxiliary
theorem: the larger of `scalingPrimeRatio` and the small-box scale times
$e^{(4(n + 2) + 2)(n + 2)}$. -/
def affineAuxiliaryComparisonConstant : ℝ :=
  max scalingPrimeRatio
    (Real.exp (Real.log affineAuxiliaryBoxScale + (affineAuxiliaryBoxExponent n : ℝ) * (n + 2 : ℝ)))

end

/-- The small-box scale `affineAuxiliaryBoxScale` is at least `1`. -/
lemma affineAuxiliaryBoxScale_one_le : 1 ≤ affineAuxiliaryBoxScale := by
  have h := scalingPrimeRatio_one_le
  unfold affineAuxiliaryBoxScale
  nlinarith

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
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
  have hL := leading_height_one_le f hir.ne_zero
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
  have hb' : hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) ≤
      hypersurfaceBadPrimeFactor f := by
    apply hypersurfaceBadPrimeFactor_mono_of_badReduction_imp
    · exact (scaledHomogenize_homogeneous 1 f le_rfl).totalDegree
        (scaledHomogenize_ne_zero _ one_ne_zero hir.ne_zero)
    · exact (unscaledHomogenize_absolute_irreducible_iff f hir.ne_zero).mp
    · exact hypersurfaceBadReduction_unscaledHomogenize_imp f hir.ne_zero
  have hA := affineAuxiliaryComparisonConstant_one_le n
  by_cases hsmall : B ≤ affineAuxiliaryBoxScale * (d + 1) ^ affineAuxiliaryBoxExponent n
  · obtain ⟨g, hg, hgdeg⟩ := unscaled_affine_auxiliary_minimum f hprim hir hd
      affineAuxiliaryBoxScale_one_le hB hsmall
    refine ⟨g, hg, hgdeg.trans ?_⟩
    exact affineMinimumAuxiliaryBound_mono n d (le_max_right _ _) (zero_le_one.trans hA) hB hL hb hb'
  · have hBA : scalingPrimeRatio ≤ B := by
      have hS : scalingPrimeRatio ≤ affineAuxiliaryBoxScale := by
        have h := scalingPrimeRatio_one_le
        unfold affineAuxiliaryBoxScale
        nlinarith
      have hpow : (1 : ℝ) ≤ (d + 1) ^ affineAuxiliaryBoxExponent n :=
        by bound
      nlinarith
    by_cases hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio
    · obtain ⟨g, hg, hgdeg⟩ := affine_auxiliary_minimum_of_small_constant_coefficient
        f hprim hir hd hc hBA hheight
      refine ⟨g, hg, hgdeg.trans ?_⟩
      exact affineMinimumAuxiliaryBound_mono n d (le_max_left _ _) (zero_le_one.trans hA) hB hL hb hb'
    · rcases affine_coefficient_height_dichotomy f hir.ne_zero hprim hB with hh | hg
      · have hcoef :=
          Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc))
            (coefficient_abs_le_integerCoefficientHeight f 0)
        have hcut := affine_coefficient_height_cutoff (n + 2) d scalingPrimeRatio_one_le hB
          ((le_of_not_gt hheight).trans (hcoef.trans hh))
        tauto
      · obtain ⟨g, hg, hgdeg⟩ := hg
        refine ⟨g, hg, ?_⟩
        have hgR : (g.totalDegree : ℝ) ≤ d := mod_cast hgdeg
        exact hgR.trans (degree_le_affineMinimumAuxiliaryBound n hd (zero_le_one.trans hA) hB hL
          (hypersurfaceBadPrimeFactor_nonneg f))

