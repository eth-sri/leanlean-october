/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineMinimum
import CCDN.AuxiliaryPolynomial.AffineHeightCutoff
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.ScaledAffineAuxiliary
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.AuxiliaryPolynomial.ScaledHypersurfaceBadPrimes
public import CCDN.AuxiliaryPolynomial.ScalingPrime
import CCDN.Algebra.ScaledHomogenizationPrimitive
import CCDN.Height.ScaledHypersurfaceHeight

/-! All box and coefficient cases for the affine auxiliary theorem when
the constant coefficient is nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma degree_le_affineMinimumAuxiliaryBound (n : ℕ) {d : ℕ} (hd : 0 < d)
    {A B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    (d : ℝ) ≤ affineMinimumAuxiliaryBound n d A B L b := by
  have := Real.log_nonneg hB
  have hQ : 1 ≤ B ^ (1 / degreeRoot n d) := Real.one_le_rpow hB (by positivity)
  refine (le_auxDegreeScale (n := n) hd).trans ?_
  have hC := affineMinimumConstant_one_le n A
  have hmin : 0 ≤ min (1 + Real.log B / d) (b / L ^ heightExponent n d) := by positivity
  unfold affineMinimumAuxiliaryBound affineAuxiliaryDegreeExpression
  calc
    _ = 1 * (auxDegreeScale n d * 1 * 1) := by ring
    _ ≤ _ := by gcongr; linarith

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

/-- The small-box scale `affineAuxiliaryBoxScale` is at least `1`. -/
lemma affineAuxiliaryBoxScale_one_le : 1 ≤ affineAuxiliaryBoxScale := by
  have h := scalingPrimeRatio_one_le
  unfold affineAuxiliaryBoxScale
  nlinarith

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
  let R := scalingPrimeRatio
  have hb' := hypersurfaceBadPrimeFactor_unscaledHomogenize_le f hir.ne_zero
  have hb := hypersurfaceBadPrimeFactor_nonneg f
  have hL := leading_height_one_le f hir.ne_zero
  have hE := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  by_cases hsmall : B ≤ affineAuxiliaryBoxScale * ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n
  · apply scaled_affine_auxiliary_minimum f hir hd (a := 1) le_rfl (hprim.scaledHomogenize_one _) hB
      (by simpa using hB)
    · simp only [Int.cast_one, div_one]
      exact (polynomial_box_root_power_bound hd affineAuxiliaryBoxScale_one_le hB hsmall).trans (le_max_right _ _)
    · exact hb'.trans (le_mul_of_one_le_left hb hE)
  · have hBA : R ≤ B := by
      have hS : R ≤ affineAuxiliaryBoxScale := by
        have h := scalingPrimeRatio_one_le
        unfold affineAuxiliaryBoxScale
        dsimp [R]
        nlinarith
      have hpow : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ affineAuxiliaryBoxExponent n :=
        one_le_pow₀ (by simp)
      exact hS.trans ((le_mul_of_one_le_right (zero_le_one.trans affineAuxiliaryBoxScale_one_le) hpow).trans (le_of_not_ge hsmall))
    by_cases hheight : Real.log |(f.coeff 0 : ℝ)| < B / R
    · obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hBA hc hheight
      apply scaled_affine_auxiliary_minimum f hir hd (a := (p : ℤ)) (by exact_mod_cast hp.one_le)
        (hprim.scaledHomogenize _ hp hnd) hB (by exact_mod_cast hhi)
      · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
        have hBR : B / (p : ℝ) ≤ R := by
          rw [div_le_iff₀ hp0]
          have h := (div_le_iff₀ (scalingPrimeRatio_one_le.trans_lt' zero_lt_one)).mp hlo.le
          linarith
        simpa only [Int.cast_natCast] using
          ((Real.rpow_le_rpow (by positivity) hBR (by positivity)).trans
            ((Real.rpow_le_rpow_of_exponent_le scalingPrimeRatio_one_le (scaleExponent_le_one n hd)).trans
              ((Real.rpow_one _).le.trans (show R ≤ affineAuxiliaryComparisonConstant n from le_max_left _ _))))
      · exact (hypersurfaceBadPrimeFactor_scaledHomogenize_le f hir.ne_zero hp).trans (by gcongr)
    · rcases affine_coefficient_height_dichotomy f hir.ne_zero hprim hB with H | ⟨g, hg, hdeg⟩
      · exfalso
        apply hsmall
        apply affine_coefficient_height_cutoff (n + 2) d scalingPrimeRatio_one_le hB
        exact (le_of_not_gt hheight).trans ((Real.log_le_log (abs_pos.mpr (by exact_mod_cast hc))
          (coefficient_abs_le_integerCoefficientHeight f 0)).trans H)
      · exact ⟨g, hg, (Nat.cast_le.mpr hdeg).trans (degree_le_affineMinimumAuxiliaryBound n hd hB hL hb)⟩

end
end CCDN
