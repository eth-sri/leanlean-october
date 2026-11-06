/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.Algebra.HomogeneousTranslation
import CCDN.Height.IntegerCoefficientHeight
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.Algebra.HomogeneousRankDichotomy
import CCDN.ForMathlib.Log
import CCDN.Plane.GridHeight
import CCDN.Plane.HomogeneousLeadingCoefficient
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
The bounded leading-coefficient translation has a controlled height cost.
Its logarithmic coefficient-position loss is at most 14d².

Coefficient height controls homogeneous evaluations, uniformly on the
integer point box, with the exact number of monomials.
-/

namespace CCDN
open MvPolynomial

/-- The affine chart of a homogeneous polynomial has no larger coefficients. -/
lemma affineChart_coefficientHeightLE {n d : ℕ} (g : MvPolynomial (Fin (n + 1)) ℤ)
    (hg : g.IsHomogeneous d) {H : ℝ} (hH : 0 ≤ H) (h : CoefficientHeightLE g H) :
    CoefficientHeightLE (affineChart n g) H := by
  intro m
  by_cases hm : ∃ j, chartExponent (homogeneousMonomials n d j) = m
  · obtain ⟨j, rfl⟩ := hm
    rw [affineChart_homogeneous_coefficient g hg]
    exact h _
  · rw [homogeneous_eq_sum_coeff g hg]
    simp_all [affineChart_monomial, coeff_monomial]

/-- A bounded integer translation supplies the leading-position
hypothesis with absolute constant 14, and a coefficient height at least one. -/
theorem exists_translated_coefficient_position {d : ℕ} (hd : 0 < d)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧ CoefficientHeightLE f H ∧
      CoefficientHeightLE (affineChart 2 (homogeneousTranslation ℤ a f)) H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| ≤
        Real.log H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          14 * (d : ℝ) ^ 2 := by
  obtain ⟨a, ha, hne, hc⟩ := exists_hypersurface_leading_coefficient_translation f hf hf0
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast Int.one_le_abs hne
  have hP := hypersurfacePositionHeightFactor_one_le 2 d
  have hlog : Real.log (hypersurfacePositionHeightFactor 2 d) ≤ 14 * d ^ 2 := by
    unfold hypersurfacePositionHeightFactor
    rw [Real.log_pow]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < d + 1 by positivity)
    rcases Nat.lt_or_ge d 2 with h | h
    · obtain rfl : d = 1 := by omega
      norm_num
      linarith [Real.log_two_lt_d9]
    · have : (2 : ℝ) ≤ d := mod_cast h
      push_cast
      nlinarith
  refine ⟨a, hypersurfacePositionHeightFactor 2 d * L, ha, one_le_mul_of_one_le_of_one_le hP hL,
    fun m => (hc m).trans (mul_le_mul_of_nonneg_right
      (hypersurfacePositionHeightFactor_ge_grid 2 d) (by linarith)),
    affineChart_coefficientHeightLE _ (homogeneousTranslation_homogeneous a hf) (by positivity)
      (hypersurfaceTranslation_coefficient_bound f hf hf0 a ha (by linarith) hc), ?_, ?_⟩
  · exact Real.log_le_log (by linarith) (by nlinarith)
  · rw [Real.log_mul (by linarith) (by linarith)]
    linarith

end CCDN
