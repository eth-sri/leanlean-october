/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.Algebra.HomogeneousRankDichotomy
import CCDN.ForMathlib.Log
import CCDN.Plane.GridHeight
import CCDN.Plane.HomogeneousLeadingCoefficient

/-!
The bounded leading-coefficient translation has a controlled height cost.
Its logarithmic coefficient-position loss is at most 14d².

Coefficient height controls homogeneous evaluations, uniformly on the
integer point box, with the exact number of monomials.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem homogeneous_integer_evaluation_bound {n d : ℕ}
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d)
    {H R : ℝ} (hH : 0 ≤ H) (hR : 1 ≤ R) (hcoeff : CoefficientHeightLE f H)
    (x : CCDN.IntPoint (n + 1)) (hx : InBox x R) :
    |(eval x f : ℝ)| ≤ ((n + d).choose d : ℝ) * H * R ^ d := by
  classical
  conv_lhs => rw [homogeneous_eq_sum_coeff f hf]
  simp only [map_sum, eval_monomial, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ j, |(f.coeff (homogeneousMonomials n d j) : ℝ) *
      (((homogeneousMonomials n d j).prod (fun i k => x i ^ k) : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin ((n + d).choose d), H * R ^ d := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoeff _) (abs_monomial_value_le _ x hR hx
        (homogeneousMonomials_degree n d j).le) (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

private lemma ternary_homogeneous_dimension_le_square (d : ℕ) :
    ((2 + d).choose d : ℝ) ≤ (↑d + 2) ^ 2 := by
  have h : 2 * ((2 + d).choose d : ℝ) = (↑d + 2) * (d + 1) := by
    exact_mod_cast ternary_homogeneous_dimension d
  nlinarith [show 0 ≤ d by positivity]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Real

/-- The height-loss factor `(d + 1) ^ (4 (d + 1)) (d + 2) ^ 2 (2 d + 1) ^ d` by which the
coefficients of the affine chart of a ternary form of degree `d`, after a translation with
parameters in `[0, d]`, may exceed a coefficient height `L` of the form (measured as
`(d + 1) ^ (2 (d + 1)) * L`); see `homogeneousTranslation_chart_coefficient_bound`. -/
def leadingPositionHeightFactor (d : ℕ) : ℝ :=
  (↑d + 1) ^ (4 * (d + 1)) * (↑d + 2) ^ 2 * (2 * ↑d + 1) ^ d

/-- The factor `leadingPositionHeightFactor d` is at least `1`. -/
lemma leadingPositionHeightFactor_one_le (d : ℕ) : 1 ≤ leadingPositionHeightFactor d := by
  apply one_le_mul_of_one_le_of_one_le
  · grind [one_le_mul_of_one_le_of_one_le, one_le_pow₀]
  · simp_all [one_le_pow₀, Nat.cast_nonneg]

variable {d : ℕ}

/-- For `d ≥ 1`, the logarithm of `leadingPositionHeightFactor d` is at most `14 d²`. -/
lemma leadingPositionHeightFactor_log_le  (hd : 0 < d) :
    Real.log (leadingPositionHeightFactor d) ≤ 14 * ↑d ^ 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h₁ := Real.log_add_one_le_self d.cast_nonneg
  have h₂ : Real.log (↑d + 2) ≤ d + 1 := by
    rw [show (d : ℝ) + 2 = (d + 1) + 1 by ring]
    exact Real.log_add_one_le_self (by positivity)
  have h₃ : Real.log (2 * ↑d + 1) ≤ 2 * d := Real.log_add_one_le_self (by positivity)
  unfold leadingPositionHeightFactor
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  calc
    _ ≤ 4 * (↑d + 1) * d + 2 * ((d : ℝ) + 1) + d * (2 * d) := by gcongr
    _ ≤ _ := by nlinarith


private lemma leadingPositionHeightFactor_interpolation_le (d : ℕ) :
    (↑d + 1) ^ (2 * (d + 1)) ≤ leadingPositionHeightFactor d := by
  have hb : (1 : ℝ) ≤ d + 1 := by linarith
  have h₁ : 1 ≤ ((d : ℝ) + 2) ^ 2 := one_le_pow₀ (by linarith)
  have h₂ : 1 ≤ (2 * (d : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
  have hp := pow_le_pow_right₀ hb (show 2 * (d + 1) ≤ 4 * (d + 1) by omega)
  unfold leadingPositionHeightFactor
  nlinarith [show 0 ≤ ((d : ℝ) + 1) ^ (4 * (d + 1)) by positivity,
    mul_le_mul_of_nonneg_left h₁ (show 0 ≤ (↑d + 1) ^ (4 * (d + 1)) by positivity)]

/-- A bounded integer translation supplies the leading-position
hypothesis with absolute constant 14, and a common height for the original form
and the translated chart. -/
theorem exists_translated_coefficient_position  (hd : 0 < d)
    (f : CCDN.IntegerPolynomial 3) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : CCDN.IntPoint 2) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      CoefficientHeightLE f H ∧
      CoefficientHeightLE (affineChart 2 (homogeneousTranslation ℤ a f)) H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| ≤
        Real.log H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          14 * ↑d ^ 2 := by
  obtain ⟨a, ha, hne, hcoeff⟩ := exists_bounded_leading_coefficient_translation f hf hf0
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Int.one_le_abs hne
  have hP := leadingPositionHeightFactor_one_le d
  have hLpos : 0 < L := by linarith
  refine ⟨a, leadingPositionHeightFactor d * L, ha, one_le_mul_of_one_le_of_one_le hP hL,
    ?_, (show ∀ (m : Fin (2 : ℕ) →₀ ℕ),
            |↑(((affineChart (2 : ℕ)) ((homogeneousTranslation ℤ a) f)).coeff m)| ≤ leadingPositionHeightFactor d * L from (by
          intro m
          let K := ((d : ℝ) + 1) ^ (2 * (d + 1))
          let V := (↑d + 2) ^ 2 * (K * L) * (2 * ↑d + 1) ^ d
          have heval (x y : ℕ) (hx : x ≤ d) (hy : y ≤ d) :
              |(eval ![↑x, (y : ℤ)] (affineChart 2 (homogeneousTranslation ℤ a f)) : ℝ)| ≤ V := by
            let z : CCDN.IntPoint 2 := ![↑x, ↑y]
            have hz : ∀ j, 0 ≤ z j ∧ z j ≤ d := by
              intro j
              fin_cases j
              · aesop
              · aesop
            have hbox : ∀ j, |((Fin.cons 1 (z + a) : CCDN.IntPoint 3) j : ℝ)| ≤ 2 * d + 1 := by
              intro j
              refine Fin.cases ?_ (fun k => ?_) j
              · simp_all
              · simp only [Fin.cons_succ, Pi.add_apply, Int.cast_add]
                have hz0 : (0 : ℝ) ≤ z k := by exact_mod_cast (hz k).1
                have ha0 : (0 : ℝ) ≤ a k := by exact_mod_cast (ha k).1
                have hzd : (z k : ℝ) ≤ d := by exact_mod_cast (hz k).2
                have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
                rw [abs_of_nonneg (by linarith)]
                linarith
            rw [affineChart_eval, homogeneousTranslation_eval_chart]
            have h := homogeneous_integer_evaluation_bound f hf (show 0 ≤ K * L by dsimp [K]; positivity)
              (show (1 : ℝ) ≤ 2 * d + 1 by simp_all)
              hcoeff (Fin.cons 1 (z + a)) hbox
            apply h.trans
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (ternary_homogeneous_dimension_le_square d) (by positivity))
              (by positivity)
          have h := integer_plane_coefficient_bound_of_grid (affineChart 2 (homogeneousTranslation ℤ a f))
            ((affineChart_totalDegree_le _).trans (homogeneousTranslation_homogeneous a hf).totalDegree_le)
            (show 0 ≤ V by dsimp [V, K]; positivity) heval m
          convert h using 1
          dsimp only [leadingPositionHeightFactor, V, K]
          ring)), ?_, ?_⟩
  · intro m
    exact (hcoeff m).trans (mul_le_mul_of_nonneg_right
      (leadingPositionHeightFactor_interpolation_le d) hLpos.le)
  · apply Real.log_le_log hLpos
    nlinarith
  · grind [Real.log_mul, leadingPositionHeightFactor_log_le]

end
end CCDN
