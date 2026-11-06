/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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
open MvPolynomial Real

/-- The height-loss factor `(d + 1) ^ (4 (d + 1)) (d + 2) ^ 2 (2 d + 1) ^ d` by which the
coefficients of the affine chart of a ternary form of degree `d`, after a translation with
parameters in `[0, d]`, may exceed a coefficient height `L` of the form (measured as
`(d + 1) ^ (2 (d + 1)) * L`); see `homogeneousTranslation_chart_coefficient_bound`. -/
def leadingPositionHeightFactor (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) ^ (4 * (d + 1)) * ((d : ℝ) + 2) ^ 2 * (2 * (d : ℝ) + 1) ^ d

/-- The factor `leadingPositionHeightFactor d` is at least `1`. -/
lemma leadingPositionHeightFactor_one_le (d : ℕ) : 1 ≤ leadingPositionHeightFactor d := by
  unfold leadingPositionHeightFactor
  have := Nat.cast_nonneg (α := ℝ) d
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith)))
    (one_le_pow₀ (by linarith))

/-- For `d ≥ 1`, the logarithm of `leadingPositionHeightFactor d` is at most `14 d²`. -/
lemma leadingPositionHeightFactor_log_le {d : ℕ} (hd : 0 < d) :
    Real.log (leadingPositionHeightFactor d) ≤ 14 * (d : ℝ) ^ 2 := by
  have hdR : (1 : ℝ) ≤ d := mod_cast hd
  have h₁ : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  have h₂ : Real.log ((d : ℝ) + 2) ≤ d + 1 := by
    rw [show (d : ℝ) + 2 = (d + 1) + 1 by ring]
    exact Real.log_add_one_le_self (by positivity)
  have h₃ : Real.log (2 * (d : ℝ) + 1) ≤ 2 * d := Real.log_add_one_le_self (by positivity)
  unfold leadingPositionHeightFactor
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
     Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  exact (by gcongr : _ ≤ 4 * ((d : ℝ) + 1) * d + 2 * ((d : ℝ) + 1) + d * (2 * d)).trans
    (by nlinarith)

/-- A bounded integer translation supplies the leading-position
hypothesis with absolute constant 14, and a coefficient height at least one. -/
theorem exists_translated_coefficient_position {d : ℕ} (hd : 0 < d)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      CoefficientHeightLE (affineChart 2 (homogeneousTranslation ℤ a f)) H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| ≤
        Real.log H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          14 * (d : ℝ) ^ 2 := by
  obtain ⟨a, ha, hne, hcoeff⟩ := exists_bounded_leading_coefficient_translation f hf hf0
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by dsimp only [L]; exact_mod_cast Int.one_le_abs hne
  have hP := leadingPositionHeightFactor_one_le d
  have hpos : 0 < leadingPositionHeightFactor d := by linarith
  have hLpos : 0 < L := by linarith
  let K := ((d : ℝ) + 1) ^ (2 * (d + 1))
  let V := ((d : ℝ) + 2) ^ 2 * (K * L) * (2 * (d : ℝ) + 1) ^ d
  have hdim : ((2 + d).choose d : ℝ) ≤ ((d : ℝ) + 2) ^ 2 := by
    have : 2 * ((2 + d).choose d : ℝ) = ((d : ℝ) + 2) * (d + 1) :=
      mod_cast ternary_homogeneous_dimension d
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have heval (x y : ℕ) (hx : x ≤ d) (hy : y ≤ d) :
      |(eval ![(x : ℤ), (y : ℤ)] (affineChart 2 (homogeneousTranslation ℤ a f)) : ℝ)| ≤ V := by
    let z : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
    have hz (j : Fin 2) : 0 ≤ z j ∧ z j ≤ d := by
      fin_cases j <;> dsimp [z]
      · exact ⟨by positivity, mod_cast hx⟩
      · exact ⟨by positivity, mod_cast hy⟩
    let w : Fin 3 → ℤ := Fin.cons 1 (z + a)
    have hbox : InBox w (2 * d + 1) :=
      Fin.cases (by simp only [w, Fin.cons_zero, Int.cast_one, abs_one]; linarith [d.cast_nonneg (α := ℝ)])
        fun k => by
          simp only [w, Fin.cons_succ, Pi.add_apply, Int.cast_add]
          have hz0 : (0 : ℝ) ≤ z k := mod_cast (hz k).1
          have ha0 : (0 : ℝ) ≤ a k := mod_cast (ha k).1
          have hzd : (z k : ℝ) ≤ d := mod_cast (hz k).2
          have had : (a k : ℝ) ≤ d := mod_cast (ha k).2
          rw [abs_of_nonneg (by linarith)]; linarith
    rw [affineChart_eval, homogeneousTranslation_eval_chart]
    have hsum : |(eval w f : ℝ)| ≤ ((2 + d).choose d : ℝ) * (K * L) * (2 * (d : ℝ) + 1) ^ d := by
      classical
      conv_lhs => rw [homogeneous_eq_sum_coeff f hf]
      simp only [map_sum, eval_monomial, Int.cast_sum, Int.cast_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun j _ => (?_ : _ ≤ (K * L) * (2 * (d : ℝ) + 1) ^ d)).trans_eq
          (by simp [mul_assoc]))
      rw [abs_mul]
      exact mul_le_mul (hcoeff _) (abs_monomial_value_le _ w
        (by linarith [d.cast_nonneg (α := ℝ)]) hbox (homogeneousMonomials_degree 2 d j).le)
        (abs_nonneg _) (by dsimp [K]; positivity)
    exact hsum.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdim (by positivity)) (by positivity))
  refine ⟨a, leadingPositionHeightFactor d * L, ha, one_le_mul_of_one_le_of_one_le hP hL,
    fun m => (integer_plane_coefficient_bound_of_grid (affineChart 2 (homogeneousTranslation ℤ a f))
      ((affineChart_totalDegree_le _).trans (homogeneousTranslation_homogeneous a hf).totalDegree_le)
      (show 0 ≤ V by dsimp [V, K]; positivity) heval m).trans_eq (by
        dsimp only [leadingPositionHeightFactor, V, K]
        rw [show 4 * (d + 1) = 2 * (d + 1) + 2 * (d + 1) by omega, pow_add]; ring),
    Real.log_le_log hLpos (by nlinarith), ?_⟩
  rw [Real.log_mul hpos.ne' hLpos.ne']
  linarith [leadingPositionHeightFactor_log_le hd]

end
end CCDN
