/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousChart
import CCDN.Height.MultivariateGridHeight
import CCDN.Plane.HomogeneousLeadingCoefficient

/-!
The bounded shear has a dimension-uniform logarithmic positioning cost.

Bounded integer shears placing a large coefficient first, in all dimensions.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {n r d : ℕ}

/-- The large leading-coefficient witness in arbitrary projective dimension.
Every original coefficient is controlled by one bounded grid evaluation. -/
theorem exists_hypersurface_leading_coefficient_translation
    (f : IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ a : Fin n → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧
      MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) ≠ 0 ∧
      CoefficientHeightLE f (((d:ℝ)+1) ^ (n*(d+1)) *
        |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|) := by
  have hc0 : affineChart n f ≠ 0 := by
    intro hz
    exact hf0 (affineChart_injective_on_homogeneous hf (isHomogeneous_zero _ _ d)
      (by simpa only [map_zero] using hz))
  obtain ⟨a, ha, hval, hcoeff⟩ := exists_integer_multivariate_grid_height_witness (affineChart n f)
    hc0 ((affineChart_totalDegree_le f).trans hf.totalDegree_le)
  have he : (homogeneousTranslation ℤ a f).coeff (Finsupp.single 0 d) =
      eval a (affineChart n f) := by
    rw [homogeneousTranslation_pure_first a f hf, affineChart_eval]
  have hlc := lex_leadingCoeff_eq_pure_first (homogeneousTranslation ℤ a f)
    (homogeneousTranslation_homogeneous a hf).totalDegree_le (he ▸ hval)
  refine ⟨a, ha, by rw [hlc, he]; exact hval, ?_⟩
  intro m
  by_cases hm : m.degree = d
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n d m hm
    rw [← affineChart_homogeneous_coefficient f hf j, hlc, he]
    exact hcoeff _
  · rw [hf.coeff_eq_zero hm, Int.cast_zero, abs_zero]
    positivity


lemma log_nat_add_one_le_root (hr : 0 < r) (hd : 0 < d) :
    Real.log ((d : ℝ) + 1) ≤ ((r : ℝ) + 1) * (d : ℝ) ^ (1 / (r : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hroot : (1 : ℝ) ≤ (d : ℝ) ^ (1 / (r : ℝ)) :=
    Real.one_le_rpow hd1 (by positivity)
  have hlog := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ d)
    (show (0 : ℝ) < 1 / (r : ℝ) by positivity)
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < d + 1)
    (show (d : ℝ) + 1 ≤ 2 * d by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  rw [div_div_eq_mul_div, div_one] at hlog
  nlinarith

end
end CCDN
