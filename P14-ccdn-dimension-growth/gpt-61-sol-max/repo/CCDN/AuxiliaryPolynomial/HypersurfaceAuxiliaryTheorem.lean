/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib.Tactic

public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.AuxiliaryPolynomial.HypersurfaceNonabsoluteAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceProjectiveAuxiliary

/-! CCDN Theorem 3.1.1 for irreducible integer homogeneous equations.
The constant is fixed before the equation, degree and radius are chosen. -/

public section
namespace CCDN
open MvPolynomial

/-- The constant `hypersurfaceAbsoluteAuxiliaryConstant n` is at least `1`. -/
lemma hypersurfaceAbsoluteAuxiliaryConstant_one_le (n : ℕ) :
    1 ≤ hypersurfaceAbsoluteAuxiliaryConstant n := by
  have hC :
      4 ≤ hypersurfacePositionedAuxiliaryConstant n (hypersurfaceAuxiliaryPositionConstant n) := by
    unfold hypersurfacePositionedAuxiliaryConstant
    have hE := Real.exp_pos (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n)
      (hypersurfaceAuxiliaryPositionConstant n))
    have hS : 0 ≤ Real.exp (hypersurfaceAuxiliaryPositionConstant n / (n + 1 : ℝ)) *
        Real.exp (hypersurfaceSmallHeightError (n + 1)
          (hypersurfaceBadPrimeNormalizedError n)) := by positivity
    linarith
  apply one_le_mul_of_one_le_of_one_le (by linarith)
  have := Real.exp_pos ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
  linarith

/-- CCDN Theorem 3.1.1: the full coefficient-sensitive auxiliary-polynomial
bound, including equations that split over an algebraic closure. -/
theorem hypersurface_projective_auxiliary
    {n d : ℕ} (f : CCDN.IntegerPolynomial (n + 3))
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ M : ℕ,
      ↑M ≤ hypersurfaceAuxiliaryDegreeBound n d B (hypersurfaceBadPrimeFactor f)
        (integerCoefficientHeight f) ∧
      ∃ g : CCDN.IntegerPolynomial (n + 3), g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (CCDN.rationalPolynomial f) →
          x ∈ projectiveZeroLocus (CCDN.rationalPolynomial g)) ∧ ¬ f ∣ g := by
  classical
  by_cases habs : AbsolutelyIrreducible f
  · obtain ⟨bad, M, hbad, hdegree, hg⟩ := hypersurface_absolute_projective_auxiliary f hf hd habs hB
    refine ⟨M, hdegree.trans_eq ?_, hg⟩
    rw [hypersurfaceBadPrimeFactor_eq_exp f habs (hf.totalDegree hir.ne_zero) bad hbad]
  · have hQ := rational_map_irreducible_of_integer f hir
      (by rw [hf.totalDegree hir.ne_zero]; exact hd)
    have hred :=
      (absolutelyIrreducibleRat_map_iff f).not.mpr habs
    obtain ⟨g, _, hgh, hgnd, hzeros⟩ := nonabsolute_projective_auxiliary f hf hQ hred
    refine ⟨d, ?_, g, hgh, fun x _ hx => hzeros hx, hgnd⟩
    unfold hypersurfaceAuxiliaryDegreeBound auxDegreeBound auxMainTerm
    rw [hypersurfaceBadPrimeFactor_eq_zero f habs, mul_zero, zero_mul, zero_div, zero_add]
    have hdD : ↑d ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
    have hl : 0 ≤ ↑d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg hB)
    exact (hdD.trans (le_add_of_nonneg_left hl)).trans
      (le_mul_of_one_le_left (by positivity) (hypersurfaceAbsoluteAuxiliaryConstant_one_le n))

end CCDN
