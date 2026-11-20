/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.AuxiliaryPolynomial.HypersurfaceNonabsoluteAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceProjectiveAuxiliary

/-! CCDN Theorem 3.1.1 for irreducible integer homogeneous equations.
The constant is fixed before the equation, degree and radius are chosen. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN Theorem 3.1.1: the full coefficient-sensitive auxiliary-polynomial
bound, including equations that split over an algebraic closure. -/
theorem hypersurface_projective_auxiliary
    {n d : ℕ} (f : IntegerPolynomial (n + 3))
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (hypersurfaceBadPrimeFactor f)
        (integerCoefficientHeight f) ∧
      ∃ g : IntegerPolynomial (n + 3), g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (rationalEquation f) →
          x ∈ projectiveZeroLocus (rationalEquation g)) ∧ ¬ f ∣ g := by
  classical
  by_cases habs : AbsolutelyIrreducible f
  · obtain ⟨bad, M, hbad, hdegree, hg⟩ := hypersurface_absolute_projective_auxiliary f hf hd habs hB
    refine ⟨M, hdegree.trans_eq ?_, hg⟩
    rw [hypersurfaceBadPrimeFactor_eq_exp f habs (hf.totalDegree hir.ne_zero) bad hbad]
  · have hQ := rational_map_irreducible_of_integer f hir
      (by simp_all [hf.totalDegree hir.ne_zero])
    obtain ⟨g, hg0, hgh, hgnd, hzeros⟩ := nonabsolute_projective_auxiliary f hf hd hQ ((absolutelyIrreducibleRat_map_iff f).not.mpr habs)
    refine ⟨d, ?_, g, hg0, hgh, fun x _ hx => hzeros hx, hgnd⟩
    unfold hypersurfaceAuxiliaryDegreeBound auxDegreeBound auxMainTerm
    rw [hypersurfaceBadPrimeFactor_eq_zero f habs, mul_zero, zero_mul, zero_div, zero_add]
    have hdD : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
    have hl : 0 ≤ (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B :=
      by bound
    exact (hdD.trans (le_add_of_nonneg_left hl)).trans
      (by grind [le_mul_of_one_le_left, hypersurfaceAbsoluteAuxiliaryConstant_one_le])

end
end CCDN
