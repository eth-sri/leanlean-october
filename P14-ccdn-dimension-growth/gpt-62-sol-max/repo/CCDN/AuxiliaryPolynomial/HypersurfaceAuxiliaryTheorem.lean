/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

/-- The constant `hypersurfaceAbsoluteAuxiliaryConstant n` is at least `1`. -/
lemma hypersurfaceAbsoluteAuxiliaryConstant_one_le (n : ℕ) :
    1 ≤ hypersurfaceAbsoluteAuxiliaryConstant n := by
  unfold hypersurfaceAbsoluteAuxiliaryConstant hypersurfacePositionedAuxiliaryConstant
  apply one_le_mul_of_one_le_of_one_le
  · have hA : 0 ≤ positionedLargeFactor n (hypersurfaceAuxiliaryPositionConstant n) :=
      (Real.exp_pos _).le
    have hS : 0 ≤ positionedSmallFactor n (hypersurfaceAuxiliaryPositionConstant n) :=
      (Real.exp_pos _).le
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · linarith [Real.exp_pos ((n + 2 : ℝ) / (n + 1 : ℝ) * (n + 2 : ℝ)), Nat.cast_nonneg (α := ℝ) n]

/-- CCDN Theorem 3.1.1: the full coefficient-sensitive auxiliary-polynomial
bound, including equations that split over an algebraic closure. -/
theorem hypersurface_projective_auxiliary
    {n d : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (hypersurfaceBadPrimeFactor f)
        (integerCoefficientHeight f) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  classical
  by_cases habs : AbsolutelyIrreducible f
  · obtain ⟨bad, M, hbad, hdegree, hg⟩ := hypersurface_absolute_projective_auxiliary f hf hd habs hB
    refine ⟨M, hdegree.trans_eq ?_, hg⟩
    rw [hypersurfaceBadPrimeFactor_eq_exp f habs (hf.totalDegree hir.ne_zero) bad hbad]
  · have hQ := rational_map_irreducible_of_integer f hir
      (by rw [hf.totalDegree hir.ne_zero]; exact hd)
    have hred : ¬ AbsolutelyIrreducibleRat (map (Int.castRingHom ℚ) f) :=
      (absolutelyIrreducibleRat_map_iff f).not.mpr habs
    obtain ⟨g, hg0, hgh, hgnd, hzeros⟩ := nonabsolute_projective_auxiliary f hf hQ hred
    refine ⟨d, ?_, g, hg0, hgh, fun x _ hx => hzeros hx, hgnd⟩
    unfold hypersurfaceAuxiliaryDegreeBound auxDegreeBound auxMainTerm
    rw [hypersurfaceBadPrimeFactor_eq_zero f habs, zero_div, mul_zero, zero_add]
    have hl : 0 ≤ auxLogTerm n d B := by have := Real.log_nonneg hB; positivity
    exact ((le_auxDegreeScale hd).trans (le_add_of_nonneg_left hl)).trans
      (le_mul_of_one_le_left (by positivity) (hypersurfaceAbsoluteAuxiliaryConstant_one_le n))

end
end CCDN
