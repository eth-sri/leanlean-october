/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.AuxiliaryPolynomial.HypersurfaceNonabsoluteAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceProjectiveAuxiliary

/-! CCDN Theorem 3.1.1 for irreducible integer homogeneous equations.
The constant is fixed before the equation, degree and radius are chosen. -/

namespace CCDN
section
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
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  unfold hypersurfaceAbsoluteAuxiliaryConstant
  apply one_le_mul_of_one_le_of_one_le (by linarith)
  have := Real.exp_pos ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- CCDN Theorem 3.1.1: the full coefficient-sensitive auxiliary-polynomial
bound, including equations that split over an algebraic closure. -/
theorem hypersurface_projective_auxiliary
    {n d : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (hypersurfaceBadPrimeFactor f)
        (integerCoefficientHeight f) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  by_cases habs : AbsolutelyIrreducible f
  · let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
    let e := (Fintype.equivFin S).symm
    let z := fun i => primitiveProjectiveRep (e i).val
    have hprim (i) : Finset.univ.gcd (z i) = 1 := primitiveProjectiveRep_gcd _
    have hz (i) : eval (z i) f = 0 :=
      (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2
    have hf0 := ne_zero_of_irreducible_map habs
    obtain ⟨bad, hbad⟩ := exists_hypersurface_bad_prime_finset f hf hd habs
    obtain ⟨M, hM, g, hg⟩ := absolute_auxiliary_degree_of_comparison f hf hd habs
      ⟨⟨hB, hz, fun i j => (primitiveProjectiveRep_bound _ j).trans
        (mem_projectivePoints.mp (e i).property).1⟩, hprim⟩ bad
      (fun a => hypersurface_auxiliaryRankComparison MonomialOrder.lex _
        (homogeneousTranslation_homogeneous a hf)
        ((homogeneousTranslation ℤ a).injective.ne (by positivity)) hd _
        (fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i))
        (fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i)) bad
        fun p => by rw [hbad, hypersurfaceBadReduction_homogeneousTranslation f hf hf0])
    obtain ⟨-, hgh, hgz, hgnd⟩ := isPointAuxiliary_iff.mp hg
    refine ⟨M, hM.trans_eq ?_, g, hgh, fun x hxB hxf => ?_, hgnd⟩
    · rw [hypersurfaceBadPrimeFactor_eq_exp f habs (hf.totalDegree hir.ne_zero) bad hbad]
    obtain ⟨i, hi⟩ := e.surjective ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
    have hh : eval (primitiveProjectiveRep (e i).val) g = 0 := hgz i
    rw [hi] at hh
    exact (mem_integer_projectiveZeroLocus hgh x).mpr hh
  · have hQ := rational_map_irreducible_of_integer f hir
      (by rw [hf.totalDegree hir.ne_zero]; exact hd)
    have hred :=
      (absolutelyIrreducibleRat_map_iff f).not.mpr habs
    obtain ⟨g, hgh, hgnd, hzeros⟩ := nonabsolute_projective_auxiliary f hf hd hQ hred
    refine ⟨d, ?_, g, hgh, fun x _ hx => hzeros hx, hgnd⟩
    unfold hypersurfaceAuxiliaryDegreeBound auxDegreeBound auxMainTerm
    rw [hypersurfaceBadPrimeFactor_eq_zero f habs, mul_zero, zero_mul, zero_div, zero_add]
    have hdD : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
    have hl : 0 ≤ d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg hB)
    exact (hdD.trans (le_add_of_nonneg_left hl)).trans
      (le_mul_of_one_le_left (by positivity) (hypersurfaceAbsoluteAuxiliaryConstant_one_le n))

