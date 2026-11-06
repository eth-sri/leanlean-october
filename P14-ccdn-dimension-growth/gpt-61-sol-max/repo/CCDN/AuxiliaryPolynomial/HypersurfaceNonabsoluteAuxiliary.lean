/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.HomogeneousLinearDescent
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! A degree-d auxiliary equation for nonabsolute irreducible hypersurfaces.
Linear descent of the two homogeneous factors suffices over any extension. -/

public section
namespace CCDN
open MvPolynomial

/-- Over an arbitrary field extension, descent of a proper factorization
produces a degree-d nonmultiple vanishing at all base-field zeros. -/
private theorem nonabsolute_homogeneous_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n d : ℕ}
    (f : MvPolynomial (Fin n) k) (hf : f.IsHomogeneous d)
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k, q ≠ 0 ∧ q.IsHomogeneous d ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  obtain ⟨g, h, hfac, hg0, hh0, hgd, hhd⟩ := exists_proper_polynomial_factors f hir hred
  have hmap0 : map (algebraMap k K) f ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero hg0 hh0
  obtain ⟨hdegrees, htop⟩ := homogeneous_factorization_top (hf.map _) hmap0 hg0 hh0 hfac
  obtain ⟨g₀, hg₀, hg₀hom, hgz⟩ := exists_nonzero_homogeneous_linear_descent (k := k)
    (homogeneousComponent g.totalDegree g) (homogeneousComponent_totalDegree_ne_zero hg0)
    (homogeneousComponent_isHomogeneous _ _)
  obtain ⟨h₀, hh₀, hh₀hom, hhz⟩ := exists_nonzero_homogeneous_linear_descent (k := k)
    (homogeneousComponent h.totalDegree h) (homogeneousComponent_totalDegree_ne_zero hh0)
    (homogeneousComponent_isHomogeneous _ _)
  refine ⟨g₀ * h₀, mul_ne_zero hg₀ hh₀, hdegrees ▸ hg₀hom.mul hh₀hom, ?_, ?_⟩
  · intro hdiv
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      rw [hf.totalDegree hir.ne_zero, hg₀hom.totalDegree hg₀] at he
      omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      rw [hf.totalDegree hir.ne_zero, hh₀hom.totalDegree hh₀] at he
      omega
  · intro x hx
    have he := congrArg (algebraMap k K) hx
    rw [map_eval, htop, eval_mul, map_zero] at he
    rw [eval_mul]
    rcases mul_eq_zero.mp he with hgzero | hhzero
    · rw [hgz x hgzero, zero_mul]
    · rw [hhz x hhzero, mul_zero]

variable {K : Type*} [Field K] [Algebra ℚ K] {n d : ℕ}

/-- Integer denominator clearing preserves the exact degree and all rational
zeros. Irreducibility is stated over Q, and splitting may occur over any extension. -/
theorem integer_nonabsolute_homogeneous_auxiliary 
    (f : CCDN.IntegerPolynomial n) (hf : f.IsHomogeneous d)
    (hir : Irreducible (CCDN.rationalPolynomial f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (CCDN.rationalPolynomial f))) :
    ∃ g : CCDN.IntegerPolynomial n, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      ∀ x : CCDN.RatPoint n, eval x (CCDN.rationalPolynomial f) = 0 →
        eval x (CCDN.rationalPolynomial g) = 0 := by
  obtain ⟨q, hq0, hqh, hqnd, hqzero⟩ := nonabsolute_homogeneous_auxiliary
    (CCDN.rationalPolynomial f) (hf.map _) hir hred
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model q hq0
  have hg0 : g ≠ 0 := by
    aesop
  refine ⟨g, hg0, rational_scalar_model_homogeneous he hqh, ?_, ?_⟩
  · intro hdiv
    apply hqnd
    have hh := dvd_mul_of_dvd_right (map_dvd (CCDN.rationalPolynomial) hdiv) (C a⁻¹)
    simpa only [he, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul] using hh
  · simp_all

/-- CCDN Lemma 3.3.1 for all rational projective zeros, independently of height. -/
theorem nonabsolute_projective_auxiliary 
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d)
    (hir : Irreducible (CCDN.rationalPolynomial f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (CCDN.rationalPolynomial f))) :
    ∃ g : CCDN.IntegerPolynomial (n + 1), g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      projectiveZeroLocus (CCDN.rationalPolynomial f) ⊆
        projectiveZeroLocus (CCDN.rationalPolynomial g) := by
  obtain ⟨g, hg0, hgh, hgnd, hz⟩ := integer_nonabsolute_homogeneous_auxiliary f hf hir hred
  exact ⟨g, hg0, hgh, hgnd, fun x hx => hz x.rep hx⟩

end CCDN
