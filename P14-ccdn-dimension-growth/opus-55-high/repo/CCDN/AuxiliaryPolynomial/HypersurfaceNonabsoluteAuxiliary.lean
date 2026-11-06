/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.HomogeneousLinearDescent
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! A degree-d auxiliary equation for nonabsolute irreducible hypersurfaces.
Linear descent of the two homogeneous factors suffices over any extension. -/

namespace CCDN
section
open MvPolynomial

/-- Over an arbitrary field extension, descent of a proper factorization
produces a degree-d nonmultiple vanishing at all base-field zeros. -/
theorem nonabsolute_homogeneous_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n d : ℕ}
    (f : MvPolynomial (Fin n) k) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k, q ≠ 0 ∧ q.IsHomogeneous d ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  obtain ⟨g, h, hfac, hg0, hh0, hgd, hhd, -⟩ :=
    exists_map_factorization (hf.totalDegree hir.ne_zero ▸ hd) hred
  obtain ⟨hdegrees, htop⟩ :=
    homogeneous_factorization_top (hf.map _) (hfac ▸ mul_ne_zero hg0 hh0) hg0 hh0 hfac
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
    rcases mul_eq_zero.mp he with hgzero | hhzero
    · grind
    grind

variable {K : Type*} [Field K] [Algebra ℚ K] {n d : ℕ}

/-- Integer denominator clearing preserves the exact degree and all rational
zeros. Irreducibility is stated over Q, and splitting may occur over any extension. -/
theorem integer_nonabsolute_homogeneous_auxiliary
    (f : MvPolynomial (Fin n) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin n) ℤ, g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      ∀ x : Fin n → ℚ, eval x (map (Int.castRingHom ℚ) f) = 0 →
        eval x (map (Int.castRingHom ℚ) g) = 0 := by
  obtain ⟨q, hq0, hqh, hqnd, hqzero⟩ := nonabsolute_homogeneous_auxiliary
    (map (Int.castRingHom ℚ) f) (hf.map _) hd hir hred
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model q hq0
  refine ⟨g, rational_scalar_model_homogeneous he hqh, ?_, ?_⟩
  · intro hdiv
    have hh := dvd_mul_of_dvd_right (map_dvd (map (Int.castRingHom ℚ)) hdiv) (C a⁻¹)
    simp_all
  · grind

/-- CCDN Lemma 3.3.1 for all rational projective zeros, independently of height. -/
theorem nonabsolute_projective_auxiliary
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      projectiveZeroLocus (map (Int.castRingHom ℚ) f) ⊆
        projectiveZeroLocus (map (Int.castRingHom ℚ) g) := by
  obtain ⟨g, hgh, hgnd, hz⟩ := integer_nonabsolute_homogeneous_auxiliary f hf hd hir hred
  exact ⟨g, hgh, hgnd, fun x hx => hz x.rep hx⟩

