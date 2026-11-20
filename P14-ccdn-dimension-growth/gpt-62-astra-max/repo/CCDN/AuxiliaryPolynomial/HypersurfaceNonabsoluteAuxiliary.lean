/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.HomogeneousLinearDescent
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! A degree-d auxiliary equation for nonabsolute irreducible hypersurfaces.
Linear descent of the two homogeneous factors suffices over any extension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Over an arbitrary field extension, descent of a proper factorization
produces a degree-d nonmultiple vanishing at all base-field zeros. -/
private theorem nonabsolute_homogeneous_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n d : ℕ}
    (f : MvPolynomial (Fin n) k) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k, q ≠ 0 ∧ q.IsHomogeneous d ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  have hmap0 := by
    exact fun he => hir.ne_zero ((map_injective (algebraMap k K) (algebraMap k K).injective)
      (by simpa using he))
  have hmapu : ¬ IsUnit (map (algebraMap k K) f) := by
    intro hu
    have he := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    simp_all [(hf.map _).totalDegree hmap0]
  have hfac : ∃ g h : MvPolynomial (Fin n) K,
      map (algebraMap k K) f = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! hn
    apply hred
    refine ⟨hmapu, ?_⟩
    grind
  obtain ⟨g, h, hfac, hgu, hhu⟩ := hfac
  have hg0 : g ≠ 0 := by grind
  have hh0 : h ≠ 0 := by grind
  have hgd := totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
  have hhd := totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
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
    rcases mul_eq_zero.mp he with hgzero | hhzero
    simp_all
    simp_all

variable {K : Type*} [Field K] [Algebra ℚ K] {n d : ℕ}

/-- Integer denominator clearing preserves the exact degree and all rational
zeros. Irreducibility is stated over Q, and splitting may occur over any extension. -/
theorem integer_nonabsolute_homogeneous_auxiliary
    (f : IntegerPolynomial n) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (rationalEquation f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (rationalEquation f))) :
    ∃ g : IntegerPolynomial n, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      ∀ x : Fin n → ℚ, eval x (rationalEquation f) = 0 →
        eval x (rationalEquation g) = 0 := by
  obtain ⟨q, hq0, hqh, hqnd, hqzero⟩ := nonabsolute_homogeneous_auxiliary
    (rationalEquation f) (hf.map _) hd hir hred
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model q hq0
  have hg0 : g ≠ 0 := by
    intro hz
    aesop
  refine ⟨g, hg0, rational_scalar_model_homogeneous he hqh, ?_, ?_⟩
  · intro hdiv
    apply hqnd
    simpa only [he, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul] using (dvd_mul_of_dvd_right (map_dvd (rationalEquation) hdiv) (C a⁻¹))
  aesop

/-- CCDN Lemma 3.3.1 for all rational projective zeros, independently of height. -/
theorem nonabsolute_projective_auxiliary
    (f : IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (rationalEquation f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (rationalEquation f))) :
    ∃ g : IntegerPolynomial (n + 1), g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      projectiveZeroLocus (rationalEquation f) ⊆
        projectiveZeroLocus (rationalEquation g) := by
  obtain ⟨g, hg0, hgh, hgnd, hz⟩ := integer_nonabsolute_homogeneous_auxiliary f hf hd hir hred
  exact ⟨g, hg0, hgh, hgnd, fun x hx => hz x.rep hx⟩

end
end CCDN
