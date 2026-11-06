/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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

/-- CCDN Lemma 3.3.1 for all rational projective zeros, independently of height. -/
theorem nonabsolute_projective_auxiliary {K : Type*}
    [Field K] [Algebra ℚ K] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      projectiveZeroLocus (map (Int.castRingHom ℚ) f) ⊆
        projectiveZeroLocus (map (Int.castRingHom ℚ) g) := by
  /- Integer denominator clearing preserves the exact degree and all rational
  zeros. Irreducibility is stated over Q, and splitting may occur over any extension. -/
  let fQ := map (Int.castRingHom ℚ) f
  have hfQ : fQ.IsHomogeneous d := hf.map _
  have hmap0 : map (algebraMap ℚ K) fQ ≠ 0 := fun he =>
    hir.ne_zero ((map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective) (by simpa using he))
  have hmapu : ¬ IsUnit (map (algebraMap ℚ K) fQ) := fun hu => by
    have he := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [(hfQ.map _).totalDegree hmap0] at he; omega
  have hfac : ∃ g h : MvPolynomial (Fin (n + 1)) K,
      map (algebraMap ℚ K) fQ = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    classical
    by_contra! hn
    exact hred ⟨hmapu, fun g h he => if hu : IsUnit g then Or.inl hu else Or.inr (hn g h he hu)⟩
  obtain ⟨gK, hK, hfac, hgu, hhu⟩ := hfac
  have hgK0 : gK ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hhK0 : hK ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hgd := totalDegree_pos_of_ne_zero_of_not_isUnit hgK0 hgu
  have hhd := totalDegree_pos_of_ne_zero_of_not_isUnit hhK0 hhu
  obtain ⟨hdegrees, htop⟩ := homogeneous_factorization_top (hfQ.map _) hmap0 hgK0 hhK0 hfac
  obtain ⟨g₀, hg₀, hg₀hom, hgz⟩ := exists_nonzero_homogeneous_linear_descent (k := ℚ)
    (homogeneousComponent gK.totalDegree gK) (homogeneousComponent_totalDegree_ne_zero hgK0)
    (homogeneousComponent_isHomogeneous _ _)
  obtain ⟨h₀, hh₀, hh₀hom, hhz⟩ := exists_nonzero_homogeneous_linear_descent (k := ℚ)
    (homogeneousComponent hK.totalDegree hK) (homogeneousComponent_totalDegree_ne_zero hhK0)
    (homogeneousComponent_isHomogeneous _ _)
  let q := g₀ * h₀
  have hq0 : q ≠ 0 := mul_ne_zero hg₀ hh₀
  have hqh : q.IsHomogeneous d := hdegrees ▸ hg₀hom.mul hh₀hom
  have hqnd : ¬ fQ ∣ q := fun hdiv => by
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      rw [hfQ.totalDegree hir.ne_zero, hg₀hom.totalDegree hg₀] at he; omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      rw [hfQ.totalDegree hir.ne_zero, hh₀hom.totalDegree hh₀] at he; omega
  obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model q hq0
  have hg0 : g ≠ 0 := fun hz =>
    mul_ne_zero (C_eq_zero.not.mpr ha) hq0 (by simpa only [hz, map_zero] using he.symm)
  refine ⟨g, hg0, rational_scalar_model_homogeneous he hqh, fun hdiv => hqnd ?_, fun x hx => ?_⟩
  · simpa only [he, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul] using
      dvd_mul_of_dvd_right (map_dvd (map (Int.castRingHom ℚ)) hdiv) (C a⁻¹)
  · refine (rational_scalar_model_zero_iff ha he x.rep).mpr ?_
    have hev := congrArg (algebraMap ℚ K) hx
    rw [map_eval, htop, eval_mul, map_zero] at hev
    dsimp [q]; rw [eval_mul]
    rcases mul_eq_zero.mp hev with hgzero | hhzero
    · rw [hgz x.rep hgzero, zero_mul]
    · rw [hhz x.rep hhzero, mul_zero]

end
end CCDN
