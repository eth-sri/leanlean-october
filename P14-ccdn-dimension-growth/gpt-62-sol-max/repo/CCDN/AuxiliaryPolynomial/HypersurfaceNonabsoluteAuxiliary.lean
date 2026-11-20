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

section

variable {K : Type*}
  [Field K] [Algebra ℚ K] {n d : ℕ}
include K n d

/-- Integer denominator clearing preserves the exact degree and all rational
zeros. Irreducibility is stated over Q, and splitting may occur over any extension. -/
theorem integer_nonabsolute_homogeneous_auxiliary
    (f : MvPolynomial (Fin n) ℤ) (hf : f.IsHomogeneous d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin n) ℤ, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      ∀ x : Fin n → ℚ, eval x (map (Int.castRingHom ℚ) f) = 0 →
        eval x (map (Int.castRingHom ℚ) g) = 0 := by
  obtain ⟨q, hq0, _, hqnd, hqh, hqzero⟩ := nonabsolute_auxiliary _ hir hred
  obtain ⟨g, ha⟩ := exists_integer_model q
  refine ⟨g, (fun hz => hq0 (ha.eq_zero_iff.mpr (by simp [hz]))), rational_model_homogeneous ha (hqh d (hf.map _)), ?_, ?_⟩
  · exact fun hdvd => hqnd ((map_dvd (map (Int.castRingHom ℚ)) hdvd).trans ha.dvd')
  · exact fun x hx => (rational_model_zero_iff ha x).mpr (hqzero x hx)

/-- CCDN Lemma 3.3.1 for all rational projective zeros, independently of height. -/
theorem nonabsolute_projective_auxiliary
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      projectiveZeroLocus (map (Int.castRingHom ℚ) f) ⊆
        projectiveZeroLocus (map (Int.castRingHom ℚ) g) := by
  obtain ⟨g, hg0, hgh, hgnd, hz⟩ := integer_nonabsolute_homogeneous_auxiliary f hf hir hred
  exact ⟨g, hg0, hgh, hgnd, fun x hx => hz x.rep hx⟩

end

end
end CCDN
