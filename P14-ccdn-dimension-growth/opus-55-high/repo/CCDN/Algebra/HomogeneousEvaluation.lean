/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousMonomials
import CCDN.Algebra.RowSelection

/-! Homogeneous equations give nonzero relations on the complete
homogeneous evaluation matrix and hence strictly deficient row rank. -/

namespace CCDN
section
open MvPolynomial Matrix

section
variable {n M : ℕ}

/-- A homogeneous polynomial of degree `M` in `n + 1` variables is the sum of its terms over
the degree-`M` monomials enumerated by `homogeneousMonomials n M`. -/
lemma homogeneous_eq_sum_coeff {K : Type*} [CommSemiring K]
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    f = ∑ j, monomial (homogeneousMonomials n M j) (f.coeff (homogeneousMonomials n M j)) := by
  ext p
  by_cases hp : p.degree = M
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n M p hp
    simp [coeff_monomial, (homogeneousMonomials_injective n M).eq_iff]
  · have hc := hf.coeff_eq_zero hp
    simp_all

lemma homogeneous_coefficients_ne_zero
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous M) (hf0 : f ≠ 0) :
    (fun j => f.coeff (homogeneousMonomials n M j)) ≠ 0 := by
  intro h
  apply hf0
  rw [homogeneous_eq_sum_coeff f hf]
  have hz : ∀ j, f.coeff (homogeneousMonomials n M j) = 0 := fun j => congrFun h j
  simp [hz, monomial_zero, Finset.sum_const_zero]

end

/-- Select a spanning family of independent evaluation rows. The
homogeneous equation, padded to degree `M`, proves strict rank deficiency. -/
theorem homogeneous_independent_evaluation_rows {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t),
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      Submodule.span ℚ (Set.range
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row) =
      Submodule.span ℚ (Set.range
        ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)).row) ∧
      s < (n + M).choose M := by
  let F := f * X (0 : Fin (n + 1)) ^ (M - d)
  have hF : F.IsHomogeneous M := by
    simpa [Nat.add_sub_of_le hdM] using hf.mul (isHomogeneous_X_pow (0 : Fin (n + 1)) (M - d))
  have hFzero : ∀ i, eval (points i) F = 0 := by grind
  let v := fun j => F.coeff (homogeneousMonomials n M j)
  have hk : evaluationMatrix (homogeneousMonomials n M) points *ᵥ
      (fun j => F.coeff (homogeneousMonomials n M j)) = 0 := by
    have he : polynomialOfCoefficients (homogeneousMonomials n M)
        (fun j => F.coeff (homogeneousMonomials n M j)) = F :=
      (homogeneous_eq_sum_coeff F hF).symm
    ext i
    rw [← eval_polynomialOfCoefficients, he]
    exact hFzero i
  have hkQ : ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)) *ᵥ
      (fun j => (v j : ℚ)) = 0 := by
    ext i
    have hi := congrFun hk i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hi ⊢
    exact_mod_cast hi
  obtain ⟨s, a, hli, hspan, hs⟩ := exists_independent_spanning_rows_lt _ _ (by
    intro h
    apply homogeneous_coefficients_ne_zero F hF (mul_ne_zero hf0 (pow_ne_zero _ (X_ne_zero _)))
    funext j
    have hj := congrFun h j
    change (v j : ℚ) = 0 at hj
    exact_mod_cast hj) hkQ
  exact ⟨s, a, hli, hspan, hs⟩

