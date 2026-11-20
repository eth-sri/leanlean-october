/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Coefficientwise application of a linear map to multivariate polynomials, and
linear coefficient descent of a polynomial over a field extension: a nonzero
polynomial vanishing at base-field points has a nonzero base-field polynomial of no
larger degree vanishing at every one of those points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Module

private def coefficientDescent {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    (φ : K →ₗ[k] k) : MvPolynomial σ K →ₗ[k] MvPolynomial σ k :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap φ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

section

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]
  (φ : K →ₗ[k] k) (f : MvPolynomial σ K)

private lemma coefficientDescent_coeff (m : σ →₀ ℕ) :
    (coefficientDescent φ f).coeff m = φ (f.coeff m) := rfl

private lemma coefficientDescent_support : (coefficientDescent φ f).support ⊆ f.support := by
  intro m hm
  simp only [mem_support_iff, coefficientDescent_coeff] at hm ⊢
  exact fun h => hm (by simp [h])

private lemma coefficientDescent_eval (x : σ → k) :
    eval x (coefficientDescent φ f) = φ (eval (algebraMap k K ∘ x) f) := by
  classical
  rw [eval_eq, eval_eq, map_sum, Finset.sum_subset (coefficientDescent_support φ f)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [coefficientDescent_coeff, Function.comp_apply, ← map_pow, ← map_prod]
    rw [mul_comm (f.coeff m), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  · intro m _ hm
    simp [notMem_support_iff.mp hm]

end

/-- Linear descent reduces the support and preserves vanishing at base-field points. -/
theorem exists_nonzero_polynomial_linear_descent {k K σ : Type*}
    [Field k] [Field K] [Algebra k K] (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ g : MvPolynomial σ k, g ≠ 0 ∧ g.totalDegree ≤ f.totalDegree ∧
      (∀ d, f.IsHomogeneous d → g.IsHomogeneous d) ∧
      ∀ x : σ → k, eval (algebraMap k K ∘ x) f = 0 → eval x g = 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  have hs := coefficientDescent_support φ f
  refine ⟨coefficientDescent φ f, ?_, Finset.sup_mono hs, fun _ h _ hm => h (mem_support_iff.mp (hs (mem_support_iff.mpr hm))), ?_⟩
  · intro he
    exact hφ (by simpa [he] using (coefficientDescent_coeff φ f m).symm)
  · intro x hx
    rw [coefficientDescent_eval, hx, map_zero]

end
end CCDN
