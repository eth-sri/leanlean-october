/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.ForMathlib.MvPolynomialDerivative
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Constant and first coefficients of an equation under a linear
one-parameter displacement of one coordinate. These are algebraic coefficient
identities, valid for arbitrary commutative target algebras. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma polynomial_coeff_one_chain {K A σ : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [Fintype σ] (ψ : MvPolynomial σ K →ₐ[K] Polynomial A)
    (f : MvPolynomial σ K) :
    (ψ f).coeff 1 = ∑ i, (ψ (pderiv i f)).coeff 0 * (ψ (X i)).coeff 1 := by
  have h := congrArg (fun p : Polynomial A => p.coeff 0)
    (derivation_algHom (Polynomial.derivative'.restrictScalars K) ψ f)
  simpa [Polynomial.coeff_derivative] using h

/-- Vary one coordinate by `t*w` in an arbitrary target algebra. -/
def linearDeformation {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A] [DecidableEq σ]
    (a : σ → A) (k : σ) (w : A) : MvPolynomial σ K →ₐ[K] Polynomial A :=
  aeval (fun j => Polynomial.C (a j) + if j = k then Polynomial.X * Polynomial.C w else 0)

section

variable {K A σ : Type*} [DecidableEq σ] [CommRing K] [CommRing A]
  [Algebra K A] (a : σ → A) (k : σ) (w : A)
  (f : MvPolynomial σ K)
include K A σ a k w f

lemma linearDeformation_eval (t : A) :
    (linearDeformation a k w f).eval t = aeval (fun j => a j + if j = k then t * w else 0) f := by
  let E := (Polynomial.aeval (R := A) t).restrictScalars K
  change E (aeval _ f) = _
  rw [comp_aeval_apply]
  congr 2
  funext j
  by_cases h : j = k <;> simp [E, h]; ring

/-- The constant coefficient of the linear deformation of `f` at `a` is the value `f(a)`. -/
lemma linearDeformation_coeff_zero :
    (linearDeformation a k w f).coeff 0 = aeval a f := by
  simp [Polynomial.coeff_zero_eq_eval_zero, linearDeformation_eval]

/-- The linear coefficient of the deformation of `f` at `a` along coordinate `k` with speed `w` is
`(∂f/∂x_k)(a) * w`. -/
lemma linearDeformation_coeff_one [Fintype σ] :
    (linearDeformation a k w f).coeff 1 = aeval a (pderiv k f) * w := by
  rw [polynomial_coeff_one_chain]
  simp_rw [linearDeformation_coeff_zero]
  rw [Finset.sum_eq_single k]
  · simp [linearDeformation, Polynomial.mul_coeff_one]
  · intro j _ hj
    simp [linearDeformation, hj]
  · simp

end

end
end CCDN
