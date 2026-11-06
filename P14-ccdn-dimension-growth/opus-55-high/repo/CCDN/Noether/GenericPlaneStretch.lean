/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import CCDN.Algebra.PolynomialPrimeLocalization
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Monic

/-! Ordinary irreducibility of the generic stretching substitution
f(x,z) -> f(x,y*z). The fresh variable y is first made invertible; scaling
then becomes a polynomial automorphism. Monicity in x descends irreducibility
back to the polynomial coefficient ring. -/

namespace CCDN
noncomputable section
open MvPolynomial

lemma optionEquivLeft_map_coefficients {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Option σ) R) :
    optionEquivLeft S σ (MvPolynomial.map φ f) =
      Polynomial.map (MvPolynomial.map φ) (optionEquivLeft R σ f) := by
  have he : (optionEquivLeft S σ).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom (MvPolynomial.map φ)).comp (optionEquivLeft R σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · simp_all
    · intro i
      cases i <;> simp
  exact RingHom.congr_fun he f

/-- Simultaneously multiply all polynomial variables by a nonzero scalar. -/
def variableScaleEquiv (K σ : Type*) [Field K] (a : K) (ha : a ≠ 0) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (aeval (fun i => C a * X i))
    (aeval (fun i => C a⁻¹ * X i))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
      simp only [map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
      simp only [map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul])

/-- The scaling automorphism by `a` sends each variable `X i` to `a * X i`. -/
@[simp] lemma variableScaleEquiv_X {K σ : Type*} [Field K]
    (a : K) (ha : a ≠ 0) (i : σ) :
    variableScaleEquiv K σ a ha (X i) = C a * X i := by
  simp [variableScaleEquiv]

/-- Introduce a fresh polynomial parameter and scale each transverse variable
by that parameter, keeping the distinguished outer variable fixed. -/
def genericStretchCoefficients (K σ : Type*) [Field K] :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ (MvPolynomial Unit K) :=
  aeval (fun i => C (X ()) * X i)

variable {K σ : Type*} [Field K] (f : MvPolynomial (Option σ) K)

/-- The generic stretch `f(x, z) ↦ f(x, y * z)` of `f`, viewed as a polynomial in the distinguished
outer variable `x` whose coefficients involve the transverse variables `z` and the fresh
parameter `y`. -/
def genericPlaneStretch
    :
    Polynomial (MvPolynomial σ (MvPolynomial Unit K)) :=
  Polynomial.map (genericStretchCoefficients K σ).toRingHom (optionEquivLeft K σ f)

