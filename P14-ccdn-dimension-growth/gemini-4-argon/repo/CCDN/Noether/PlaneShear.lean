/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Fin.VecNotation
import CCDN.Noether.BivariateTotalDegree

/-! Integral plane shears are polynomial-ring automorphisms in every
characteristic. They will place the highest-degree part in the outer variable. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Fix variable zero and replace variable one by x₁+a*x₀. -/
def planeShearHom (R : Type*) [CommRing R] (a : R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![X 0, X 1 + C a * X 0]

/-- The plane shear `x₁ ↦ x₁ + a * x₀` as an algebra automorphism. The inverse shear uses the
negative parameter, so this works over Z and all its residue fields without determinant
denominators. -/
def planeShear (R : Type*) [CommRing R] (a : R) :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  /- Composing the plane shears with parameters `a` and `b` gives the shear with parameter
  `a + b`. -/
  /- The plane shear with parameter zero is the identity. -/
  AlgEquiv.ofAlgHom (planeShearHom R a) (planeShearHom R (-a))
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp [planeShearHom])
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp [planeShearHom])

/-- A plane shear preserves the total degree; the inverse shear gives the reverse inequality. -/
lemma planeShear_totalDegree {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) (f : MvPolynomial (Fin 2) R) :
    (planeShear R a f).totalDegree = f.totalDegree := by
  classical
  have hle (b : R) (g : MvPolynomial (Fin 2) R) :
      (planeShear R b g).totalDegree ≤ g.totalDegree := by
    have hx : (X 1 + C b * X 0 : MvPolynomial (Fin 2) R).totalDegree ≤ 1 :=
      (totalDegree_add _ _).trans (max_le (by simp)
        (by simpa using totalDegree_mul (C b : MvPolynomial (Fin 2) R) (X 0)))
    conv_lhs => rw [g.as_sum, map_sum]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
    have hmono : planeShear R b (monomial m (g.coeff m)) =
        C (g.coeff m) * (X 0) ^ m 0 * (X 1 + C b * X 0) ^ m 1 := by
      change aeval ![X 0, X 1 + C b * X 0] (monomial m (g.coeff m)) = _
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [algebraMap_eq, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
    rw [hmono]
    have h₁ := totalDegree_mul (C (g.coeff m) : MvPolynomial (Fin 2) R) ((X 0) ^ m 0)
    have h₂ := totalDegree_mul (C (g.coeff m) * (X 0) ^ m 0 : MvPolynomial (Fin 2) R)
      ((X 1 + C b * X 0) ^ m 1)
    have h₃ := (totalDegree_pow (X 1 + C b * X 0 : MvPolynomial (Fin 2) R) (m 1)).trans
      (by simpa using Nat.mul_le_mul_left (m 1) hx)
    simp only [totalDegree_C, totalDegree_X_pow, zero_add] at h₁
    have hs : m.sum (fun _ e => e) = m 0 + m 1 := by
      conv_lhs => rw [bivariate_exponent_eq m]
      exact bivariate_exponent_sum _ _
    have hm_le := le_totalDegree hm
    omega
  apply le_antisymm (hle a f)
  have h := hle (-a) (planeShear R a f)
  rwa [show planeShear R (-a) (planeShear R a f) = f from (planeShear R a).symm_apply_apply f] at h

/-- `planeShear` commutes with every coefficient map. -/
lemma planeShear_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (planeShear R a f) =
      planeShear S (φ a) (MvPolynomial.map φ f) := by
  suffices hh : (MvPolynomial.map φ).comp (planeShearHom R a).toRingHom =
      (planeShearHom S (φ a)).toRingHom.comp (MvPolynomial.map φ) from
    congrArg (fun h : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) S => h f) hh
  apply MvPolynomial.ringHom_ext
  · intro c; simp [planeShearHom]
  · intro i; fin_cases i <;> simp [planeShearHom]

end
end CCDN
