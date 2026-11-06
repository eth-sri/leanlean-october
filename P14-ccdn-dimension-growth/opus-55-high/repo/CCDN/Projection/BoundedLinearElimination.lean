/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfaceAffineCoordinates
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.ForMathlib.MvPolynomial
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! A single bounded linear elimination step. A chosen nonzero ideal equation
of degree d becomes monic after a linear coordinate change with integer
direction bounded by d+1. The quotient is integral over the remaining linear
coordinates. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- A bounded integral direction simultaneously avoids the top form and the
coordinate hyperplane needed for an invertible linear substitution. -/
theorem exists_bounded_full_degree_direction {σ : Type*} [Fintype σ]
    (f : MvPolynomial (Option σ) ℚ) (hf : f ≠ 0) :
    ∃ b : Option σ → ℤ, (∀ i, 0 ≤ b i ∧ b i ≤ f.totalDegree + 1) ∧
      b none ≠ 0 ∧
      eval (fun i => (b i : ℚ)) (homogeneousComponent f.totalDegree f) ≠ 0 := by
  let P := X none * homogeneousComponent f.totalDegree f
  have hp := mul_ne_zero (X_ne_zero none) (homogeneousComponent_totalDegree_ne_zero hf)
  have hd : P.totalDegree ≤ f.totalDegree + 1 := by
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    have hh := (homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree_le
    omega
  obtain ⟨b, hb, hval⟩ := exists_integer_grid_eval_ne_zero_of_degreeOf P hp _ fun i => (degreeOf_le_totalDegree P i).trans hd
  change eval (fun i => (b i : ℚ))
    (X none * homogeneousComponent f.totalDegree f) ≠ 0 at hval
  rw [eval_mul, eval_X] at hval
  exact ⟨b, hb, mod_cast (mul_ne_zero_iff.mp hval).1,
    (mul_ne_zero_iff.mp hval).2⟩

variable {K σ : Type*} [Field K] (I : Ideal (MvPolynomial (Option σ) K))

/-- The retained variables, transported back through the coordinate
automorphism, as elements of the original quotient. -/
def coordinateEliminationMap
    (e : MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial (Option σ) K ⧸ I :=
  (Ideal.Quotient.mkₐ K I).comp (e.symm.toAlgHom.comp (rename some))

/-- For the linear coordinate change attached to a direction `b` with `b none ≠ 0`, the elimination
map sends the variable `X i` to the class of `X (some i) - (b (some i) / b none) * X none`. -/
lemma coordinateEliminationMap_direction_X
    (b : Option σ → K)
    (hb : b none ≠ 0) (i : σ) :
    coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb) (X i) =
      (Ideal.Quotient.mk I) (X (some i) - C (b (some i) / b none) * X none) := by
  simp [coordinateEliminationMap, hypersurfaceAffineCoordinates]
  erw [show (directionCoordinates b hb).symm (X (some i)) = directionCoordinatesInv b (X (some i)) from rfl]
  simp [directionCoordinatesInv, div_eq_mul_inv, map_mul, mul_assoc]

/-- A monic equation in the eliminated coordinate proves integrality over
the retained coordinates, for any ideal containing the equation. -/
theorem coordinateEliminationMap_isIntegral
    (e : MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K)
    (q : MvPolynomial (Option σ) K)
    (hq : q ∈ I.map e)
    (hm : (optionEquivLeft K σ q).Monic) :
    (coordinateEliminationMap I e).IsIntegral := by
  let E := e.trans (optionEquivLeft K σ)
  let J := I.map E
  let φ := (Ideal.Quotient.mkₐ (MvPolynomial σ K) J).comp
    (Algebra.ofId (MvPolynomial σ K) (Polynomial (MvPolynomial σ K)))
  have hφ := hm.quotient_isIntegral (by
    change (optionEquivLeft K σ q) ∈ I.map
      ((optionEquivLeft K σ).toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom)
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hq)
  have hmap : J.map E.symm = I := by
    change Ideal.map E.symm.toRingEquiv.toRingHom
      (Ideal.map E.toRingEquiv.toRingHom I) = I
    rw [Ideal.map_map]
    have he :=
      E.toRingEquiv.symm_toRingHom_comp_toRingHom
    simp_all
  let ψ : (Polynomial (MvPolynomial σ K) ⧸ J) ≃ₐ[K]
      (MvPolynomial (Option σ) K ⧸ I) :=
    Ideal.quotientEquivAlg J I E.symm hmap.symm
  have hψ : RingHom.IsIntegral (R := Polynomial (MvPolynomial σ K) ⧸ J)
      (A := MvPolynomial (Option σ) K ⧸ I) ψ.toRingEquiv.toRingHom := by
    apply RingHom.isIntegral_of_surjective
    exact ψ.surjective
  have hint := RingHom.IsIntegral.trans
    (S := Polynomial (MvPolynomial σ K) ⧸ J)
    (T := MvPolynomial (Option σ) K ⧸ I)
    φ.toRingHom ψ.toRingEquiv.toRingHom hφ hψ
  have heq : ψ.toAlgHom.comp (φ.restrictScalars K) = coordinateEliminationMap I e := by
    ext i
    simp [φ, coordinateEliminationMap]
    change (Ideal.Quotient.mk I) (E.symm (Polynomial.C (X i))) =
      (Ideal.Quotient.mk I) (e.symm (X (some i)))
    simp [E, optionEquivLeft_symm_C_X]
  change (ψ.toAlgHom.comp (φ.restrictScalars K)).IsIntegral at hint
  rwa [heq] at hint

