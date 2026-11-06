/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.AuxiliaryPolynomial.HypersurfaceAffineCoordinates
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.IntegerPolynomialAvoidance
import CCDN.ForMathlib.MvPolynomial
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! A single bounded linear elimination step. A chosen nonzero ideal equation
of degree d becomes monic after a linear coordinate change with integer
direction bounded by d+1. The quotient is integral over the remaining linear
coordinates. -/

@[expose] public section
namespace CCDN
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
  obtain ⟨b, hb, hval⟩ := exists_integer_grid_eval_ne_zero_of_totalDegree P hp _ hd
  rw [eval_mul, eval_X] at hval
  exact ⟨b, hb, by simp_all,
    (mul_ne_zero_iff.mp hval).2⟩

variable {K σ : Type*} [Field K] (I : Ideal (MvPolynomial (Option σ) K))

variable (e : MvPolynomial (Option σ) K ≃ₐ[K] MvPolynomial (Option σ) K)

/-- The retained variables, transported back through the coordinate
automorphism, as elements of the original quotient. -/
noncomputable def coordinateEliminationMap 
      :=
  (Ideal.Quotient.mkₐ K I).comp (e.symm.toAlgHom.comp (rename some))

/-- For the linear coordinate change attached to a direction `b` with `b none ≠ 0`, the elimination
map sends the variable `X i` to the class of `X (some i) - (b (some i) / b none) * X none`. -/
lemma coordinateEliminationMap_direction_X  (b : Option σ → K)
    (hb : b none ≠ 0) (i : σ) :
    coordinateEliminationMap I (hypersurfaceAffineCoordinates 0 b hb) (X i) =
      (Ideal.Quotient.mk I) (X (some i) - C (b (some i) / b none) * X none) := by
  simp [coordinateEliminationMap, hypersurfaceAffineCoordinates,
    directionCoordinates, directionCoordinatesInv,
    div_eq_mul_inv, map_mul, mul_assoc]

/-- A monic equation in the eliminated coordinate proves integrality over
the retained coordinates, for any ideal containing the equation. -/
theorem coordinateEliminationMap_isIntegral 
    
    (q : MvPolynomial (Option σ) K)
    (hq : q ∈ I.map e)
    (hm : (optionEquivLeft K σ q).Monic) :
    (coordinateEliminationMap I e).IsIntegral := by
  let E := e.trans (optionEquivLeft K σ)
  let J := I.map E
  have hJ : (optionEquivLeft K σ q) ∈ I.map
      ((optionEquivLeft K σ).toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom) := by
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hq
  let φ := (Ideal.Quotient.mkₐ (MvPolynomial σ K) J).comp
    (Algebra.ofId (MvPolynomial σ K) (Polynomial (MvPolynomial σ K)))
  have hφ := hm.quotient_isIntegral hJ
  have hmap : Ideal.map E.symm.toRingEquiv.toRingHom
      (Ideal.map E.toRingEquiv.toRingHom I) = I := by
    rw [Ideal.map_map]
    have he : E.symm.toRingEquiv.toRingHom.comp E.toRingEquiv.toRingHom = RingHom.id _ :=
      E.toRingEquiv.symm_toRingHom_comp_toRingHom
    change I.map (E.symm.toRingEquiv.toRingHom.comp E.toRingEquiv.toRingHom) = I
    rw [he, Ideal.map_id]
  let ψ :=
    Ideal.quotientEquivAlg J I E.symm hmap.symm
  have hψ : RingHom.IsIntegral (R := Polynomial (MvPolynomial σ K) ⧸ J)
      (A := MvPolynomial (Option σ) K ⧸ I) ψ.toRingEquiv.toRingHom := by
    apply RingHom.isIntegral_of_surjective
    exact ψ.surjective
  have hint := RingHom.IsIntegral.trans (R := MvPolynomial σ K)
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

end CCDN
