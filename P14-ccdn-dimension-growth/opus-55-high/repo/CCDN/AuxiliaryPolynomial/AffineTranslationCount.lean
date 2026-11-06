/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.AffineTranslation
import CCDN.Determinant.SingularReduction
import CCDN.Plane.GridHeight

/-! Bounded translations remove a zero constant coefficient and preserve the
finite-field residue count, primitivity and integer point families. -/

namespace CCDN
section
open MvPolynomial

section
variable {R : Type*} [CommRing R] {n : ℕ}

/-- Evaluating the affine translate of `f` by `a` at `x` gives the value of `f` at `x + a`. -/
lemma affineTranslation_eval
    (a x : Fin n → R) (f : MvPolynomial (Fin n) R) :
    eval x (affineTranslation R a f) = eval (x + a) f := by
  change eval x (eval₂ C (fun j => X j + C (a j)) f) = _
  rw [← eval_assoc]
  congr 2
  funext j
  simp

/-- The constant coefficient of the affine translate of `f` by `a` is the value of `f` at
`a`. -/
lemma affineTranslation_constantCoeff
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).coeff 0 = eval a f := by
  have he := affineTranslation_eval a 0 f
  simpa [zero_add, eval_zero, constantCoeff_eq] using he

end

/-- An integral affine translate of a primitive integral polynomial is primitive. -/
lemma PrimitiveIntegerPolynomial.translate_affine {n : ℕ} (a : Fin n → ℤ)
    {f : MvPolynomial (Fin n) ℤ} (hf : PrimitiveIntegerPolynomial f) :
    PrimitiveIntegerPolynomial (affineTranslation ℤ a f) := by
  intro c hc
  have hd := (C_dvd_iff_dvd_coeff c _).mpr hc
  have he := map_dvd (affineTranslation ℤ a).symm.toRingHom hd
  have hC : (affineTranslation ℤ a).symm (C c) = C c := (affineTranslation ℤ a).symm.commutes c
  change (affineTranslation ℤ a).symm (C c) ∣
    (affineTranslation ℤ a).symm (affineTranslation ℤ a f) at he
  rw [hC, AlgEquiv.symm_apply_apply] at he
  exact hf c ((C_dvd_iff_dvd_coeff c f).mp he)

section
variable (a : Fin 2 → ℤ) (f : MvPolynomial (Fin 2) ℤ) (p : ℕ)

/-- Translation of the residue zero set, over ZMod p for every p. -/
def affineTranslationResidueEquiv :
    PlaneResidue (affineTranslation ℤ a f) p ≃ PlaneResidue f p where
  toFun x := ⟨x.val + fun j => (a j : ZMod p), by
    have h := x.property
    rw [← eval_map, affineTranslation_map, affineTranslation_eval] at h
    simpa [eval_map, Function.comp_def, Int.coe_castRingHom] using h⟩
  invFun x := ⟨x.val - fun j => (a j : ZMod p), by
    rw [← eval_map, affineTranslation_map, affineTranslation_eval]
    simpa [Function.comp_def, Int.coe_castRingHom, sub_add_cancel, eval_map] using x.property⟩
  left_inv x := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv x := by apply Subtype.ext; exact sub_add_cancel _ _

end

