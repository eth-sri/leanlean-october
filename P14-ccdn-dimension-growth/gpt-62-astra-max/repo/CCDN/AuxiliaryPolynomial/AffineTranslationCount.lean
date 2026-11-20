/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.AffineTranslation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CCDN.Determinant.PlaneMultiplicity
public import CCDN.Plane.FiniteFieldConstants
import CCDN.Plane.GridHeight

/-! Bounded translations remove a zero constant coefficient and preserve the
finite-field residue count, primitivity and integer point families. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R)

/-- Evaluating the affine translate of `f` by `a` at `x` gives the value of `f` at `x + a`. -/
lemma affineTranslation_eval (x : Fin n → R) (f : MvPolynomial (Fin n) R) :
    eval x (affineTranslation R a f) = eval (x + a) f := by
  change eval x (eval₂ C (fun j => X j + C (a j)) f) = _
  rw [← eval_assoc]
  congr 2
  funext j
  simp

/-- The constant coefficient of the affine translate of `f` by `a` is the value of `f` at
`a`. -/
lemma affineTranslation_constantCoeff (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).coeff 0 = eval a f := by
  simpa [constantCoeff_eq] using (affineTranslation_eval a 0 f)

/-- An integral affine translate of a primitive integral polynomial is primitive. -/
lemma PrimitiveIntegerPolynomial.translate_affine (a : Fin n → ℤ)
    {f : IntegerPolynomial n} (hf : PrimitiveIntegerPolynomial f) :
    PrimitiveIntegerPolynomial (affineTranslation ℤ a f) := by
  intro c hc
  have he := map_dvd (affineTranslation ℤ a).symm.toRingHom ((C_dvd_iff_dvd_coeff c _).mpr hc)
  have hC : (affineTranslation ℤ a).symm (C c) = C c := (affineTranslation ℤ a).symm.commutes c
  change (affineTranslation ℤ a).symm (C c) ∣
    (affineTranslation ℤ a).symm (affineTranslation ℤ a f) at he
  rw [hC, AlgEquiv.symm_apply_apply] at he
  exact hf c (by grind [C_dvd_iff_dvd_coeff])

end
end CCDN
