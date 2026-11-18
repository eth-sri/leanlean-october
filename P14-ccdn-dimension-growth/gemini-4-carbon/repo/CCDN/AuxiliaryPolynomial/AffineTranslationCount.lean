/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineTranslation
public import CCDN.Height.PrimitiveIntegerPolynomial

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma affineTranslation_eval {R : Type*} [CommRing R] {n : ℕ}
    (a x : Fin n → R) (f : MvPolynomial (Fin n) R) :
    eval x (affineTranslation R a f) = eval (x + a) f := by
  change eval x (eval₂ C (fun j => X j + C (a j)) f) = _
  rw [← eval_assoc]; congr 2; funext j; simp

lemma affineTranslation_constantCoeff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).coeff 0 = eval a f := by
  simpa only [zero_add, eval_zero, constantCoeff_eq] using affineTranslation_eval a 0 f

lemma PrimitiveIntegerPolynomial.translate_affine {n : ℕ} (a : Fin n → ℤ)
    {f : MvPolynomial (Fin n) ℤ} (hf : PrimitiveIntegerPolynomial f) :
    PrimitiveIntegerPolynomial (affineTranslation ℤ a f) := by
  intro c hc
  have he := map_dvd (affineTranslation ℤ a).symm.toRingHom ((C_dvd_iff_dvd_coeff c _).mpr hc)
  have hC : (affineTranslation ℤ a).symm (C c) = C c :=
    (affineTranslation ℤ a).symm.commutes c
  change (affineTranslation ℤ a).symm (C c) ∣
    (affineTranslation ℤ a).symm (affineTranslation ℤ a f) at he
  rw [hC, AlgEquiv.symm_apply_apply] at he
  exact hf c ((C_dvd_iff_dvd_coeff c f).mp he)

end
end CCDN
