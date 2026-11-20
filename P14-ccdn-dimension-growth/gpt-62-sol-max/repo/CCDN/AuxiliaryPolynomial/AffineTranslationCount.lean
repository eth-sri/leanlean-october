/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.Algebra.IntegerPolynomialAvoidance
public import CCDN.Algebra.AffineTranslation
public import CCDN.Height.PrimitiveIntegerPolynomial

/-! Bounded translations remove a zero constant coefficient and preserve the
finite-field residue count, primitivity and integer point families. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluating the affine translate of `f` by `a` at `x` gives the value of `f` at `x + a`. -/
lemma affineTranslation_eval {R : Type*} [CommRing R] {n : ℕ}
    (a x : Fin n → R) (f : MvPolynomial (Fin n) R) :
    eval x (affineTranslation R a f) = eval (x + a) f := by
  change eval x (eval₂ C (fun j => X j + C (a j)) f) = _
  rw [← eval_assoc]
  congr 2
  funext j
  simp

/-- The constant coefficient of the affine translate of `f` by `a` is the value of `f` at
`a`. -/
lemma affineTranslation_constantCoeff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).coeff 0 = eval a f := by
  have he := affineTranslation_eval a 0 f
  simpa only [zero_add, eval_zero, constantCoeff_eq] using he

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

/-- A nonzero integral polynomial `f` in `n` variables has an integral translate with nonzero
constant coefficient by a vector whose entries lie in `[0, deg f]`. -/
theorem exists_bounded_affine_translation_nonzero_constant {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) :
    ∃ a : Fin n → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      (affineTranslation ℤ a f).coeff 0 ≠ 0 := by
  obtain ⟨a, ha, he⟩ := exists_integer_grid_eval_ne_zero f hf _ le_rfl
  exact ⟨a, ha, by rwa [affineTranslation_constantCoeff]⟩

end
end CCDN
