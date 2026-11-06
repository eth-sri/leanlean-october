/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Translation of multivariate polynomials by a point: `originShift a` substitutes
`X j + a j` for every variable, moving the point `a` to the origin. `originShiftEquiv a` is
the same substitution as an algebra automorphism, with inverse the shift by `-a`. -/

@[expose] public section
namespace CCDN
open MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- The substitution `X j ↦ X j + a j`, which moves the point `a` to the origin. -/
noncomputable def originShift  (a : σ → R)  := eval₂Hom C (fun j => X j + C (a j))

/-- The origin shift fixes constant polynomials. -/
@[simp] lemma originShift_C  (a : σ → R) (c : R) :
    originShift a (C c) = C c := by
  simp [originShift]

/-- The origin shift by `a` sends the variable `X j` to `X j + a j`. -/
@[simp] lemma originShift_X  (a : σ → R) (j : σ) :
    originShift a (X j) = X j + C (a j) := by
  simp [originShift]

private lemma originShift_neg  (a : σ → R) (f : MvPolynomial σ R) :
    originShift (-a) (originShift a f) = f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf => simp [hf]

/-- The substitution `X j ↦ X j + a j` as an algebra automorphism, with inverse the
substitution `X j ↦ X j - a j`. -/
@[simps (rhsMd := .default) apply symm_apply]
noncomputable def originShiftEquiv  (a : σ → R)  :=
  AlgEquiv.ofAlgHom (aeval fun j => X j + C (a j)) (aeval fun j => X j + C ((-a) j))
    (by aesop)
    (by aesop)


/-- The origin shift of a nonzero polynomial is nonzero. -/
lemma originShift_ne_zero  (a : σ → R)
    {f : MvPolynomial σ R} (hf : f ≠ 0) : originShift a f ≠ 0 :=
  (map_ne_zero_iff _ ((Function.LeftInverse.injective (originShift_neg a)))).2 hf

/-- The origin shift commutes with coefficient maps: mapping the coefficients of the shift of `f`
by `a` along `φ` gives the shift of the mapped polynomial by the mapped point `φ ∘ a`. -/
lemma originShift_map {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : σ → R) (f : MvPolynomial σ R) :
    map φ (originShift a f) = originShift (fun j => φ (a j)) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf => simp [hf]

private lemma eval_originShift  (a x : σ → R)
    (f : MvPolynomial σ R) :
    eval x (originShift a f) = eval (fun j => x j + a j) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf => simp [hf]

/-- Evaluating the origin shift of `f` by `a` at `x - a` gives the value of `f` at `x`. -/
lemma eval_sub_originShift  (a x : σ → R)
    (f : MvPolynomial σ R) :
    eval (fun j => x j - a j) (originShift a f) = eval x f := by
  simp_all [eval_originShift, sub_add_cancel]

/-- The origin shift of `f` by `a` takes at the origin the value of `f` at `a`. -/
lemma eval_zero_originShift  (a : σ → R)
    (f : MvPolynomial σ R) : eval 0 (originShift a f) = eval a f := by
  rw [eval_originShift]
  simp only [Pi.zero_apply, zero_add]

/-- The origin shift commutes with partial derivatives. -/
lemma pderiv_originShift  (a : σ → R)
    (f : MvPolynomial σ R) (j : σ) :
    pderiv j (originShift a f) = originShift a (pderiv j f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f k hf =>
    simp only [map_mul, pderiv_mul, map_add, hf]
    by_cases h : k = j
    · subst k
      simp
    · simp [pderiv_X_of_ne h]

end CCDN
