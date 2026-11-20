/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.Box
public import CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Integral translations of the affine chart, lifted to homogeneous linear
coordinate changes, preserve primitive equations and homogeneous degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The homogeneous linear substitution fixing `X 0` and sending `X (j + 1)` to
`X (j + 1) + a j * X 0`; on the affine chart `X 0 = 1` it is the translation by `a`. -/
def homogeneousTranslationHom (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0))

/-- Composing the homogeneous translations by `a` and by `b` gives the homogeneous translation
by `a + b`. -/
lemma homogeneousTranslationHom_comp {R : Type*} [CommRing R] {n : ℕ} (a b : Fin n → R) :
    (homogeneousTranslationHom R a).comp (homogeneousTranslationHom R b) =
      homogeneousTranslationHom R (a + b) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  simp [homogeneousTranslationHom]
  · simp only [homogeneousTranslationHom, AlgHom.comp_apply, aeval_X, Fin.cons_succ,
      map_add, map_mul, aeval_C, Fin.cons_zero, Pi.add_apply, algebraMap_eq]
    ring

/-- The homogeneous translation by zero is the identity. -/
@[simp] lemma homogeneousTranslationHom_zero (R : Type*) [CommRing R] (n : ℕ) :
    homogeneousTranslationHom R (0 : Fin n → R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [homogeneousTranslationHom]

/-- The homogeneous translation by `a` (fixing `X 0` and sending `X (j + 1)` to
`X (j + 1) + a j * X 0`) as an algebra automorphism, with inverse the homogeneous translation
by `-a`. -/
def homogeneousTranslation (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom (homogeneousTranslationHom R a) (homogeneousTranslationHom R (-a))
    (by rw [homogeneousTranslationHom_comp, add_neg_cancel, homogeneousTranslationHom_zero])
    (by rw [homogeneousTranslationHom_comp, neg_add_cancel, homogeneousTranslationHom_zero])

section

variable {R : Type*} [CommRing R]
include R

/-- The homogeneous translation of a homogeneous polynomial of degree `d` is homogeneous of
degree `d`. -/
lemma homogeneousTranslation_homogeneous {n d : ℕ}
    (a : Fin n → R) {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsHomogeneous d) :
    (homogeneousTranslation R a f).IsHomogeneous d := by
  change (aeval (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)) f).IsHomogeneous d
  let v : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
    Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)
  have hv : ∀ i, (v i).IsHomogeneous 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [v, Fin.cons_zero] using isHomogeneous_X R (0 : Fin (n + 1))
    · simpa only [v, Fin.cons_succ] using
        (isHomogeneous_X R j.succ).add ((isHomogeneous_X R (0 : Fin (n + 1))).C_mul (a j))
  simpa [one_mul] using hf.aeval v hv

/-- The homogeneous translation of `f` by `a` evaluates at `x` to the value of `f` at the point
with coordinates `x 0` and `x (j + 1) + a j * x 0`. -/
lemma homogeneousTranslation_eval {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) (x : Fin (n + 1) → R) :
    eval x (homogeneousTranslation R a f) =
      eval (Fin.cons (x 0) (fun j => x j.succ + a j * x 0)) f := by
  change eval x (eval₂ C (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)) f) = _
  rw [← eval_assoc]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- On the affine chart `X 0 = 1`, the homogeneous translation of `f` by `a` evaluates at the
point `(1, z)` to the value of `f` at `(1, z + a)`. -/
lemma homogeneousTranslation_eval_chart {n : ℕ}
    (a z : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons 1 z) (homogeneousTranslation R a f) = eval (Fin.cons 1 (z + a)) f := by
  rw [homogeneousTranslation_eval]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_one]
  rfl

end

end
end CCDN
