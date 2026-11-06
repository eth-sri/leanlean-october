/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.Box
import CCDN.Height.PrimitiveIntegerPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Integral translations of the affine chart, lifted to homogeneous linear
coordinate changes, preserve primitive equations and homogeneous degree. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {n : ℕ}

/-- The homogeneous linear substitution fixing `X 0` and sending `X (j + 1)` to
`X (j + 1) + a j * X 0`; on the affine chart `X 0 = 1` it is the translation by `a`. -/
def homogeneousTranslationHom (R : Type*) [CommRing R] (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  aeval (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0))

/-- Composing the homogeneous translations by `a` and by `b` gives the homogeneous translation
by `a + b`. -/
lemma homogeneousTranslationHom_comp {R : Type*} [CommRing R] (a b : Fin n → R) :
    (homogeneousTranslationHom R a).comp (homogeneousTranslationHom R b) =
      homogeneousTranslationHom R (a + b) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [homogeneousTranslationHom]
  · simp only [homogeneousTranslationHom, AlgHom.comp_apply, aeval_X, Fin.cons_succ,
      map_add, map_mul, aeval_C, Fin.cons_zero, Pi.add_apply, algebraMap_eq]
    ring

end

section
variable (R : Type*) [CommRing R]

/-- The homogeneous translation by zero is the identity. -/
@[simp] lemma homogeneousTranslationHom_zero (n : ℕ) :
    homogeneousTranslationHom R (0 : Fin n → R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [homogeneousTranslationHom]

/-- The homogeneous translation by `a` (fixing `X 0` and sending `X (j + 1)` to
`X (j + 1) + a j * X 0`) as an algebra automorphism, with inverse the homogeneous translation
by `-a`. -/
def homogeneousTranslation {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom (homogeneousTranslationHom R a) (homogeneousTranslationHom R (-a))
    (by rw [homogeneousTranslationHom_comp, add_neg_cancel, homogeneousTranslationHom_zero])
    (by rw [homogeneousTranslationHom_comp, neg_add_cancel, homogeneousTranslationHom_zero])

end

/-- The homogeneous translation of a homogeneous polynomial of degree `d` is homogeneous of
degree `d`. -/
lemma homogeneousTranslation_homogeneous {R : Type*} [CommRing R] {n d : ℕ}
    (a : Fin n → R) {f : MvPolynomial (Fin (n + 1)) R} (hf : f.IsHomogeneous d) :
    (homogeneousTranslation R a f).IsHomogeneous d := by
  change (aeval (Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)) f).IsHomogeneous d
  let v : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
    Fin.cons (X 0) (fun j => X j.succ + C (a j) * X 0)
  have hv : ∀ i, (v i).IsHomogeneous 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [v, Fin.cons_zero] using isHomogeneous_X R (0 : Fin (n + 1))
    · simpa [v, Fin.cons_succ] using
        (isHomogeneous_X R j.succ).add ((isHomogeneous_X R (0 : Fin (n + 1))).C_mul (a j))
  simpa using hf.aeval v hv

variable {n : ℕ}

/-- The homogeneous translation by an integer vector of a primitive integer polynomial is
primitive. -/
lemma PrimitiveIntegerPolynomial.translate_homogeneous (a : Fin n → ℤ)
    {f : MvPolynomial (Fin (n + 1)) ℤ} (hf : PrimitiveIntegerPolynomial f) :
    PrimitiveIntegerPolynomial (homogeneousTranslation ℤ a f) := by
  intro c hc
  have hd := (C_dvd_iff_dvd_coeff c _).mpr hc
  have he := map_dvd (homogeneousTranslation ℤ a).symm.toRingHom hd
  have hC : (homogeneousTranslation ℤ a).symm (C c) = C c :=
    (homogeneousTranslation ℤ a).symm.commutes c
  change (homogeneousTranslation ℤ a).symm (C c) ∣
    (homogeneousTranslation ℤ a).symm (homogeneousTranslation ℤ a f) at he
  rw [hC, AlgEquiv.symm_apply_apply] at he
  exact hf c ((C_dvd_iff_dvd_coeff c f).mp he)

/-- The homogeneous translation of `f` by `a` evaluates at `x` to the value of `f` at the point
with coordinates `x 0` and `x (j + 1) + a j * x 0`. -/
lemma homogeneousTranslation_eval {R : Type*} [CommRing R]
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
lemma homogeneousTranslation_eval_chart {R : Type*} [CommRing R]
    (a z : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons 1 z) (homogeneousTranslation R a f) = eval (Fin.cons 1 (z + a)) f := by
  rw [homogeneousTranslation_eval]
  simp
  rfl

/-- If `z` lies in the box of radius `B ≥ 1` and every coordinate of `a` lies in `[0, d]`, then
every coordinate of `z - a` has absolute value at most `(d + 1) * B`. -/
lemma homogeneousTranslation_integer_point_box {B : ℝ} {d : ℕ}
    (hB : 1 ≤ B) (a z : Fin n → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    (hz : InBox z B) (j : Fin n) :
    |((z j - a j : ℤ) : ℝ)| ≤ ((d : ℝ) + 1) * B := by
  rw [Int.cast_sub]
  have ha0 : (0 : ℝ) ≤ a j := by simp_all
  have had : (a j : ℝ) ≤ d := mod_cast (ha j).2
  have h := abs_sub_le (z j : ℝ) 0 (a j : ℝ)
  simp [sub_zero, zero_sub, abs_neg, abs_of_nonneg ha0] at h
  nlinarith [hz j, show (0 : ℝ) ≤ d by positivity]

