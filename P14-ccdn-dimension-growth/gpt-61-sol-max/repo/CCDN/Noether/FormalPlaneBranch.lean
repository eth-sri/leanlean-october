/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Noether.FormalImplicitRoot

/-! Formal branches of plane equations at nonsingular points, in either
coordinate chart. The other coordinate is the parameter X plus its base value. -/

@[expose] public section
namespace CCDN

variable {K : Type*} [CommRing K]

/-- Turn coordinate j into a polynomial variable and the other coordinate
into the formal parameter X+a. -/
noncomputable def formalPlanePolynomial  (j : Fin 2) (a : K)  :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp PowerSeries.C)
    (fun k => if k = j then Polynomial.X else Polynomial.C (PowerSeries.X + PowerSeries.C a))

/-- `formalPlanePolynomial j a` sends variable `j` to the polynomial variable and the other
variable to the constant polynomial with value the power series `X + a`. -/
@[simp] lemma formalPlanePolynomial_X 
    (j k : Fin 2) (a : K) :
    formalPlanePolynomial j a (MvPolynomial.X k) =
      if k = j then Polynomial.X else Polynomial.C (PowerSeries.X + PowerSeries.C a) := by
  simp [formalPlanePolynomial]

variable (j : Fin 2) (a : K) (f : MvPolynomial (Fin 2) K)

private lemma formalPlanePolynomial_derivative 
     :
    (formalPlanePolynomial j a f).derivative =
      formalPlanePolynomial j a (MvPolynomial.pderiv j f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [formalPlanePolynomial]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f k hf =>
    by_cases h : k = j
    · subst k
      simp [map_mul, Polynomial.derivative_mul, formalPlanePolynomial_X, hf]
      ring
    · simp [map_mul, Polynomial.derivative_mul, formalPlanePolynomial_X, hf, h]
      ring

private lemma formalPlanePolynomial_eval 
     (g : PowerSeries K) :
    (formalPlanePolynomial j a f).eval g =
      MvPolynomial.eval₂ PowerSeries.C
        (fun k => if k = j then g else PowerSeries.X + PowerSeries.C a) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [formalPlanePolynomial]
  | add f h hf hh => simp [map_add, hf, hh]
  | mul_X f k hf =>
    aesop

private lemma formalPlanePolynomial_constant_eval 
    (j : Fin 2) (a b : K) (f : MvPolynomial (Fin 2) K) :
    ((formalPlanePolynomial j a f).map PowerSeries.constantCoeff).eval b =
      MvPolynomial.eval (fun k => if k = j then b else a) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [formalPlanePolynomial]
  | add f h hf hh => simp [map_add, hf, hh]
  | mul_X f k hf =>
    aesop

/-- A point of the plane is recovered from its coordinate `j` and its other coordinate `j.rev`. -/
lemma plane_coordinate_cases {K : Type*} (z : Fin 2 → K) (j : Fin 2) :
    (fun k => if k = j then z j else z j.rev) = z := by
  grind

/-- A nonzero chosen partial derivative supplies a formal branch
through the given point. This works in arbitrary characteristic. -/
theorem exists_formal_plane_branch {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0) (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    ∃ g : PowerSeries K, PowerSeries.constantCoeff g = z j ∧
      MvPolynomial.eval₂ PowerSeries.C
        (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev)) f = 0 := by
  let F := formalPlanePolynomial j (z j.rev) f
  have hroot : (F.map PowerSeries.constantCoeff).eval (z j) = 0 := by
    rw [formalPlanePolynomial_constant_eval, plane_coordinate_cases]
    exact hz
  have hder : (F.derivative.map PowerSeries.constantCoeff).eval (z j) ≠ 0 := by
    rw [formalPlanePolynomial_derivative, formalPlanePolynomial_constant_eval,
      plane_coordinate_cases]
    exact hj
  obtain ⟨g, hg, hfg⟩ := exists_formal_simple_root F (z j) hroot hder
  refine ⟨g, hg, ?_⟩
  rwa [formalPlanePolynomial_eval] at hfg

end CCDN
