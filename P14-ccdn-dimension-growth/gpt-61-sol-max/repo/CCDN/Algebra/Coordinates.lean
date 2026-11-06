/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Ideal.Defs

/-! Coordinate types shared by the affine, projective, and Hilbert-function arguments. -/

public section
namespace CCDN

variable (n : ℕ)

/-- Integer points of affine `n`-space. -/
abbrev IntPoint  := Fin n → ℤ
/-- Rational points of affine `n`-space. -/
abbrev RatPoint  := Fin n → ℚ
/-- Rational projective points in dimension `n`. -/
abbrev ProjectivePoint  := Projectivization ℚ (Fin (n + 1) → ℚ)
/-- Integer polynomials in `n` coordinate variables. -/
abbrev IntegerPolynomial  := MvPolynomial (Fin n) ℤ
/-- Rational polynomials in `n` coordinate variables. -/
abbrev CoordinatePolynomial  := MvPolynomial (Fin n) ℚ
/-- Ideals in the rational coordinate polynomial ring. -/
abbrev CoordinateIdeal  := Ideal (CoordinatePolynomial n)
/-- An integer polynomial regarded as a rational polynomial. -/
noncomputable abbrev rationalPolynomial {σ : Type*} :=
  MvPolynomial.map (σ := σ) (Int.castRingHom ℚ)

end CCDN
