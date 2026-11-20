/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.Cast.Defs

@[expose] public section
namespace CCDN

/-- Integral equations in a fixed number of coordinates. -/
abbrev IntegerPolynomial (n : ℕ) := MvPolynomial (Fin n) ℤ

/-- The polynomial ring `ℚ[x₁, …, xₙ]` in which affine algebraic sets are cut out. -/
abbrev CoordinatePolynomial (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- Extension of an integral equation to the rational coordinate ring. -/
noncomputable abbrev rationalEquation {σ : Type*} := MvPolynomial.map (σ := σ) (Int.castRingHom ℚ)

/-- Reduction of an integral equation modulo `p`. -/
noncomputable abbrev residueEquation {σ : Type*} (p : ℕ) := MvPolynomial.map (σ := σ) (Int.castRingHom (ZMod p))

/-- The matrix of values of a family of polynomials on a family of points. -/
noncomputable abbrev valueMatrix {σ R ι κ : Type*} [CommSemiring R] (z : ι → σ → R)
    (F : κ → MvPolynomial σ R) := Matrix.of fun i j => MvPolynomial.eval (z i) (F j)

end CCDN
