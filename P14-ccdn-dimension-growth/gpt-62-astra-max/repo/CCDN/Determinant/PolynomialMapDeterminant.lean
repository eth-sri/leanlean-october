/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.Analysis.PrimeCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CCDN.Determinant.PlaneMultiplicity
public import CCDN.Plane.FiniteFieldConstants
public import CCDN.Height.IntegerCoefficientHeight
public import CCDN.Height.CountingHypotheses
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import CCDN.Hilbert.HomogeneousHilbert
import CCDN.Determinant.HomogeneousDeterminantComparison

/-! The determinant comparison for polynomial homogeneous-coordinate maps of
integer plane-curve points. The residue geometry comes from the plane
equation, so coordinates such as (H,x,y) need no rational rows. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix Real

/-- Evaluating the composite `g ∘ τ` of a polynomial map `τ` and a polynomial `g` at `z` is
evaluating `g` at `τ(z)`. -/
lemma eval_polynomial_coordinate_map {R : Type*} [CommRing R] {n m : ℕ}
    (τ : Fin m → MvPolynomial (Fin n) R) (g : MvPolynomial (Fin m) R) (z : Fin n → R) :
    eval z (aeval τ g) = eval (fun j => eval z (τ j)) g := by
  change eval z (eval₂ C τ g) = _
  rw [← eval_assoc]
  rfl

end
end CCDN
