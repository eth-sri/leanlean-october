module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.Core
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.Projection


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The Frobenius dual and the actual derivative of an ambient loss

This file does not endow Matrix with an InnerProductSpace instance: its inherited
supremum norm is not the Frobenius norm. The scalar product is GS.frobInner.
The matrix representing a continuous linear functional is constructed from
its values on matrix units; no gradient hypothesis is inserted as an axiom.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
open scoped BigOperators
namespace GS.RiemannianCompletion
variable {n : ℕ}

/-- The actual matrix unit with its only nonzero entry at (i,j). -/
def unitEntry (i j : Fin n) : Mat n :=
  fun k l => if k = i then if l = j then 1 else 0 else 0

/-- An equality of actual matrices, not a basis postulate. -/
theorem matrix_expansion (Z : Mat n) :
    Z = ∑ i, ∑ j, Z i j • unitEntry i j := by
  classical
  ext k l
  simp [unitEntry, Matrix.sum_apply, Matrix.smul_apply, eq_comm]

/-- Frobenius representative of a functional, defined without differentiability. -/
def dualMatrix (D : Mat n →L[ℝ] ℝ) : Mat n := fun i j => D (unitEntry i j)

theorem functional_eq_frobInner (D : Mat n →L[ℝ] ℝ) (A : Mat n) :
    D A = frobInner (dualMatrix D) A := by
  calc
    D A = D (∑ i, ∑ j, A i j • unitEntry i j) :=
      congrArg D (matrix_expansion A)
    _ = ∑ i, ∑ j, A i j * D (unitEntry i j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = frobInner (dualMatrix D) A := by
      unfold frobInner dualMatrix
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _

/-- The ambient Frobenius gradient is computed from mathlib's real fderiv.
For nondifferentiable functions this follows fderiv's zero convention; all
calculus statements below explicitly assume differentiability. -/
def ambientGradient (f : Mat n → ℝ) (X : Mat n) : Mat n :=
  dualMatrix (fderiv ℝ f X)

theorem ambientGradient_represents (f : Mat n → ℝ) (X A : Mat n) :
    fderiv ℝ f X A = frobInner (ambientGradient f X) A :=
  functional_eq_frobInner (fderiv ℝ f X) A

end GS.RiemannianCompletion
