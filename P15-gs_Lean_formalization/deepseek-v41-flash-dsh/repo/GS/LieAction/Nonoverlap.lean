module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
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
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import GS.CompactFibres
public import GS.Core
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.Projection
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The stabilizer in the real orthogonal non-overlap case

The entire O-block stabilizer is described, not just its tangent space.
It is equivalent to the 2^n diagonal sign matrices. This statement is for O,
not SO: separate determinant constraints would reduce the sign choices.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Each intersection of a right block and a pulled-back left block contains
at most one coordinate. This is the exact no-offdiagonal-overlap condition. -/
def NoOffDiagonalOverlap (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective (fun i => (block₁ i, block₂ (σ i)))

end GS.LieAction
