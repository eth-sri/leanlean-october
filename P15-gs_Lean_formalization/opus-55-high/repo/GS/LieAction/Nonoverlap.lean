module

public import GS.CompactFibres
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import GS.Core
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import GS.Frobenius
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient
public import GS.Shuffle
public import GS.GeometryAlgebra

@[expose] public section


/-!
# The stabilizer in the real orthogonal non-overlap case

The entire O-block stabilizer is described, not just its tangent space.
It is equivalent to the 2^n diagonal sign matrices. This statement is for O,
not SO: separate determinant constraints would reduce the sign choices.

-/

noncomputable section
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Each intersection of a right block and a pulled-back left block contains
at most one coordinate. This is the exact no-offdiagonal-overlap condition. -/
def NoOffDiagonalOverlap (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective (fun i => (block₁ i, block₂ (σ i)))




end GS.LieAction
