module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Actual compactness of orthogonal block factors and their matrix images

Compactness/closedness is not confused with smoothness.
The theorems apply to m=2 and m=3; m=3 can still be singular.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

 theorem orthogonal_entry_abs_le_one {A : Mat n} (hA : Orthogonal A) (i j : Fin n) :
    |A i j| ≤ 1 := by
  have hg := congrFun (congrFun hA.1 j) j
  have he : (∑ k : Fin n, A k j * A k j)=1 := by
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using hg
  have hs : A i j * A i j ≤ 1 := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (A k j)) (Finset.mem_univ i)
  by_contra hn
  have hp : 0 < (|A i j|-1)*(|A i j|+1) := by
    apply mul_pos
    · linarith [lt_of_not_ge hn]
    · positivity
  nlinarith [sq_abs (A i j)]

end GS.Extensions
