module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.Smooth
public import GS.CompactFibres
public import GS.Continuation.AmbientProjection
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialCurves
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.GeodesicNormal
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OriginalCompact
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.GlobalGeometry.ExactSharing
public import GS.GlobalGeometry.FrobeniusProjection
public import GS.GlobalGeometry.SharedAlgebra
public import GS.GlobalGeometry.SharedFactorCurves
public import GS.GlobalGeometry.SharedNormalEquations
public import GS.LieAction.BlockGroup
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.SharedGeometry.Algebra
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact groups of repeated physical orthogonal blocks

`Pattern` records only the block size, its positivity/divisibility, and the
within-layer sharing labels.  `Factor` is a closed subgroup of the existing
block orthogonal group, with the inherited matrix topology.  In particular,
no group law or topology is imposed on a parametrized image by fiat.
-/

set_option autoImplicit false

noncomputable section
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ}

/-- A valid complete-block layout and arbitrary within-layer sharing labels.
Unused labels are allowed; different layers have independent patterns. -/
structure Pattern (n : ℕ) where
  size : ℕ
  positive : 0 < size
  divides : size ∣ n
  label : ℕ → ℕ

namespace Pattern

def block (s : Pattern n) (i : Fin n) : ℕ := i.val / s.size

/-- Actual entry equalities define a subgroup of the already constructed
block orthogonal group. -/
def subgroup (s : Pattern n) : Subgroup (GS.LieAction.BlockO s.block) where
  carrier := {A | TiedEntries s.size s.label A.val}
  one_mem' := TiedEntries.one s.size s.label
  mul_mem' := by
    intro A B hA hB
    exact TiedEntries.mul s.positive s.divides A.property.1 B.property.1 hA hB
  inv_mem' := by
    intro A hA
    exact hA.transpose

theorem subgroup_isClosed (s : Pattern n) :
    IsClosed (s.subgroup : Set (GS.LieAction.BlockO s.block)) :=
  (isClosed_tiedEntries s.size s.label).preimage continuous_subtype_val

end Pattern

abbrev Factor (s : Pattern n) := ↥s.subgroup
abbrev Generator (s : Pattern n) := ↥(sharedSkewSpace (n := n) s.size s.label)

namespace Factor
variable {s : Pattern n}

/-- The original finite matrix, through the two inherited subtypes. -/
def matrix (A : Factor s) : Mat n := A.val.val

@[simp] theorem matrix_one : matrix (1 : Factor s) = 1 := rfl
theorem matrix_shared (A : Factor s) : SharedOrthogonalFactor s.size s.label (matrix A) :=
  ⟨A.val.property.1, A.val.property.2, A.property⟩

theorem matrix_orthogonal (A : Factor s) : Orthogonal (matrix A) := A.val.property.2

theorem matrix_injective : Function.Injective (matrix : Factor s → Mat n) := by
  intro A B h
  apply Subtype.ext
  exact Subtype.ext h

theorem continuous_matrix : Continuous (matrix : Factor s → Mat n) :=
  continuous_subtype_val.comp continuous_subtype_val

def ofMatrix (A : Mat n) (hA : SharedOrthogonalFactor s.size s.label A) : Factor s :=
  ⟨⟨A, hA.1, hA.2.1⟩, hA.2.2⟩

@[simp] theorem matrix_ofMatrix (A : Mat n) (hA : SharedOrthogonalFactor s.size s.label A) :
    matrix (ofMatrix A hA) = A := rfl

end Factor

instance factorCompactSpace (s : Pattern n) : CompactSpace (Factor s) :=
  isCompact_iff_compactSpace.mp s.subgroup_isClosed.isCompact

/-- The two layers can use unrelated sharing maps and block sizes. -/
abbrev Factors (right left : Pattern n) := Factor left × Factor right

end GS.SharedGeometry
