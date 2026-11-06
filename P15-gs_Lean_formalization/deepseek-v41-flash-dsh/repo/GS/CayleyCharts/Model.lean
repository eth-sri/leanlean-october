module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.CayleyCharts.Algebra
public import GS.Core
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.Projection


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The finite-dimensional coordinate model

The model is the actual submodule of supported skew-symmetric matrices.
It carries the inherited finite-dimensional normed vector-space structure
for the entrywise supremum matrix norm, with the original product topology.
This is NOT a proposed definition of the tangent space of the GS orbit.
A continuous linear map into the model extends chart coordinates to ambient
matrices, making smoothness statements meaningful without assuming a manifold.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.CayleyCharts
variable {n : ℕ}

def modelSpace (block : Fin n → ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | Supported block A ∧ GS.IsSkew A}
  zero_mem' := by constructor <;> simp [Supported, GS.IsSkew]
  add_mem' := by
    intro A B hA hB
    refine ⟨hA.1.add hB.1, ?_⟩
    change (A + B)ᵀ = -(A + B)
    rw [Matrix.transpose_add, hA.2, hB.2, neg_add]
  smul_mem' := by
    intro c A hA
    refine ⟨Supported.smul c hA.1, ?_⟩
    change (c • A)ᵀ = -(c • A)
    rw [Matrix.transpose_smul, show Aᵀ = -A from hA.2, smul_neg]

abbrev Model (block : Fin n → ℕ) := ↥(modelSpace block)

/-- Every point of the linear coordinate model has a valid Cayley denominator. -/
theorem admissible_model {block : Fin n → ℕ} (x : Model block) :
    admissible x.val := admissible_of_isSkew x.val x.property.2

/-- Continuous linear inclusion into the original matrix space. -/
def modelInclusion (block : Fin n → ℕ) : Model block →L[ℝ] Mat n :=
  (modelSpace block).subtypeL

end GS.CayleyCharts
