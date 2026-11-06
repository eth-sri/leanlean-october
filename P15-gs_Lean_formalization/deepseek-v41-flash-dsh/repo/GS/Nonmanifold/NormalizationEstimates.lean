module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
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
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialChart
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OriginalCompact
public import GS.Extensions.OriginalFibres
public import GS.Extensions.OriginalUniform
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.M4Certificate
public import GS.M4Necessary
public import GS.M4Obstruction
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Specifications
public import GS.ThreeFactor


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Concrete steps toward uniform coverage of the original family

These estimates formalize the normalized scalar error and the integer cocycle
in the manuscript. The existence of all normalized representatives and small
skew logarithms is still a separate obligation; this file does not assume a
local-coverage or nonmanifold theorem under another name.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
open scoped BigOperators
namespace GS.Nonmanifold

/-- Orthogonality of exp H forces H to be skew on a symmetric injectivity domain.
Only local injectivity is used; existence of H is not asserted here. -/
theorem skew_of_exp_orthogonal {q : ℕ} (V : Set (Mat q))
    (hinj : Set.InjOn (@matrixExp q) V) (H : Mat q)
    (ht : Hᵀ ∈ V) (hn : -H ∈ V) (hH : Orthogonal (matrixExp H)) : IsSkew H := by
  apply hinj ht hn
  rw [matrixExp_transpose]
  calc
    (matrixExp H)ᵀ = (matrixExp H)ᵀ * (matrixExp H * matrixExp (-H)) := by
      rw [matrixExp_mul_neg, Matrix.mul_one]
    _ = matrixExp (-H) := by rw [← Matrix.mul_assoc, hH.1, Matrix.one_mul]

/-- The symmetric chart restriction is built explicitly from the existing
inverse-function-theorem result, rather than passed as an extra assumption. -/
theorem exists_open_exp_skew_detection (q : ℕ) :
    ∃ V : Set (Mat q), IsOpen V ∧ (0:Mat q) ∈ V ∧
      ∀ H ∈ V, Orthogonal (matrixExp H) → IsSkew H := by
  obtain ⟨U,hU,h0,hinj⟩ := exists_open_matrixExp_injective q
  let V : Set (Mat q) := (fun H : Mat q => Hᵀ) ⁻¹' U ∩
    (fun H : Mat q => -H) ⁻¹' U
  have hV : IsOpen V :=
    (hU.preimage (by fun_prop)).inter (hU.preimage (by fun_prop))
  refine ⟨V,hV,?_,?_⟩
  · exact ⟨by simpa using h0, by simpa using h0⟩
  · intro H hH ho
    exact skew_of_exp_orthogonal U hinj H hH.1 hH.2 ho

end GS.Nonmanifold
