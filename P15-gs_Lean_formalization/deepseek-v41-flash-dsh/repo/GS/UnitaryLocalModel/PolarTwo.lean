module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
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
public import GS.ComplexAlgebra
public import GS.Continuation.ExponentialBasics
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OriginalCompact
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.NonmanifoldCompletion.BlockRealization
public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryLocalModel.PauliCoordinates
public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryNonmanifold.ScalarBridge


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Uniqueness of positive polar factors

The compact local-model argument needs algebraic uniqueness, rather than a
continuous choice of singular vectors or a constructed matrix polar function.
A positive polar factor is determined by its square; the remaining unitary
factor is then determined by invertibility. The statement is proved in every
finite size and specialized positivity includes the two-by-two anchor blocks.
-/
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace GS.UnitaryLocalModel
open GS.UnitaryNonmanifold

/-- Equal unitary-times-positive products have equal factors. -/
theorem positive_polar_unique {n : ℕ} (U V P Q : CMat n)
    (hU : GS.Unitary U) (hV : GS.Unitary V)
    (hP : P.PosDef) (hQ : Q.PosDef) (he : U*P = V*Q) :
    U = V ∧ P = Q := by
  have hs : P^2 = Q^2 := by
    have h := congrArg (fun T : CMat n => Tᴴ*T) he
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hQ.isHermitian.eq,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, ← Matrix.mul_assoc Vᴴ V,
      hU.1, hV.1, Matrix.one_mul, pow_two] using h
  have hPQ : P = Q := (CFC.sq_eq_sq_iff P Q hP.posSemidef.nonneg hQ.posSemidef.nonneg).mp hs
  refine ⟨?_, hPQ⟩
  subst Q
  exact hP.isUnit.mul_right_cancel he

/-- The right-positive convention has the same uniqueness property. -/
theorem positive_polar_unique_right {n : ℕ} (U V P Q : CMat n)
    (hU : GS.Unitary U) (hV : GS.Unitary V)
    (hP : P.PosDef) (hQ : Q.PosDef) (he : P*U = Q*V) :
    U = V ∧ P = Q := by
  have ht : Uᴴ*P = Vᴴ*Q := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hQ.isHermitian.eq]
      using congrArg Matrix.conjTranspose he
  obtain ⟨hUV, hPQ⟩ := positive_polar_unique Uᴴ Vᴴ P Q
    hU.conjTranspose hV.conjTranspose hP hQ ht
  exact ⟨Matrix.conjTranspose_injective hUV, hPQ⟩

end GS.UnitaryLocalModel
