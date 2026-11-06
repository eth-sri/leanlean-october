module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Diagonal
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
public import Mathlib.Tactic.NormNum
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
public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryLocalModel.NormalizationAlgebra
public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryNonmanifold.ScalarBridge


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Continuity of anchor dephasing

The anchor condition is open, and the explicit phase normalization is
continuous wherever its row and column anchors are nonzero. These statements
apply to arbitrary continuous parameter families of the original factors.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold

namespace GS.UnitaryLocalModel

variable {q : ℕ}

theorem continuousAt_phase {z : ℂ} (hz : z ≠ 0) : ContinuousAt phase z := by
  apply continuousAt_id.div
    (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
  change (‖z‖ : ℂ) ≠ 0
  exact_mod_cast norm_ne_zero_iff.mpr hz

theorem isOpen_anchorNonzero (Q : CMat q) (o : Fin q) :
    IsOpen {A : CMat q | AnchorNonzero Q A o} := by
  unfold AnchorNonzero
  apply IsOpen.and
  · simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_const.and (isOpen_ne_fun
      (show Continuous (fun A : CMat q => A i o) from by fun_prop) continuous_const)
  · simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_const.and (isOpen_ne_fun
      (show Continuous (fun A : CMat q => A o j) from by fun_prop) continuous_const)

theorem continuousAt_rowPhase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (i : Fin q) :
    ContinuousAt (fun M : CMat q => rowPhase Q M o i) A := by
  have he : ContinuousAt (fun M : CMat q => M i o / Q i o) A :=
    (show Continuous (fun M : CMat q => M i o) from by fun_prop).continuousAt.div_const _
  exact ContinuousAt.comp (f := fun M : CMat q => M i o / Q i o)
    (g := phase) (continuousAt_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)) he

theorem continuousAt_colPhase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (j : Fin q) :
    ContinuousAt (fun M : CMat q => colPhase Q M o j) A := by
  have he : ContinuousAt (fun M : CMat q => M o j / Q o j) A :=
    (show Continuous (fun M : CMat q => M o j) from by fun_prop).continuousAt.div_const _
  exact ContinuousAt.comp (f := fun M : CMat q => M o j / Q o j)
    (g := phase) (continuousAt_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)) he

theorem continuousAt_dephase {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) :
    ContinuousAt (fun M : CMat q => dephase Q M o) A := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (((continuousAt_rowPhase ha i).star.mul
    (continuous_apply_apply i j).continuousAt).mul
    (continuousAt_colPhase ha j).star).mul (continuousAt_rowPhase ha o)

section ParameterFamilies

variable {E : Type*} [TopologicalSpace E] {x : E}
  {A B : E → CMat q} {U V : E → Fin q → CMat 2}
  {Q : CMat q} {o : Fin q}

end ParameterFamilies
end GS.UnitaryLocalModel
