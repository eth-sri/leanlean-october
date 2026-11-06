module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Projection
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
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.BlockCharts
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.OrbitCharts
public import GS.CayleyCharts.Smooth
public import GS.CompactFibres
public import GS.Continuation.AmbientProjection
public import GS.Core
public import GS.Extensions.GeodesicNormal
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.Projection
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A horizontal complement for the orbit differential

All finite-dimensional choices in this file are constructed from complements
of submodules. The horizontal restriction is injective and has a continuous
linear left inverse defined on the full ambient matrix space. No hypothesis
excluding overlap is used.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.CayleyCharts GS.LieAction GS.ManifoldCompletion

namespace GS.OverlapGeometry

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def horizontalComplement (D : E →L[ℝ] F) : Submodule ℝ E :=
  Classical.choose (LinearMap.ker D.toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalComplement_isCompl (D : E →L[ℝ] F) :
    IsCompl (horizontalComplement D) (LinearMap.ker D.toLinearMap) :=
  (Classical.choose_spec (LinearMap.ker D.toLinearMap).exists_isCompl).symm

def complementKernelEquiv (D : E →L[ℝ] F) :
    (horizontalComplement D × (LinearMap.ker D.toLinearMap)) ≃L[ℝ] E :=
  (Submodule.prodEquivOfIsCompl _ _ (horizontalComplement_isCompl D)).toContinuousLinearEquiv

def horizontalRestriction (D : E →L[ℝ] F) : horizontalComplement D →L[ℝ] F :=
  D.comp (horizontalComplement D).subtypeL

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalRestriction_injective (D : E →L[ℝ] F) :
    Function.Injective (horizontalRestriction D) := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp (horizontalComplement_isCompl D).disjoint
    ((x : E) - (y : E)) ((horizontalComplement D).sub_mem x.property y.property)
  change D ((x : E) - (y : E)) = 0
  change D (x : E) = D (y : E) at h
  rw [map_sub, h, sub_self]

def horizontalRangeComplement (D : E →L[ℝ] F) : Submodule ℝ F :=
  Classical.choose (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalRangeComplement_isCompl (D : E →L[ℝ] F) :
    IsCompl (LinearMap.range (horizontalRestriction D).toLinearMap) (horizontalRangeComplement D) :=
  Classical.choose_spec (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

/-- A linear left inverse on the whole target, including normal directions. -/
def horizontalLeftInverse (D : E →L[ℝ] F) : F →L[ℝ] horizontalComplement D :=
  (LinearMap.linearProjOfIsCompl (horizontalRangeComplement D)
    (horizontalRestriction D).toLinearMap (horizontalRestriction_injective D)
    (horizontalRangeComplement_isCompl D)).toContinuousLinearMap

@[simp] theorem horizontalLeftInverse_apply (D : E →L[ℝ] F)
    (x : horizontalComplement D) : horizontalLeftInverse D (D x) = x :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ x

theorem horizontalLeftInverse_comp (D : E →L[ℝ] F) :
    (horizontalLeftInverse D).comp (horizontalRestriction D) =
      ContinuousLinearMap.id ℝ (horizontalComplement D) := by
  apply ContinuousLinearMap.ext
  intro x
  exact horizontalLeftInverse_apply D x

end Linear

variable {n : ℕ}

/-- The actual differential of the original factor parametrization. -/
def orbitDerivative (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    PairModel b₁ b₂ →L[ℝ] Mat n :=
  fderiv ℝ (orbitParam (1 : FactorGroup b₁ b₂) (permMatrix σ)) 0

abbrev OrbitKernel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :=
  LinearMap.ker (orbitDerivative b₁ b₂ σ).toLinearMap

abbrev HorizontalModel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :=
  horizontalComplement (orbitDerivative b₁ b₂ σ)

end GS.OverlapGeometry
