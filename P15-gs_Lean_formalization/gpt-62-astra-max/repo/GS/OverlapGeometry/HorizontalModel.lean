module

public import GS.CompactFibres
public import GS.Core
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact

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

lemma splits (D : E →L[ℝ] F) : (horizontalRestriction D).HasLeftInverse :=
  .of_injective_of_finiteDimensional (fun x y h => Subtype.ext
    (LinearMap.injOn_of_disjoint_ker subset_rfl (horizontalComplement_isCompl D).disjoint x.property y.property h))

end Linear

variable {n : ℕ}

end GS.OverlapGeometry
