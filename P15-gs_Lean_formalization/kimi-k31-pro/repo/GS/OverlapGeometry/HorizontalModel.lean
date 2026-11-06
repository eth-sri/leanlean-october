module

public import GS.ManifoldCompletion.OrbitDifferential
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

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
end GS.OverlapGeometry
