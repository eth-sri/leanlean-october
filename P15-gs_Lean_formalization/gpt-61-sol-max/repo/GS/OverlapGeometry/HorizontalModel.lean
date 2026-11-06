
import GS.ManifoldCompletion.OrbitDifferential
import Mathlib.LinearAlgebra.Projection



/-!
# A horizontal complement for the orbit differential

All finite-dimensional choices in this file are constructed from complements
of submodules. The horizontal restriction is injective and has a continuous
linear left inverse defined on the full ambient matrix space. No hypothesis
excluding overlap is used.
-/

noncomputable section


namespace GS.OverlapGeometry

section Linear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

variable (D : E →L[ℝ] F)

def horizontalComplement  : Submodule ℝ E :=
  Classical.choose (LinearMap.ker D.toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalComplement_isCompl  :
    IsCompl (horizontalComplement D) (LinearMap.ker D.toLinearMap) :=
  (Classical.choose_spec (LinearMap.ker D.toLinearMap).exists_isCompl).symm

def complementKernelEquiv  :
    (horizontalComplement D × (LinearMap.ker D.toLinearMap)) ≃L[ℝ] E :=
  (Submodule.prodEquivOfIsCompl _ _ (horizontalComplement_isCompl D)).toContinuousLinearEquiv



def horizontalRestriction := D.comp (horizontalComplement D).subtypeL



theorem horizontalRestriction_injective  :
    Function.Injective (horizontalRestriction D) := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp (horizontalComplement_isCompl D).disjoint
    ((x : E) - (y : E)) ((horizontalComplement D).sub_mem x.property y.property)
  change D ((x : E) - (y : E)) = 0
  change D (x : E) = D (y : E) at h
  rw [map_sub, h, sub_self]

def horizontalRangeComplement  : Submodule ℝ F :=
  Classical.choose (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem horizontalRangeComplement_isCompl  :
    IsCompl (LinearMap.range (horizontalRestriction D).toLinearMap) (horizontalRangeComplement D) :=
  Classical.choose_spec (LinearMap.range (horizontalRestriction D).toLinearMap).exists_isCompl

/-- A linear left inverse on the whole target, including normal directions. -/
def horizontalLeftInverse  : F →L[ℝ] horizontalComplement D :=
  (LinearMap.linearProjOfIsCompl (horizontalRangeComplement D)
    (horizontalRestriction D).toLinearMap (horizontalRestriction_injective D)
    (horizontalRangeComplement_isCompl D)).toContinuousLinearMap

@[simp] theorem horizontalLeftInverse_apply 
    (x : horizontalComplement D) : horizontalLeftInverse D (D x) = x :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ x

theorem horizontalLeftInverse_comp  :
    (horizontalLeftInverse D).comp (horizontalRestriction D) =
      ContinuousLinearMap.id ℝ (horizontalComplement D) := by
  apply ContinuousLinearMap.ext
  intro x
  exact horizontalLeftInverse_apply D x

end Linear














end GS.OverlapGeometry
