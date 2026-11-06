import Mathlib.Tactic
import GS.MatrixGeometry.Base

import GS.MatrixGeometry.BundleRetraction
import GS.MatrixGeometry.Gradient
import GS.Extensions.TangentSections


set_option backward.isDefEq.respectTransparency false
/-!
# Smooth intrinsic gradient sections and the exact shared gradient update

The target here is the actual tangent bundle, not only the matrix realization
of a vector field. To avoid assuming a smooth inverse to the inclusion
differential, we differentiate the smooth map F(X,Z) = R_X(proj_X Z) in its
ambient second variable at zero. This constructs the bundled tangent projector
from mathlib's genuine tangent map. No gradient-section regularity is assumed
in proving the smoothness of F: its matrix value is an explicit Cayley formula.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.MatrixBase
open scoped Manifold
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)
local instance gradientSectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance gradientSectionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance gradientSectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

variable (X : MatrixOrbit right left P)

/-- The already constructed pointwise tangent lift, as a continuous linear map. -/
def tangentProjectionCLM  :
    KMat 𝕜 n →L[ℝ] HorizontalModel right left P :=
  ({ toFun := tangentProjection right left P X
     map_add' := by
       intro Z W
       apply inclusionDifferential_injective right left P X
       simp only [map_add,inclusion_tangentProjection]
     map_smul' := by
       intro a Z
       apply inclusionDifferential_injective right left P X
       simp only [map_smul,inclusion_tangentProjection,RingHom.id_apply]
   } : KMat 𝕜 n →ₗ[ℝ] HorizontalModel right left P).toContinuousLinearMap



variable (p : MatrixOrbit right left P × KMat 𝕜 n)

/-- Ambient-input extension of the retraction, still valued in the exact orbit. -/
def ambientRetraction  :
    MatrixOrbit right left P :=
  cayleyFibreRetraction right left P p.1 (tangentProjection right left P p.1 p.2)

variable (f : KMat 𝕜 n → ℝ)

@[simp] theorem ambientRetraction_val  (Z : KMat 𝕜 n) :
    (ambientRetraction right left P (X, Z)).val =
      sharedCayleyValue right left X.val Z 1 := by
  change sharedCayleyValue right left X.val
    (inclusionDifferential right left P X (tangentProjection right left P X Z)) 1 = _
  rw [inclusion_tangentProjection]
  exact sharedCayleyValue_projected X.val Z 1

@[simp] theorem ambientRetraction_zero  :
    ambientRetraction right left P (X, 0) = X := by aesop

-- Preserve the abstract subspace interfaces during elaboration. Their defining
-- terms need not be expanded when comparing manifold and normed-space instances.
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

/-- This proof uses the matrix formula and hence is independent of the desired
smoothness of the tangent projection as a section. -/
theorem ambientRetraction_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, KMat 𝕜 n)))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (ambientRetraction right left P) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P
    ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, KMat 𝕜 n)))
    (ambientRetraction right left P)).mpr
  have hb : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, KMat 𝕜 n)))
      (𝓘(ℝ, KMat 𝕜 n)) ⊤ (fun p : MatrixOrbit right left P × KMat 𝕜 n => p.1.val) :=
    (sharedOrbit_val_contMDiff right left P).comp contMDiff_fst
  have hl := minimumNormLift_contMDiff right left P
  have h := (generatorCayleyValue_smooth right left).comp_contMDiff
    (hb.prodMk_space (hl.prodMk_space (contMDiff_const (c := (1 : ℝ)))))
  exact h.congr (fun ⟨X,Z⟩ => ambientRetraction_val right left P X Z)

/-- The projected ambient vector as an element of the TRUE total tangent bundle. -/
def tangentProjectionBundle  :
    TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) :=
  ⟨p.1, tangentProjection right left P p.1 p.2⟩

/-- Joint smoothness of the actual tangent lift, including its varying base. -/
theorem tangentProjectionBundle_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, KMat 𝕜 n)))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ⊤
      (tangentProjectionBundle right left P) := by
  refine (((ambientRetraction_contMDiff right left P).contMDiff_tangentMap (by simp)).comp
    (GS.Extensions.contMDiff_vertical_input (M := MatrixOrbit right left P)
      (V := KMat 𝕜 n) (𝓘(ℝ, HorizontalModel right left P)))).congr ?_
  rintro ⟨X,Z⟩
  have h := mfderiv_comp_apply_of_eq
    (I := 𝓘(ℝ, KMat 𝕜 n)) (f := fun W : KMat 𝕜 n => (X,W)) 0
    ((ambientRetraction_contMDiff right left P).mdifferentiable (by simp) (X,0))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) rfl Z
  simp only [TangentSpace, mfderiv_prod_right, ContinuousLinearMap.inr_apply,
    Function.comp_def] at h
  have hd := mfderiv_comp_apply_of_eq (0 : KMat 𝕜 n)
    ((cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp) 0)
    (tangentProjectionCLM right left P X).mdifferentiableAt
    (map_zero (tangentProjectionCLM right left P X)) Z
  simp only [TangentSpace, ContinuousLinearMap.mfderiv_eq,
    cayleyFibreRetraction_mfderiv_zero, ContinuousLinearMap.id_apply] at hd
  have hd := h.symm.trans hd
  dsimp only [Function.comp_def, tangentMap, tangentProjectionBundle]
  congr 1
  · aesop
  · exact hd.symm

end GS.MatrixGeometry
