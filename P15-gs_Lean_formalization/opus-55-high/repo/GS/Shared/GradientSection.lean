module

public import GS.Shared.BundleRetraction
public import GS.Shared.Gradient
public import GS.Extensions.TangentSections

@[expose] public section

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
open scoped Topology Manifold ContDiff
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance gradientSectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance gradientSectionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance gradientSectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- The already constructed pointwise tangent lift, as a continuous linear map. -/
def tangentProjectionCLM (X : MatrixOrbit right left P) :
    𝕄 →L[ℝ] HorizontalModel right left P :=
  ({ toFun := tangentProjection right left P X
     map_add' := tangentProjection_add right left P X
     map_smul' := tangentProjection_smul right left P X
   } : 𝕄 →ₗ[ℝ] HorizontalModel right left P).toContinuousLinearMap


/-- Ambient-input extension of the retraction, still valued in the exact orbit. -/
def ambientRetraction (p : MatrixOrbit right left P × 𝕄) :
    MatrixOrbit right left P :=
  cayleyFibreRetraction right left P p.1 (tangentProjection right left P p.1 p.2)

section
variable (X : MatrixOrbit right left P)
@[simp] theorem ambientRetraction_val (Z : 𝕄) :
    (ambientRetraction right left P (X, Z)).val =
      sharedCayleyValue right left X.val Z 1 := by
  change sharedCayleyValue right left X.val
    (inclusionDifferential right left P X (tangentProjection right left P X Z)) 1 = _
  simp

@[simp] theorem ambientRetraction_zero :
    ambientRetraction right left P (X, 0) = X := by
  simp [ambientRetraction]

end

-- Preserve the abstract subspace interfaces during elaboration. Their defining
-- terms need not be expanded when comparing manifold and normed-space instances.
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

/-- This proof uses the matrix formula and hence is independent of the desired
smoothness of the tangent projection as a section. -/
theorem ambientRetraction_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (ambientRetraction right left P) := by
  apply (sharedOrbit_contMDiff_iff_ambient right left P
    ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
    (ambientRetraction right left P)).mpr
  have hb : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (𝓘(ℝ, 𝕄)) ⊤ (fun p : MatrixOrbit right left P × 𝕄 => p.1.val) :=
    ContMDiff.comp
      (g := fun X : MatrixOrbit right left P => X.val)
      (f := fun p : MatrixOrbit right left P × 𝕄 => p.1)
      (sharedOrbit_val_contMDiff right left P) contMDiff_fst
  have hl := minimumNormLift_contMDiff right left P
  have h := (generatorCayleyValue_smooth right left).comp_contMDiff
    (hb.prodMk_space (hl.prodMk_space (contMDiff_const (c := (1 : ℝ)))))
  have he : (fun p : MatrixOrbit right left P × 𝕄 =>
      (ambientRetraction right left P p).val) =
      (fun p : MatrixOrbit right left P × 𝕄 =>
        sharedCayleyValue right left p.1.val p.2 1) := by
    aesop
  aesop

section
variable (X : MatrixOrbit right left P) (Z : 𝕄)
/-- The same partial derivative written as the full derivative on a vertical vector. -/
theorem ambientRetraction_vertical_mfderiv :
    @Eq (HorizontalModel right left P)
      (mfderiv ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
        (𝓘(ℝ, HorizontalModel right left P)) (ambientRetraction right left P)
        (X, (0 : 𝕄)) ((0 : HorizontalModel right left P), Z))
      (tangentProjection right left P X Z) := by
  have h := mfderiv_comp_apply_of_eq (0 : 𝕄) ((ambientRetraction_contMDiff right left P).mdifferentiable (by simp) (X, 0))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) rfl Z
  simp only [TangentSpace, mfderiv_prod_right, ContinuousLinearMap.inr_apply, Function.comp_def, id] at h
  refine h.symm.trans ?_
  have := mfderiv_comp_apply_of_eq (0 : 𝕄) ((cayleyFibreRetraction_contMDiff right left P X).mdifferentiable (by simp) 0)
    (tangentProjectionCLM right left P X).mdifferentiableAt (map_zero _) Z
  simp only [TangentSpace, ContinuousLinearMap.mfderiv_eq, cayleyFibreRetraction_mfderiv_zero right left P X,
    ContinuousLinearMap.id_apply] at this
  exact this

end

/-- Smooth vertical vector at (X,0), with ambient input Z. -/
def projectionVerticalInput (p : MatrixOrbit right left P × 𝕄) :
    TangentBundle ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (MatrixOrbit right left P × 𝕄) :=
  ⟨(p.1, 0), (0, p.2)⟩

theorem projectionVerticalInput_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄))).tangent ⊤
      (projectionVerticalInput right left P) :=
  GS.Extensions.contMDiff_vertical_input
    (M := MatrixOrbit right left P) (V := 𝕄) (𝓘(ℝ, HorizontalModel right left P))

section
variable (p : MatrixOrbit right left P × 𝕄)
/-- The projected ambient vector as an element of the TRUE total tangent bundle. -/
def tangentProjectionBundle :
    TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) :=
  ⟨p.1, tangentProjection right left P p.1 p.2⟩

end

section
variable (f : 𝕄 → ℝ)
/-- The intrinsic gradient as a section of mathlib's actual tangent bundle. -/
def intrinsicGradientSection (X : MatrixOrbit right left P) :
    TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) :=
  ⟨X, intrinsicGradient right left P f X⟩


/-- A genuinely C-infinity loss suffices; analyticity is not required. -/
theorem intrinsicGradientSection_smooth (hf : ContDiff ℝ ∞ f) :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ∞
      (intrinsicGradientSection right left P f) := by
  have h : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄)))
      (𝓘(ℝ, HorizontalModel right left P)).tangent ⊤ (tangentProjectionBundle right left P) := by
    convert ((ambientRetraction_contMDiff right left P).contMDiff_tangentMap (by simp)).comp
      (projectionVerticalInput_contMDiff right left P) using 1
    funext p
    simp only [Function.comp, tangentProjectionBundle, projectionVerticalInput, tangentMap,
      ambientRetraction_vertical_mfderiv]
    simp
  have h' := ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := 𝕄 →L[ℝ] ℝ) (F := 𝕄) (n := ∞) (dualCLM (𝕜 := 𝕜) (n := n))
  have hg : ContDiff ℝ ∞ (ambientGradient f) := h'.comp (hf.fderiv_right (m := ∞) (by simp))
  exact (h.of_le le_top).comp (contMDiff_id.prodMk (hg.comp_contMDiff
    ((sharedOrbit_val_contMDiff right left P).of_le le_top)))


end

end GS.Shared
