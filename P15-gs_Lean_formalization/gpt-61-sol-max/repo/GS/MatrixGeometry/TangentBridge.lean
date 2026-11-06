import Mathlib.Tactic
import GS.MatrixGeometry.Base

import GS.MatrixGeometry.OrbitAtlas
import GS.MatrixGeometry.HorizontalDifferential
import GS.MatrixGeometry.Projection
import GS.OverlapGeometry.ManifoldSmoothMaps


set_option backward.isDefEq.respectTransparency false
/-!
# The actual tangent space of the shared matrix orbit

The inclusion derivative of the constructed atlas has exactly the point-based
shared generator range.  The existing coupled projector is consequently the
orthogonal projector onto the full manifold tangent image, not merely onto
velocities with an assumed differentiable factor lift.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.MatrixBase
open scoped Manifold
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)
local instance tangentBridgeNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance tangentBridgeChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P


variable (X : MatrixOrbit right left P)

variable (Z : KMat 𝕜 n)

/-- Full image of the actual mathlib manifold differential. -/
theorem orbit_tangent_image_iff   :
    (∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, KMat 𝕜 n))
        (fun Y : MatrixOrbit right left P => Y.val) X v = Z) ↔
      Z ∈ pointDirections right left X.val := by
  rw [sharedOrbit_val_mfderiv_eq right left P X]
  have he : (fun h : HorizontalModel right left P =>
      preferredFactor P X • horizontalValue right left P h) =
      (fun h : HorizontalModel right left P => orbitParam (preferredFactor P X) P h.val) := by
    funext h
    exact (orbitParam_eq_translate (preferredFactor P X) P h.val).symm
  rw [he]
  have hg : preferredFactor P X • P = X.val :=
    congrArg Subtype.val (preferredFactor_spec P X)
  have hh := horizontalOrbit_fderiv_zero_range P (preferredFactor P X) Z
  rw [hg] at hh
  constructor
  · tauto
  · aesop

/-- The fixed points of the canonical projector are exactly the true tangents. -/
theorem pointProjection_fixed_iff_tangent_image
      :
    pointProjection right left X.val Z = Z ↔
      ∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
        mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, KMat 𝕜 n))
          (fun Y : MatrixOrbit right left P => Y.val) X v = Z := by
  grind [pointProjection_mem, pointProjection_of_mem, orbit_tangent_image_iff]

/-- The projected ambient matrix has one and only one actual tangent lift. -/
theorem pointProjection_unique_tangent_lift
      :
    ∃! v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, KMat 𝕜 n))
        (fun Y : MatrixOrbit right left P => Y.val) X v =
          pointProjection right left X.val Z := by
  obtain ⟨v, hv⟩ := (orbit_tangent_image_iff right left P X _).mpr
    (pointProjection_mem X.val Z)
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact sharedOrbit_val_mfderiv_injective right left P X (hw.trans hv.symm)



/-- The same criterion permits a manifold source, including its tangent bundle. -/
theorem sharedOrbit_contMDiff_iff_ambient {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → MatrixOrbit right left P) :
    ContMDiff I (𝓘(ℝ, HorizontalModel right left P)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, KMat 𝕜 n)) ⊤ (fun x => (f x).val) :=
  by exact?

end GS.MatrixGeometry
