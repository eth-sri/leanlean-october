module

public import GS.Shared.OrbitAtlas
public import GS.Shared.HorizontalDifferential
public import GS.Shared.Projection
public import GS.OverlapGeometry.ManifoldSmoothMaps

@[expose] public section

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
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance tangentBridgeNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance tangentBridgeChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

section
variable (X : MatrixOrbit right left P) (Z : 𝕄)
/-- Full image of the actual mathlib manifold differential. -/
theorem orbit_tangent_image_iff :
    (∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, 𝕄))
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
  tauto

/-- The fixed points of the canonical projector are exactly the true tangents. -/
theorem pointProjection_fixed_iff_tangent_image
    :
    pointProjection right left X.val Z = Z ↔
      ∃ v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
        mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, 𝕄))
          (fun Y : MatrixOrbit right left P => Y.val) X v = Z := by
  rw [orbit_tangent_image_iff]
  constructor
  · intro h
    rw [← h]
    exact pointProjection_mem X.val Z
  · exact pointProjection_of_mem X.val Z

/-- The projected ambient matrix has one and only one actual tangent lift. -/
theorem pointProjection_unique_tangent_lift
    :
    ∃! v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X,
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, 𝕄))
        (fun Y : MatrixOrbit right left P => Y.val) X v =
          pointProjection right left X.val Z := by
  obtain ⟨v, hv⟩ := (orbit_tangent_image_iff right left P X _).mpr
    (pointProjection_mem X.val Z)
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact sharedOrbit_val_mfderiv_injective right left P X (hw.trans hv.symm)

end

/-- The intrinsic and ambient smooth-map interfaces agree. -/
theorem sharedOrbit_contMDiff_iff_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → MatrixOrbit right left P) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, HorizontalModel right left P)) ⊤ f ↔
      ContDiff ℝ ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_contDiff (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) f

/-- The same criterion permits a manifold source, including its tangent bundle. -/
theorem sharedOrbit_contMDiff_iff_ambient {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) (f : M → MatrixOrbit right left P) :
    ContMDiff I (𝓘(ℝ, HorizontalModel right left P)) ⊤ f ↔
      ContMDiff I (𝓘(ℝ, 𝕄)) ⊤ (fun x => (f x).val) :=
  GS.OverlapGeometry.slice_contMDiff_iff_ambient (preferredOrbitSlice right left P)
    (preferredOrbitSlice_covers right left P) I f

end GS.Shared
