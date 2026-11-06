module

public import GS.Shared.Retraction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A canonical smooth retraction on the whole shared tangent bundle

The base is the actual shared matrix orbit, with its inherited-topology atlas.
The retraction is globally defined on mathlib's entire tangent bundle. It
fixes the zero section and its actual manifold differential on every zero
fibre is the identity. Arbitrary overlap and fixed singular carriers are
allowed. This is the exact Cayley map, not a truncated numerical algorithm.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance bundleRetractionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance bundleRetractionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance bundleRetractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

section
variable (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P))
/-- Canonical function on the actual whole tangent bundle. -/
def cayleyRetraction
    :
    MatrixOrbit right left P := cayleyFibreRetraction right left P p.proj p.2

@[simp] theorem cayleyRetraction_val
    :
    (cayleyRetraction right left P p).val =
      sharedCayleyValue right left p.proj.val (tangentAmbient right left P p) 1 := rfl

end

/-- Joint smoothness, including the varying base and all tangent fibres. -/
theorem cayleyRetraction_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (cayleyRetraction right left P) := by
  have hargs : ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, 𝕄))).prod (𝓘(ℝ, ℝ))) ⊤
      (fun p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) =>
        ((p.proj, tangentAmbient right left P p), (1 : ℝ))) :=
    ((Bundle.contMDiff_proj (TangentSpace (𝓘(ℝ, HorizontalModel right left P)))).prodMk
      (tangentAmbient_contMDiff right left P)).prodMk contMDiff_const
  have ha := (sharedCayleyValue_contMDiff right left P).comp hargs
  apply (sharedOrbit_contMDiff_iff_ambient right left P
    (𝓘(ℝ, HorizontalModel right left P)).tangent (cayleyRetraction right left P)).mpr
  aesop

section
variable (X : MatrixOrbit right left P)
@[simp] theorem cayleyRetraction_zero_section :
    cayleyRetraction right left P ⟨X, 0⟩ = X := cayleyFibreRetraction_zero right left P X

/-- The genuine manifold derivative of the fibre map, not only a matrix expansion. -/
theorem cayleyRetraction_fibre_mfderiv_zero :
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => cayleyRetraction right left P ⟨X, v⟩)
      (0 : HorizontalModel right left P) = ContinuousLinearMap.id ℝ (HorizontalModel right left P) :=
  cayleyFibreRetraction_mfderiv_zero right left P X


end

end GS.Shared
