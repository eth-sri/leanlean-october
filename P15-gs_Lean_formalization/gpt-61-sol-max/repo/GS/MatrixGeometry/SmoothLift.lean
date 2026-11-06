import GS.MatrixGeometry.Base

import GS.MatrixGeometry.GeneratorAction
import GS.MatrixGeometry.LocalSections


set_option backward.isDefEq.respectTransparency false
/-!
# Smooth minimum-physical-norm lifting on a fixed shared orbit

At a point g.P the canonical lift is Ad(g) D_P^dagger (g^-1.Z).
A smooth local factor section gives a smooth formula; equivariance makes
all such local formulas agree. The carrier may be singular, even zero.
No smooth pseudoinverse across changing orbit ranks is assumed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.MatrixBase
open scoped Manifold
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)
local instance smoothLiftNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance smoothLiftChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P


/-- Polynomial transport of a fixed linear lift. The model projections only
provide total extensions off the shared factor group. -/
def transportedMinimumNormLift (p : KMat 𝕜 n × (KMat 𝕜 n × KMat 𝕜 n)) : PairGenerator right left :=
  let v := minimumNormLift right left P (p.1ᴴ * p.2.2 * p.2.1)
  (modelProjection left (p.1 * v.1.val * p.1ᴴ),
   modelProjection right (p.2.1 * v.2.val * p.2.1ᴴ))

/-- Joint smoothness on the whole fixed orbit times the ambient matrix space. -/
theorem minimumNormLift_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, KMat 𝕜 n)))
      (𝓘(ℝ, PairGenerator right left)) ⊤
      (fun p : MatrixOrbit right left P × KMat 𝕜 n => minimumNormLift right left p.1.val p.2) := by
  apply transported_contMDiff right left P (fun X Z => minimumNormLift right left X Z)
    (transportedMinimumNormLift right left P)
  · fun_prop [transportedMinimumNormLift]
  · intro g Z
    have h := minimumNormLift_equivariant g P (g⁻¹ • Z)
    rw [smul_inv_smul] at h
    rw [h]
    have he : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by simp_all
    rw [he]
    apply Prod.ext
    · exact modelProjection_inclusion (generatorAction g
        (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).1
    · exact modelProjection_inclusion (generatorAction g
        (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).2

end GS.MatrixGeometry
