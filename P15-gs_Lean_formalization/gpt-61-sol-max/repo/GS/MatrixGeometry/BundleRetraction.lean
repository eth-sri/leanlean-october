import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Retraction


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
open GS.MatrixBase
open scoped Manifold
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)
local instance bundleRetractionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance bundleRetractionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

/-- Canonical function on the actual whole tangent bundle. -/
def cayleyRetraction
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) := cayleyFibreRetraction right left P p.proj p.2



end GS.MatrixGeometry
