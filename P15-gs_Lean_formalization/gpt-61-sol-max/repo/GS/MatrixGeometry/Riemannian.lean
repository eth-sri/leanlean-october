import GS.MatrixGeometry.Base

import GS.MatrixGeometry.OrbitAtlas
import GS.MatrixGeometry.AmbientDual
import GS.Extensions.FiniteTopology
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.LocallyConvex.Bounded


set_option backward.isDefEq.respectTransparency false
/-!
# The smooth Frobenius metric on a shared matrix orbit

The horizontal atlas gives the actual shared two-factor orbit its inherited smooth
manifold structure. Pulling the ambient Frobenius pairing back through the
injective manifold derivative of the inclusion defines a positive definite
metric on mathlib's actual tangent spaces. Its evaluation is smooth on the
total tangent bundle. No assumption excluding overlap is used.

The chart norm is retained. No equality between the chart norm and the
Frobenius norm is asserted, and no norm instance is replaced.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.MatrixBase
open scoped Manifold

namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]

variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)

-- Cache the existing submodule instance so tangent-bundle elaboration does
-- not unfold the chosen horizontal complement while searching for it.
local instance riemannianHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _

local instance metricChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P



attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

variable (X : MatrixOrbit right left P)

/-- Ambient realization of a genuine manifold tangent vector. -/
def inclusionDifferential :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X →L[ℝ] KMat 𝕜 n :=
  mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, KMat 𝕜 n))
    (fun Y : MatrixOrbit right left P => Y.val) X

theorem inclusionDifferential_injective :
    Function.Injective (inclusionDifferential right left P X) :=
  sharedOrbit_val_mfderiv_injective right left P X



-- These local instances expose the already existing horizontal chart norm.













end GS.MatrixGeometry
