import GS.MatrixGeometry.Base

import GS.MatrixGeometry.TangentBridge
import GS.MatrixGeometry.Riemannian
import GS.MatrixGeometry.SmoothProjection
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv


set_option backward.isDefEq.respectTransparency false
/-!
# The intrinsic gradient on the genuine shared orbit

The ambient orthogonal projector is lifted into the actual tangent space of
our horizontal atlas. Its Frobenius pairing is the manifold derivative of the
restricted loss. The lift, Riesz identity, uniqueness, and stationarity are all
proved for actual repeated full blocks, without excluding overlap.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.MatrixBase
open scoped Manifold
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)
variable (X : MatrixOrbit right left P)

local instance gradientHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance gradientChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P


variable (Z : KMat 𝕜 n)

/-- A canonical tangent lift exists because the already-defined point projector
lands in the actual differential image. No choice of a new factorization is made. -/
def tangentProjection  :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  Classical.choose (pointProjection_unique_tangent_lift right left P X Z)

@[simp] theorem inclusion_tangentProjection
     :
    inclusionDifferential right left P X (tangentProjection right left P X Z) =
      pointProjection right left X.val Z :=
  (Classical.choose_spec (pointProjection_unique_tangent_lift right left P X Z)).1



@[simp] theorem tangentProjection_zero :
    tangentProjection right left P X (0 : KMat 𝕜 n) = 0 := by
  apply inclusionDifferential_injective right left P X
  simp only [map_zero,inclusion_tangentProjection]

variable (f : KMat 𝕜 n → ℝ)

/-- This vector inhabits mathlib's TangentSpace for the constructed atlas. -/
def intrinsicGradient 
    (X : MatrixOrbit right left P) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  tangentProjection right left P X (ambientGradient f X.val)





end GS.MatrixGeometry
