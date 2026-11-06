module

public import GS.Shared.OrbitAtlas
public import GS.Extensions.FiniteTopology
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

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
open scoped Manifold Topology

namespace GS.Shared

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)

-- Cache the existing submodule instance so tangent-bundle elaboration does
-- not unfold the chosen horizontal complement while searching for it.
local instance riemannianHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _

local instance metricChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

local instance metricIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

attribute [local irreducible] sharedSkewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

section
variable (X : MatrixOrbit right left P)
/-- Ambient realization of a genuine manifold tangent vector. -/
def inclusionDifferential :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X →L[ℝ] 𝕄 :=
  mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, 𝕄))
    (fun Y : MatrixOrbit right left P => Y.val) X

theorem inclusionDifferential_injective :
    Function.Injective (inclusionDifferential right left P X) :=
  sharedOrbit_val_mfderiv_injective right left P X

/-- The Frobenius pullback on the true tangent fibre, using the horizontal
atlas and allowing continuous stabilizers. -/
def tangentPairing (v w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) : ℝ :=
  frob (inclusionDifferential right left P X v)
    (inclusionDifferential right left P X w)

theorem tangentPairing_add_left (u v w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (u + v) w =
      tangentPairing right left P X u w + tangentPairing right left P X v w := by
  unfold tangentPairing
  rw [map_add, frob_add_left]


theorem tangentPairing_smul_left (a : ℝ) (v w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (a • v) w = a * tangentPairing right left P X v w := by
  unfold tangentPairing
  rw [map_smul, frob_smul_left]


end

section
variable (X : MatrixOrbit right left P) (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X)
@[simp] theorem tangentPairing_zero_left :
    tangentPairing right left P X 0 v = 0 := by simp [tangentPairing]


theorem tangentPairing_self_eq_zero_iff :
    tangentPairing right left P X v v = 0 ↔ v = 0 := by
  change frob (inclusionDifferential right left P X v) (inclusionDifferential right left P X v) = 0 ↔ v = 0
  rw [frob_self_eq_zero]
  constructor
  · intro h
    apply inclusionDifferential_injective right left P X
    grind
  grind

end

-- These local instances expose the already existing horizontal chart norm.
section Fibrewise






end Fibrewise

/-- Ambient realization on the actual total tangent bundle. -/
def tangentAmbient
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P))
      (MatrixOrbit right left P)) : 𝕄 :=
  inclusionDifferential right left P p.proj p.2

theorem tangentAmbient_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent (𝓘(ℝ, 𝕄)) ⊤
      (tangentAmbient right left P) :=
  (contMDiff_snd_tangentBundle_modelSpace (𝕄) (𝓘(ℝ, 𝕄))).comp
    ((sharedOrbit_val_contMDiff right left P).contMDiff_tangentMap (by simp))





end GS.Shared
