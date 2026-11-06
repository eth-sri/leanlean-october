module

public import GS.SharedGeometry.OrbitAtlas
public import GS.RiemannianCompletion.FrobeniusDual
public import GS.Extensions.FiniteTopology
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.CayleyCharts
open GS.RiemannianCompletion
open scoped Manifold Topology

namespace GS.SharedGeometry

variable {n : ℕ} (right left : Pattern n) (P : Mat n)

-- Cache the existing submodule instance so tangent-bundle elaboration does
-- not unfold the chosen horizontal complement while searching for it.
local instance horizontalNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _

local instance metricChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

local instance metricIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Ambient realization of a genuine manifold tangent vector. -/
def inclusionDifferential (X : MatrixOrbit right left P) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X →L[ℝ] Mat n :=
  mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
    (fun Y : MatrixOrbit right left P => Y.val) X

theorem inclusionDifferential_injective (X : MatrixOrbit right left P) :
    Function.Injective (inclusionDifferential right left P X) :=
  sharedOrbit_val_mfderiv_injective right left P X

/-- The Frobenius pullback on the true tangent fibre, using the horizontal
atlas and allowing continuous stabilizers. -/
def tangentPairing (X : MatrixOrbit right left P)
    (v w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) : ℝ :=
  frobInner (inclusionDifferential right left P X v)
    (inclusionDifferential right left P X w)

theorem tangentPairing_add_left (X : MatrixOrbit right left P)
    (u v w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (u + v) w =
      tangentPairing right left P X u w + tangentPairing right left P X v w := by
  unfold tangentPairing
  rw [map_add, frobInner_add_left]

theorem tangentPairing_smul_left (X : MatrixOrbit right left P)
    (a : ℝ) (v w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (a • v) w = a * tangentPairing right left P X v w := by
  unfold tangentPairing
  rw [map_smul, frobInner_smul_left]

@[simp] theorem tangentPairing_zero_left (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X 0 v = 0 := by simp [tangentPairing]

theorem tangentPairing_self_eq_zero_iff (X : MatrixOrbit right left P)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X v v = 0 ↔ v = 0 := by
  change frobSq (inclusionDifferential right left P X v) = 0 ↔ v = 0
  rw [frobSq_eq_zero_iff]
  constructor
  · intro h
    apply inclusionDifferential_injective right left P X
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

/-- Ambient realization on the actual total tangent bundle. -/
def tangentAmbient
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P))
      (MatrixOrbit right left P)) : Mat n :=
  inclusionDifferential right left P p.proj p.2

theorem tangentAmbient_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent (𝓘(ℝ, Mat n)) ⊤
      (tangentAmbient right left P) := by
  exact (contMDiff_snd_tangentBundle_modelSpace (Mat n) (𝓘(ℝ, Mat n))).comp
    ((sharedOrbit_val_contMDiff right left P).contMDiff_tangentMap (by simp))

end GS.SharedGeometry
