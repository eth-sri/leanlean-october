/-
Native coordinate dictionary. The determinant identity is
proved by expanding literal compact binary octMul/trace/jordan coordinates.
The actual26 tracefree basis gives an algebraic adapter and explicit metric and
cubic equalities; no normed Albert or native isometry instance is introduced.
Reference CA already contains the raw-pairing division by3; no second division.
All products here are literal native jordan, with its matrix symmetrization1/2.
No general cubic recognition or norm/unit-preserving-is-product claim appears.
-/
module

public import AlbertGeometry.NativeCoordinateDerivatives
public import AlbertRecognition.RecoveryCoordinates
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section
namespace AlbertGeometry.NativeCoordinateDictionary
noncomputable section
open Module Glennie AlbertRecognition
open AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeNormAlgebra AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives
open scoped BigOperators Quaternion

/-- Literal upper-coordinate compact determinant with the fixed triangle order. -/
def nativeDeterminant (x : Albert) : ℝ :=
  x.d0 * x.d1 * x.d2 - x.d0 * octNormSq x.o12 -
    x.d1 * octNormSq x.o02 - x.d2 * octNormSq x.o01 +
    2 * octRe (octMul (octMul x.o01 x.o12) (octConj x.o02))

-- Declaration-scoped resource budget for literal coordinate expansion.

/-- Independent actual binary-coordinate expansion; no determinant identity is
an input, and no associative octonion/matrix law is invoked. -/
theorem nativeNewtonNorm_eq_nativeDeterminant (x : Albert) :
    nativeNewtonNorm x = nativeDeterminant x := by
  simp [nativeNewtonNorm, nativeDeterminant, Glennie.inner, Glennie.trace, oct_simps, octRe]
  ring

abbrev TracefreeCoordinates := EuclideanSpace ℝ (Fin 26)

/-- The actual normalized26 basis is algebraically transported from real
Euclidean coordinates. There is no native/topological instance on V. -/
def tracefreeCoordinates : TracefreeCoordinates ≃ₗ[ℝ] V :=
  (EuclideanSpace.equiv (Fin 26) ℝ).toLinearEquiv.trans
    RecoveryCoordinates.basis.equivFun.symm

theorem tracefreeCoordinates_repr (v : TracefreeCoordinates) (i : Fin 26) :
    RecoveryCoordinates.basis.repr (tracefreeCoordinates v) i = v i := by
  have h : RecoveryCoordinates.basis.equivFun (tracefreeCoordinates v) =
      (EuclideanSpace.equiv (Fin 26) ℝ) v := by
    exact RecoveryCoordinates.basis.equivFun.apply_symm_apply
      ((EuclideanSpace.equiv (Fin 26) ℝ) v)
  have hi := congrFun h i
  rw [Basis.equivFun_apply] at hi
  -- `simpa` compares reducibly here; `exact` compares at default transparency, where
  -- `⇑(EuclideanSpace.equiv _ _) v i` is `v.ofLp i` (PiLp.coe_continuousLinearEquiv is rfl).
  exact hi

/-- The native metric equality is proved from the actual basis coordinates,
not supplied as an isometry certificate or an installed inner-product instance. -/
theorem tracefreeCoordinates_metric (u v : TracefreeCoordinates) :
    Glennie.inner (tracefreeCoordinates u : Albert) (tracefreeCoordinates v : Albert) / 3 =
      ∑ i : Fin 26, u i * v i := by
  change gA (tracefreeCoordinates u) (tracefreeCoordinates v) = _
  rw [RecoveryCoordinates.metric_coordinates]
  simp [tracefreeCoordinates_repr]

/-- The literal native reference cubic, as a function of actual26 coordinates. -/
def coordinateReferenceCubic (u v w : TracefreeCoordinates) : ℝ :=
  referenceCubic.form (tracefreeCoordinates u) (tracefreeCoordinates v) (tracefreeCoordinates w)

theorem coordinateReferenceCubic_eq_raw_product (u v w : TracefreeCoordinates) :
    coordinateReferenceCubic u v w =
      Glennie.inner (jordan (tracefreeCoordinates u : Albert) (tracefreeCoordinates v : Albert))
        (tracefreeCoordinates w : Albert) / 3 := by
  exact CA_eq_native _ _ _

theorem coordinateReferenceCubic_diagonal (v : TracefreeCoordinates) :
    coordinateReferenceCubic v v v = nativeNewtonNorm (tracefreeCoordinates v : Albert) := by
  rw [coordinateReferenceCubic_eq_raw_product]
  unfold nativeNewtonNorm
  rw [trace_V]
  rw [inner_comm (jordan (tracefreeCoordinates v : Albert) (tracefreeCoordinates v : Albert))
    (tracefreeCoordinates v : Albert)]
  ring

/-- Actual full unit-plus-tracefree map; its inverse laws are proved below. -/
def normalizedNativePoint (t : ℝ) (v : TracefreeCoordinates) : Albert :=
  t • (1 : Albert) + (tracefreeCoordinates v : Albert)

theorem trace_normalizedNativePoint (t : ℝ) (v : TracefreeCoordinates) :
    Glennie.trace (normalizedNativePoint t v) = 3*t := by
  simp [normalizedNativePoint, trace_add, trace_smul, trace_unit, trace_V]
  ring

theorem project_normalizedNativePoint (t : ℝ) (v : TracefreeCoordinates) :
    project (normalizedNativePoint t v) = tracefreeCoordinates v := by
  apply Subtype.ext
  rw [project_coe]
  unfold Glennie.traceless
  rw [trace_normalizedNativePoint]
  have hc : (3*t)/3 = t := by ring
  rw [hc]
  unfold normalizedNativePoint
  module

/-- Full normalized metric equality; the reference Euclidean product metric
is compared as a scalar bilinear function, not installed on native Albert. -/
theorem normalizedNativePoint_metric (t s : ℝ) (v w : TracefreeCoordinates) :
    Glennie.inner (normalizedNativePoint t v) (normalizedNativePoint s w) / 3 =
      t*s + ∑ i : Fin 26, v i * w i := by
  calc
    Glennie.inner (normalizedNativePoint t v) (normalizedNativePoint s w) / 3 =
        t*s + Glennie.inner (tracefreeCoordinates v : Albert) (tracefreeCoordinates w : Albert)/3 := by
      simp [normalizedNativePoint, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, inner_unit_left, inner_unit_right, trace_add, trace_smul,
        trace_unit, trace_V]
      ring
    _ = _ := by rw [tracefreeCoordinates_metric]

/-- Actual ambient Euclidean coordinates of the normalized native point. -/
def normalizedCoordinatePoint (t : ℝ) (v : TracefreeCoordinates) : Coordinates :=
  delta.symm (normalizedNativePoint t v)

@[simp] theorem delta_normalizedCoordinatePoint (t : ℝ) (v : TracefreeCoordinates) :
    delta (normalizedCoordinatePoint t v) = normalizedNativePoint t v :=
  delta.apply_symm_apply _

theorem fderiv_coordinateNewton_unit_normalized (t : ℝ) (v : TracefreeCoordinates) :
    fderiv ℝ coordinateNewton nativeCoordinateUnit (normalizedCoordinatePoint t v) = 3*t := by
  rw [fderiv_coordinateNewton_at_unit, delta_normalizedCoordinatePoint, trace_normalizedNativePoint]

/-- The actual differential kernel condition on the26 coordinate directions. -/
theorem normalizedCoordinatePoint_tangent (v : TracefreeCoordinates) :
    fderiv ℝ coordinateNewton nativeCoordinateUnit (normalizedCoordinatePoint 0 v) = 0 := by
  rw [fderiv_coordinateNewton_unit_normalized]
  ring

/-- Actual geometric basepoint metric calibration on all normalized directions. -/
theorem coordinateLogMetric_unit_normalized (t s : ℝ) (v w : TracefreeCoordinates) :
    coordinateLogMetric nativeCoordinateUnit (normalizedCoordinatePoint t v)
      (normalizedCoordinatePoint s w) = t*s + ∑ i : Fin 26, v i*w i := by
  rw [coordinateLogMetric_at_unit, delta_normalizedCoordinatePoint, delta_normalizedCoordinatePoint]
  exact normalizedNativePoint_metric t s v w

/-- This CLM is constructed ONLY between two existing Euclidean normed carriers.
Intermediate V and Albert maps remain algebraic and acquire no norm instances. -/
def tracefreeCoordinateMap : TracefreeCoordinates →L[ℝ] Coordinates :=
  (delta.symm.toLinearMap.comp
    (traceFreeSpace.subtype.comp tracefreeCoordinates.toLinearMap)).toContinuousLinearMap

theorem tracefreeCoordinateMap_apply (v : TracefreeCoordinates) :
    tracefreeCoordinateMap v = normalizedCoordinatePoint 0 v := by
  change delta.symm (tracefreeCoordinates v : Albert) =
    delta.symm ((0 : ℝ) • (1 : Albert) + (tracefreeCoordinates v : Albert))
  simp

theorem tracefreeCoordinateMap_metric (u v : TracefreeCoordinates) :
    coordinateLogMetric nativeCoordinateUnit (tracefreeCoordinateMap u) (tracefreeCoordinateMap v) =
      ∑ i : Fin 26, u i*v i := by
  rw [tracefreeCoordinateMap_apply, tracefreeCoordinateMap_apply,
    coordinateLogMetric_unit_normalized]
  ring

end
end AlbertGeometry.NativeCoordinateDictionary
