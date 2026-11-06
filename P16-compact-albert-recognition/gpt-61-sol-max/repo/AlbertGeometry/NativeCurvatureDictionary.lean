/-
Constructs the native DN-kernel tangent coordinates
from actual inverse laws, and the actual trace/3 metric and three-slot cubic
bindings. The generic part uses an explicit metric FRAME only: an algebraic
coordinate choice, never a recognized norm/unit/product equivalence. Actual
full scalar four-curvature equality is equivalent to native q equality, so the
unrestricted q-fiber theorem applies. No normed native Albert/V.
-/
module
public import AlbertGeometry.LinearSimp
public import Mathlib.LinearAlgebra.Multilinear.Curry

public import AlbertGeometry.RegularLevelChart
public import AlbertGeometry.CubicHessian
public import AlbertGeometry.NativeCoordinateDerivatives
public import AlbertRecognition.CubicFiber
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section
namespace AlbertGeometry.NativeCurvatureDictionary
noncomputable section
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open Module Glennie AlbertRecognition
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives
abbrev NativeChartTangent := tangentSpace nativeEuclideanRepresentation nativeCoordinateUnit

/-- The actual DN kernel is the pullback of the native trace kernel. -/
theorem nativeTangentSpace_eq :
    tangentSpace nativeEuclideanRepresentation nativeCoordinateUnit =
      traceFreeSpace.comap delta.toLinearMap := by
  ext x
  change fderiv ℝ (diagonalCubic nativeEuclideanRepresentation.form)
    nativeCoordinateUnit x = 0 ↔ Glennie.trace (delta x) = 0
  change normTrace nativeEuclideanRepresentation nativeCoordinateUnit x = 0 ↔ _
  rw [native_normTrace]

/-- Restrict the native linear equivalence to the equal tangent kernels. -/
def nativeMetricFrame : V ≃ₗ[ℝ] NativeChartTangent :=
  (delta.ofSubmodule' traceFreeSpace).symm.trans
    (LinearEquiv.ofEq _ _ nativeTangentSpace_eq.symm)

@[simp] theorem nativeMetricFrame_coe (x : V) :
    (nativeMetricFrame x : Coordinates) = delta.symm (x : Albert) := rfl

theorem nativeMetricFrame_metric (x y : V) :
    logHessianForm nativeEuclideanRepresentation nativeCoordinateUnit
      (nativeMetricFrame x) (nativeMetricFrame y) = gA x y := by
  have h := AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso.rawTraceForm_eq_three_logMetric
    nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization
    (nativeMetricFrame x) (nativeMetricFrame y)
  rw [native_rawTraceForm, nativeMetricFrame_coe, nativeMetricFrame_coe,
    delta.apply_symm_apply, delta.apply_symm_apply] at h
  change _ = inner (x : Albert) (y : Albert) / 3
  rw [nativeMetricFrame_coe, nativeMetricFrame_coe]
  linarith


theorem nativeMetricFrame_cubic (x y z : V) :
    nativeEuclideanRepresentation.form
      ![(nativeMetricFrame x : Coordinates), (nativeMetricFrame y : Coordinates),
        (nativeMetricFrame z : Coordinates)] = referenceCubic.form x y z := by
  change rawNewtonPolarization (delta (nativeMetricFrame x))
    (delta (nativeMetricFrame y)) (delta (nativeMetricFrame z)) = _
  simp only [nativeMetricFrame_coe, LinearEquiv.apply_symm_apply,
    rawNewtonPolarization, trace_V, zero_mul, mul_zero, sub_zero, zero_add]
  change _ = CA x y z
  rw [CA_eq_native, ← inner_jordan_associative]
  ring

section GenericMetricFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
local notation "W" => tangentSpace P e
-- Apply the same actual metric and raised cubic by their explicit names.
-- Projected notation quotations are avoided; no quotation option is changed.
variable (F : V ≃ₗ[ℝ] tangentSpace P e)

-- All intermediate modules are fixed by these structure fields. No inferred
-- composition module and no topology or norm on the algebraic carrier V is used.
def frameTrilinearForm : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  ((P.form.toMultilinearMap.compLinearMap
    (fun _ => (tangentSpace P e).subtype.comp F.toLinearMap)).curryRight.curryRight).toLinearMap 0 0

private theorem frameTrilinearForm_apply (x y z : V) :
    frameTrilinearForm P e F x y z = P.form ![(F x : E), (F y : E), (F z : E)] := by
  simp only [frameTrilinearForm, MultilinearMap.toLinearMap_apply,
    MultilinearMap.curryRight_apply, MultilinearMap.compLinearMap_apply]
  apply congrArg P.form
  funext i
  fin_cases i <;> rfl

/-- Literal tangent coefficients in an algebraic metric frame. This is a
coordinate pullback, not an assumed native/unknown cubic recognition. -/
def frameCubic  : SymmetricCubic where
  form := frameTrilinearForm P e F
  swap12 x y z := by
    simpa only [frameTrilinearForm_apply] using P.swap12 (F x : E) (F y : E) (F z : E)
  swap23 x y z := by
    simpa only [frameTrilinearForm_apply] using P.swap23 (F x : E) (F y : E) (F z : E)

@[simp] theorem frameCubic_apply  (x y z : V) :
    (frameCubic P e F).form x y z = P.form ![(F x : E), (F y : E), (F z : E)] :=
  frameTrilinearForm_apply P e F x y z

end GenericMetricFrame

end
end AlbertGeometry.NativeCurvatureDictionary
