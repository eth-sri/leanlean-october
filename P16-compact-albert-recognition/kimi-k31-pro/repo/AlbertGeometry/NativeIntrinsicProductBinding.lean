/-
Native norm/unit roundtrip. The raw pairing is the ACTUAL
DN/D2N pairing and is identified with literal native inner through the proved
coordinate derivatives. Its nondegeneracy is derived from native positive
separation and the algebraic delta equivalence. The generic toDual adjoint is
identified by its genuine derivative pairing, not by defining it to be native.
Unhalved cross and halved intrinsic product then return literal native jordan.
All normed objects live on existing Euclidean coordinates; no norm on Albert,
unknown Jordan premise, assumed adjoint identity, or recognition map is input.
-/
module

public import AlbertGeometry.NativeCoordinateDerivatives
public import AlbertGeometry.BasedNormAdjointTransport

@[expose] public section
namespace AlbertGeometry.NativeIntrinsicProductBinding
noncomputable section
open Module Glennie
open AlbertGeometry.Cubic AlbertGeometry.NativeNormAlgebra
open AlbertGeometry.CubicPolynomialRepresentation AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport

/-- Actual DN at the actual native unit is native trace in algebraic coordinates. -/
theorem native_normTrace (x : Coordinates) :
    normTrace nativeEuclideanRepresentation nativeCoordinateUnit x = Glennie.trace (delta x) := by
  change fderiv ℝ (diagonalCubic nativeEuclideanRepresentation.form) nativeCoordinateUnit x = _
  rw [← coordinateNewton_eq_diagonal]
  exact fderiv_coordinateNewton_at_unit x

/-- Genuine second derivative, already proved from actual scalar differentiation. -/
theorem native_cubicHessian_unit (x y : Coordinates) :
    cubicHessian nativeEuclideanRepresentation nativeCoordinateUnit x y =
      Glennie.trace (delta x) * Glennie.trace (delta y) - Glennie.inner (delta x) (delta y) := by
  rw [← coordinateNewtonHessian_eq_cubicHessian]
  exact coordinateNewtonHessian_at_unit x y

/-- Full27 ACTUAL raw derivative pairing, not an installed native inner product. -/
theorem native_rawTraceForm (x y : Coordinates) :
    rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit x y =
      Glennie.inner (delta x) (delta y) := by
  rw [rawTraceForm_apply, native_normTrace, native_normTrace, native_cubicHessian_unit]
  ring

/-- Algebraic projection of the actual raw continuous form for its genuine dual. -/
def nativeRawBilinear : LinearMap.BilinForm ℝ Coordinates :=
  rawBilinearForm nativeEuclideanRepresentation nativeCoordinateUnit

@[simp] theorem nativeRawBilinear_apply (x y : Coordinates) :
    nativeRawBilinear x y = Glennie.inner (delta x) (delta y) := native_rawTraceForm x y

/-- No base positivity hypothesis is added: separation is a native theorem. -/
theorem nativeRawBilinear_nondegenerate : nativeRawBilinear.Nondegenerate := by
  constructor
  · intro x hx
    have hzero : Glennie.inner (delta x) (delta x) = 0 := by
      simpa only [nativeRawBilinear_apply] using hx x
    apply delta.injective
    simpa only [map_zero] using (inner_self_eq_zero (delta x)).mp hzero
  · intro x hx
    have hzero : Glennie.inner (delta x) (delta x) = 0 := by
      simpa only [nativeRawBilinear_apply] using hx x
    apply delta.injective
    simpa only [map_zero] using (inner_self_eq_zero (delta x)).mp hzero

/-- The actual finite-dimensional toDual equivalence, with derived certificate. -/
def nativeRawDual : Coordinates ≃ₗ[ℝ] Module.Dual ℝ Coordinates :=
  nativeRawBilinear.toDual nativeRawBilinear_nondegenerate

@[simp] theorem nativeRawDual_apply (x y : Coordinates) :
    nativeRawDual x y = Glennie.inner (delta x) (delta y) := nativeRawBilinear_apply x y

/-- Intrinsic producer supplied by actual DN and actual raw toDual inversion. -/
def nativeIntrinsicAdjoint (x : Coordinates) : Coordinates :=
  intrinsicAdjoint nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate x

/-- Existence/uniqueness pairing identifies the genuine intrinsic adjoint with
literal native adjoint; the native formula is not its definition. -/
theorem nativeIntrinsicAdjoint_eq (x : Coordinates) :
    nativeIntrinsicAdjoint x = delta.symm (nativeAdjoint (delta x)) := by
  symm
  apply intrinsicAdjoint_unique nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate
  intro y
  rw [native_rawTraceForm, LinearEquiv.apply_symm_apply, ← coordinateNewton_eq_diagonal]
  exact (fderiv_coordinateNewton_apply x y).symm

theorem delta_nativeIntrinsicAdjoint (x : Coordinates) :
    delta (nativeIntrinsicAdjoint x) = nativeAdjoint (delta x) := by
  rw [nativeIntrinsicAdjoint_eq, LinearEquiv.apply_symm_apply]

/-- Generic actual unhalved polarization, as an actual coordinate function. -/
def nativeIntrinsicCross (x y : Coordinates) : Coordinates :=
  intrinsicCross nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate x y

theorem delta_nativeIntrinsicCross (x y : Coordinates) :
    delta (nativeIntrinsicCross x y) = nativeCross (delta x) (delta y) := by
  change delta (nativeIntrinsicAdjoint (x + y) - nativeIntrinsicAdjoint x -
    nativeIntrinsicAdjoint y) = _
  simp only [map_sub, delta_nativeIntrinsicAdjoint, map_add, nativeCross]

theorem native_intrinsicS (x y : Coordinates) :
    intrinsicS nativeEuclideanRepresentation nativeCoordinateUnit x y =
      Glennie.trace (delta x) * Glennie.trace (delta y) - Glennie.inner (delta x) (delta y) := by
  simp only [intrinsicS, native_normTrace, native_rawTraceForm]

/-- Genuine generic half-product computed from actual norm/unit derivatives. -/
def nativeIntrinsicProduct (x y : Coordinates) : Coordinates :=
  intrinsicProduct nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate x y

/-- The decisive literal roundtrip, for all full27 coordinate vectors. -/
theorem delta_nativeIntrinsicProduct (x y : Coordinates) :
    delta (nativeIntrinsicProduct x y) = jordan (delta x) (delta y) := by
  calc
    delta (nativeIntrinsicProduct x y) = nativeRecoveredProduct (delta x) (delta y) := by
      change delta ((1/2 : ℝ) • (nativeIntrinsicCross x y +
        normTrace nativeEuclideanRepresentation nativeCoordinateUnit x • y +
        normTrace nativeEuclideanRepresentation nativeCoordinateUnit y • x -
        intrinsicS nativeEuclideanRepresentation nativeCoordinateUnit x y • nativeCoordinateUnit)) = _
      simp only [map_smul, map_add, map_sub, delta_nativeIntrinsicCross,
        native_normTrace, native_intrinsicS, delta_nativeCoordinateUnit, nativeRecoveredProduct]
      module
    _ = jordan (delta x) (delta y) := nativeRecoveredProduct_eq _ _

end
end AlbertGeometry.NativeIntrinsicProductBinding
