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
public import AlbertGeometry.AmbientLeviCivitaProduct

@[expose] public section
namespace AlbertGeometry.NativeIntrinsicProductBinding
noncomputable section
open Module Glennie
open AlbertGeometry.Cubic
open AlbertGeometry.CubicPolynomialRepresentation AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.BasedNormDerivativeTransport.BasedNormIso
open AlbertGeometry.BasedNormAdjointTransport

/-- Algebraic projection of the actual raw continuous form for its genuine dual. -/
def nativeRawBilinear : LinearMap.BilinForm ℝ Coordinates :=
  rawBilinearForm nativeEuclideanRepresentation nativeCoordinateUnit

@[simp] theorem nativeRawBilinear_apply (x y : Coordinates) :
    nativeRawBilinear x y = Glennie.inner (delta x) (delta y) := native_rawTraceForm x y

/-- No base positivity hypothesis is added: separation is a native theorem. -/
theorem nativeRawBilinear_nondegenerate : nativeRawBilinear.Nondegenerate := by
  constructor <;> intro x hx
  all_goals
    apply delta.injective
    simpa only [map_zero] using (inner_self_eq_zero (delta x)).mp
      (by simpa only [nativeRawBilinear_apply] using hx x)

def nativeIntrinsicProduct (x y : Coordinates) : Coordinates :=
  intrinsicProduct nativeEuclideanRepresentation nativeCoordinateUnit
    nativeRawBilinear_nondegenerate x y

theorem delta_nativeIntrinsicProduct (x y : Coordinates) :
    delta (nativeIntrinsicProduct x y) = jordan (delta x) (delta y) := by
  apply delta.symm.injective
  rw [delta.symm_apply_apply]
  apply ((rawBilinearForm nativeEuclideanRepresentation nativeCoordinateUnit).toDual
    nativeRawBilinear_nondegenerate).injective
  apply LinearMap.ext
  intro z
  change rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit
    (intrinsicProduct nativeEuclideanRepresentation nativeCoordinateUnit
      nativeRawBilinear_nondegenerate x y) z =
    rawTraceForm nativeEuclideanRepresentation nativeCoordinateUnit
      (delta.symm (jordan (delta x) (delta y))) z
  erw [AlbertGeometry.AmbientLeviCivitaProduct.intrinsicProduct_pairing
    nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization]
  simp only [intrinsicS, native_normTrace, native_rawTraceForm, LinearEquiv.apply_symm_apply]
  change 3 * rawNewtonPolarization (delta x) (delta y) (delta z) + _ = _
  simp only [rawNewtonPolarization, ← inner_jordan_associative]
  ring

end
end AlbertGeometry.NativeIntrinsicProductBinding
