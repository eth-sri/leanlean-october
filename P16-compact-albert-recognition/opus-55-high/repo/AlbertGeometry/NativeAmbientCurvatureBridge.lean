/-
Actual native ambient Levi-Civita curvature,
including every radial slot. Consumes the actual generic connection/curvature
and the preserved native derivative-defined product producer. The native
log-Hessian metric remains trace/3. No native normed-space instance is added.
-/
module

public import AlbertGeometry.AmbientCurvatureProduct
public import AlbertGeometry.NativeAmbientConnectionBridge

@[expose] public section
namespace AlbertGeometry.NativeAmbientCurvatureBridge
open Glennie
open AlbertGeometry.Cubic
open AlbertGeometry.BasedNormDerivativeTransport
open AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeIntrinsicProductBinding
open AlbertGeometry.NativeAmbientConnectionBridge
open AlbertGeometry.AmbientCurvatureProduct

local notation "QN" => nativeEuclideanRepresentation
local notation "en" => nativeCoordinateUnit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

include he hp in
/-- A supplied/constructed norm-unit map gives native actual curvature as a
derived output. No curvature-preservation field or unknown Jordan law is input. -/
theorem nativeRecognition_ambientCurvature
    (I : BasedNormIso P e QN en) (u v w : E) :
    delta (I.equiv (ambientCurvature P e u v w)) =
      -(jordan (delta (I.equiv u))
          (jordan (delta (I.equiv v)) (delta (I.equiv w))) -
        jordan (delta (I.equiv v))
          (jordan (delta (I.equiv u)) (delta (I.equiv w)))) := by
  rw [ambientCurvature_at_one_eq_neg_product_commutator P e he hp]
  simp [map_sub, nativeRecognition_product P e he hp I]

end AlbertGeometry.NativeAmbientCurvatureBridge
