/-
Constructs the native DN-kernel tangent coordinates
from actual inverse laws, and the actual trace/3 metric and three-slot cubic
bindings. The generic part uses an explicit metric FRAME only: an algebraic
coordinate choice, never a recognized norm/unit/product equivalence. Actual
full scalar four-curvature equality is equivalent to native q equality, so the
unrestricted q-fiber theorem applies. No normed native Albert/V.
-/
module

public import AlbertGeometry.LeviCivitaCurvature
public import AlbertGeometry.NativeTracefreeFormBinding
public import AlbertRecognition.CubicFiber
public import AlbertRecognition.RecoveryCoordinates
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section
namespace AlbertGeometry.NativeCurvatureDictionary
noncomputable section
open AlbertRecognition
open AlbertGeometry.Cubic AlbertGeometry.CubicPolynomialRepresentation
open AlbertGeometry.NativeNormAlgebra AlbertGeometry.NativeEuclideanNormBinding
open AlbertGeometry.NativeCoordinateDerivatives AlbertGeometry.NativeCoordinateDictionary
open AlbertGeometry.NativeTracefreeFormBinding
open scoped BigOperators

-- Reuse the same canonical tangent operator norms used in LeviCivitaConnection. These
-- are existing instances on the actual DN-kernel, never a norm on algebraic V.
attribute [local instance] pullbackMetricDualNormedAddCommGroup pullbackMetricDualNormedSpace
  pullbackMetricBilinearNormedAddCommGroup pullbackMetricBilinearNormedSpace
  pullbackMetricTrilinearNormedAddCommGroup pullbackMetricTrilinearNormedSpace
  lcEndNormedAddCommGroup lcEndNormedSpace
  lcBilinearVectorNormedAddCommGroup lcBilinearVectorNormedSpace
  lcInverseNormedAddCommGroup lcInverseNormedSpace

/-- Normalization of the genuine native coordinate cubic at the actual unit. -/
theorem nativeNormalization :
    diagonalCubic nativeEuclideanRepresentation.form nativeCoordinateUnit = 1 := by
  rw [diagonal_nativeEuclideanRepresentation, delta_nativeCoordinateUnit,
    nativeNewtonNorm_one]

/-- Genuine ambient positivity, proved by native raw-inner positivity, not
assumed from norm positivity or imposed by a new normed Albert instance. -/
theorem nativeBaseMetricPositive (u : Coordinates) (hu : u ≠ 0) :
    0 < logHessianForm nativeEuclideanRepresentation nativeCoordinateUnit u u := by
  rw [← coordinateLogMetric_eq_logHessianForm, coordinateLogMetric_at_unit]
  have := (Glennie.inner_self_nonneg (delta u)).lt_of_ne'
    ((Glennie.inner_self_eq_zero _).not.2 (delta.map_ne_zero_iff.2 hu))
  linarith

abbrev NativeChartTangent := tangentSpace nativeEuclideanRepresentation nativeCoordinateUnit

/-- The old native tangent and the actual chart tangent are the SAME kernel,
by equality of the whole Newton and continuous diagonal functions. -/
theorem nativeTangentSpace_eq :
    nativeCoordinateTangentSpace =
      tangentSpace nativeEuclideanRepresentation nativeCoordinateUnit := by simp [nativeCoordinateTangentSpace, tangentSpace, coordinateNewton_eq_diagonal]

/-- Constructed actual Euclidean26-to-chart-tangent CLEquiv. No inverse or
native topology is a premise. Equal-submodule coercion changes no vector. -/
def nativeChartCoordinates : TracefreeCoordinates ≃L[ℝ] NativeChartTangent :=
  tangentCoordinatesContinuous.trans
    (LinearEquiv.ofEq nativeCoordinateTangentSpace
      (tangentSpace nativeEuclideanRepresentation nativeCoordinateUnit)
      nativeTangentSpace_eq).toContinuousLinearEquiv

@[simp] theorem nativeChartCoordinates_coe (v : TracefreeCoordinates) :
    (nativeChartCoordinates v : Coordinates) = tracefreeCoordinateMap v := by rfl

/-- The frame into the actual tangent is entirely constructed through Euclidean
coordinates. V remains an algebraic carrier throughout. -/
def nativeMetricFrame : V ≃ₗ[ℝ] NativeChartTangent :=
  tracefreeCoordinates.symm.trans nativeChartCoordinates.toLinearEquiv

@[simp] theorem nativeMetricFrame_coe (x : V) :
    (nativeMetricFrame x : Coordinates) = tracefreeCoordinateMap (tracefreeCoordinates.symm x) :=
  nativeChartCoordinates_coe _

/-- Full actual normalized metric identity, not unscaled native/Pi-infinity norm. -/
theorem nativeMetricFrame_metric (x y : V) :
    baseChartMetric nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization
      (nativeMetricFrame x) (nativeMetricFrame y) = gA x y := by
  rw [baseChartMetric_apply, nativeMetricFrame_coe, nativeMetricFrame_coe,
    ← coordinateLogMetric_eq_logHessianForm, tracefreeCoordinateMap_metric]
  have h := tracefreeCoordinates_metric (tracefreeCoordinates.symm x)
    (tracefreeCoordinates.symm y)
  simpa [gA, LinearEquiv.apply_symm_apply] using h.symm

/-- Full three-slot equality with the native reference cubic. The
native form and reference cubic already contain exactly ONE division by3. -/
theorem nativeMetricFrame_cubic (x y z : V) :
    nativeEuclideanRepresentation.form
      ![(nativeMetricFrame x : Coordinates), (nativeMetricFrame y : Coordinates),
        (nativeMetricFrame z : Coordinates)] = referenceCubic.form x y z := by
  rw [nativeMetricFrame_coe, nativeMetricFrame_coe, nativeMetricFrame_coe,
    nativeEuclideanForm_tracefree]
  simp [coordinateReferenceCubic, LinearEquiv.apply_symm_apply]

section GenericMetricFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- All intermediate modules are fixed by these structure fields. No inferred
-- composition module and no topology or norm on the algebraic carrier V is used.
def frameAmbientMap (P : SymmetricTrilinearForm E) (e : E)
    (F : V ≃ₗ[ℝ] tangentSpace P e) : V →ₗ[ℝ] E :=
  (tangentSpace P e).subtype ∘ₗ F.toLinearMap

def frameTrilinearForm (P : SymmetricTrilinearForm E) (e : E)
    (F : V ≃ₗ[ℝ] tangentSpace P e) : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.lcomp ℝ _ (frameAmbientMap P e F) ∘ₗ LinearMap.llcomp ℝ _ _ _
    (LinearMap.lcomp ℝ ℝ (frameAmbientMap P e F) ∘ₗ ContinuousLinearMap.coeLM ℝ) ∘ₗ
    ContinuousLinearMap.coeLM ℝ ∘ₗ (fullyCurried P).toLinearMap ∘ₗ frameAmbientMap P e F

-- These witnesses concern structure projections only, not a new metric/product.

theorem frameTrilinearForm_apply (P : SymmetricTrilinearForm E) (e : E)
    (F : V ≃ₗ[ℝ] tangentSpace P e) (x y z : V) :
    frameTrilinearForm P e F x y z =
      fullyCurried P (F x : E) (F y : E) (F z : E) := by
  rfl

/-- Literal tangent coefficients in an algebraic metric frame. This is a
coordinate pullback, not an assumed native/unknown cubic recognition. -/
def frameCubic (P : SymmetricTrilinearForm E) (e : E)
    (F : V ≃ₗ[ℝ] tangentSpace P e) : SymmetricCubic where
  form := frameTrilinearForm P e F
  swap12 x y z := by simpa [frameTrilinearForm_apply, fullyCurried_apply] using P.swap12 _ _ _
  swap23 x y z := by simpa [frameTrilinearForm_apply, fullyCurried_apply] using P.swap23 _ _ _

@[simp] theorem frameCubic_apply (P : SymmetricTrilinearForm E) (e : E)
    (F : V ≃ₗ[ℝ] tangentSpace P e) (x y z : V) :
    (frameCubic P e F).form x y z = P.form ![(F x : E), (F y : E), (F z : E)] :=
  fullyCurried_apply ..

/-- Literal scalar FOUR-tensor of the ACTUAL Levi-Civita curvature, in F.
The desired native q formula does not occur in this definition. -/
def scalarCurvatureInFrame (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (F : V ≃ₗ[ℝ] tangentSpace P e)
    (x y z w : V) : ℝ :=
  let r := chartCurvature P e he (0 : tangentSpace P e) (F x) (F y) (F z)
  let metric := (baseChartMetric P e he).toLinearMap
  let metricAt := (metric r).toLinearMap
  metricAt (F w)

variable [FiniteDimensional ℝ E]

/-- The unknown tangent K and native KB of its literal coordinate
cubic are the SAME raised operator under the metric frame, proved by pairing. -/
theorem raisedTangentCubic_frame (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (F : V ≃ₗ[ℝ] tangentSpace P e)
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
    (hmetric : ∀ x y : V, baseChartMetric P e he (F x) (F y) = gA x y)
    (x y : V) :
    raisedTangentCubic P e he (F x) (F y) = F (KB (frameCubic P e F) x y) := by
  have h0 := (leviCivitaChartDomain_spec P e he hpos).2.1
  apply pullbackMetric_dual_injective P e he hpos 0 h0
  ext w
  obtain ⟨w, rfl⟩ := F.surjective w
  change baseChartMetric P e he
      (raisedTangentCubic P e he (F x) (F y)) (F w) =
    baseChartMetric P e he (F (KB (frameCubic P e F) x y)) (F w)
  rw [raisedTangentCubic_pairing P e he hpos, hmetric, KB_pairing, frameCubic_apply]

/-- Exact q/sign/metric dictionary from genuine curvature, for ALL four slots. -/
theorem scalarCurvatureInFrame_eq_native_q (P : SymmetricTrilinearForm E) (e : E)
    (he : diagonalCubic P.form e = 1) (F : V ≃ₗ[ℝ] tangentSpace P e)
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
    (hmetric : ∀ x y : V, baseChartMetric P e he (F x) (F y) = gA x y)
    (x y z w : V) :
    scalarCurvatureInFrame P e he F x y z w =
      -(gA y z * gA x w - gA x z * gA y w) -
        gA (q (frameCubic P e F) x y z) w := by
  rw [scalarCurvatureInFrame, chartCurvature_zero P e he hpos]
  simp only [ContinuousLinearMap.coe_coe, baseMetricWedge, raisedCubicCommutator,
    map_sub, map_neg,
    map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [raisedTangentCubic_frame P e he F hpos hmetric,
    raisedTangentCubic_frame P e he F hpos hmetric,
    raisedTangentCubic_frame P e he F hpos hmetric,
    raisedTangentCubic_frame P e he F hpos hmetric]
  simp [hmetric, q, operatorComm_apply]
  simp [gA, Glennie.inner_sub_left, sub_div]

end GenericMetricFrame

/-- The native extracted cubic is actually referenceCubic; there is no
reference-cubic equality field or assumed recognized isomorphism. -/
theorem frameCubic_native :
    frameCubic nativeEuclideanRepresentation nativeCoordinateUnit nativeMetricFrame =
      referenceCubic := by
  apply symmetricCubic_eq_of_form_eq
  ext x y z
  rw [frameCubic_apply, nativeMetricFrame_cubic]

/-- Actual native scalar four-curvature is defined through the produced chart. -/
def nativeScalarCurvature (x y z w : V) : ℝ :=
  scalarCurvatureInFrame nativeEuclideanRepresentation nativeCoordinateUnit
    nativeNormalization nativeMetricFrame x y z w

theorem nativeScalarCurvature_eq_native_q (x y z w : V) :
    nativeScalarCurvature x y z w =
      -(gA y z * gA x w - gA x z * gA y w) - gA (q referenceCubic x y z) w := by
  rw [nativeScalarCurvature, scalarCurvatureInFrame_eq_native_q
    nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization nativeMetricFrame
    nativeBaseMetricPositive nativeMetricFrame_metric, frameCubic_native]

/-- Actual native curvature value transported back algebraically from the
constructed chart tangent, without a prescribed native curvature expression. -/
def nativeCurvatureValue (x y z : V) : V :=
  nativeMetricFrame.symm
    (chartCurvature nativeEuclideanRepresentation nativeCoordinateUnit nativeNormalization
      0 (nativeMetricFrame x) (nativeMetricFrame y) (nativeMetricFrame z))

theorem nativeCurvatureValue_pairing (x y z w : V) :
    gA (nativeCurvatureValue x y z) w = nativeScalarCurvature x y z w := by
  have h := nativeMetricFrame_metric (nativeCurvatureValue x y z) w
  simp [nativeCurvatureValue, LinearEquiv.apply_symm_apply] at h
  simpa [nativeCurvatureValue, nativeScalarCurvature, scalarCurvatureInFrame,
    ContinuousLinearMap.coe_coe] using h.symm

section RecoveryFromActualCurvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
variable (F : V ≃ₗ[ℝ] tangentSpace P e)
variable (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
variable (hmetric : ∀ x y : V,
  baseChartMetric P e he (F x) (F y) = gA x y)

include hpos hmetric in
/-- Full actual curvature tensor matching and scalar-four matching are
literally equivalent by actual metric nondegeneracy in the two frames. -/
theorem fullCurvature_matches_iff_scalar :
    (∀ x y z : V, chartCurvature P e he 0 (F x) (F y) (F z) =
      F (nativeCurvatureValue x y z)) ↔
    (∀ x y z w : V,
      scalarCurvatureInFrame P e he F x y z w = nativeScalarCurvature x y z w) := by
  constructor
  · intro hR x y z w
    rw [scalarCurvatureInFrame, hR x y z]
    simp only [ContinuousLinearMap.coe_coe]
    rw [hmetric, nativeCurvatureValue_pairing]
  · intro hR x y z
    have h0 := (leviCivitaChartDomain_spec P e he hpos).2.1
    apply pullbackMetric_dual_injective P e he hpos 0 h0
    ext w
    obtain ⟨w, rfl⟩ := F.surjective w
    change scalarCurvatureInFrame P e he F x y z w =
      baseChartMetric P e he (F (nativeCurvatureValue x y z)) (F w)
    rw [hR, hmetric, nativeCurvatureValue_pairing]

include hpos hmetric in
/-- FULL actual scalar four-curvature matching is equivalent to the unrestricted native quadratic fiber, with metric and wedge fixed.
Metric nondegeneracy proves the reverse dictionary; no partial sectional data. -/
theorem scalarCurvature_matches_iff_q :
    (∀ x y z w : V, scalarCurvatureInFrame P e he F x y z w = nativeScalarCurvature x y z w) ↔
      q (frameCubic P e F) = q referenceCubic := by
  constructor
  · intro hR
    funext x y
    apply LinearMap.ext
    intro z
    apply metricDual.injective
    apply LinearMap.ext
    intro w
    change gA (q (frameCubic P e F) x y z) w = gA (q referenceCubic x y z) w
    have h := hR x y z w
    rw [scalarCurvatureInFrame_eq_native_q P e he F hpos hmetric,
      nativeScalarCurvature_eq_native_q] at h
    linarith
  · intro hq x y z w
    rw [scalarCurvatureInFrame_eq_native_q P e he F hpos hmetric,
      nativeScalarCurvature_eq_native_q, hq]

include hpos hmetric in
/-- Actual curvature yields the full ± reference cubic fiber in its
metric frame. Norm/product recognition is a separate derived integration. -/
theorem frameCubic_sign_of_actual_curvature
    (hR : ∀ x y z w : V,
      scalarCurvatureInFrame P e he F x y z w = nativeScalarCurvature x y z w) :
    frameCubic P e F = referenceCubic ∨
      frameCubic P e F = scalarCubic (-1) referenceCubic := by
  exact (q_fiber_reference (frameCubic P e F)).mp
    ((scalarCurvature_matches_iff_q P e he F hpos hmetric).mp hR)

include hpos hmetric in
/-- The same ± recovery follows from the FULL actual vector-valued
one-point curvature tensor under a metric coordinate frame. -/
theorem frameCubic_sign_of_full_curvature
    (hR : ∀ x y z : V, chartCurvature P e he 0 (F x) (F y) (F z) =
      F (nativeCurvatureValue x y z)) :
    frameCubic P e F = referenceCubic ∨
      frameCubic P e F = scalarCubic (-1) referenceCubic := by
  exact frameCubic_sign_of_actual_curvature P e he F hpos hmetric
    ((fullCurvature_matches_iff_scalar P e he F hpos hmetric).mp hR)

end RecoveryFromActualCurvature
end
end AlbertGeometry.NativeCurvatureDictionary
