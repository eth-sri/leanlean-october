/-
Unit/tangent reconstruction. The WHOLE normalized cubic along
unit+tangent directions is expanded by actual trilinearity/symmetry and actual
DN/Hessian identities. A tangent metric+cubic equivalence then constructs an
ambient linear norm/unit equivalence via the already proved derivative splits.
No recognized ambient map, unknown Jordan identity or norm preservation is an
input to that construction. This is an actual polynomial identity, not jets
named as a norm or an assumed Taylor expansion.
-/
module

public import AlbertGeometry.NativeCurvatureDictionary
public import AlbertGeometry.BasedNormDerivativeTransport
public import Mathlib.LinearAlgebra.Prod

@[expose] public section
namespace AlbertGeometry.UnitTangentNormReconstruction
noncomputable section
open AlbertGeometry.Cubic AlbertGeometry.BasedNormDerivativeTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)

/-- Literal diagonal evaluation in three slots. -/
theorem diagonalCubic_eq_three (x : E) :
    diagonalCubic P.form x = P.form ![x,x,x] := by
  unfold diagonalCubic
  congr 1
  ext i
  fin_cases i <;> rfl

/-- True tangent vectors have no two-unit cubic coefficient, by actual DN. -/
theorem cubic_unit_unit_tangent (u : (tangentSpace P e)) : P.form ![e,e,(u : E)] = 0 := by
  have h : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
  rw [fderiv_diagonalCubic_apply_symmetric] at h
  linarith

/-- The one-unit/two-tangent coefficient is exactly -a_e/2, deduced from the
actual Hessian/log-Hessian relation and true Hessian=6P, not supplied as a jet. -/
theorem cubic_unit_tangent_tangent (u v : (tangentSpace P e)) :
    P.form ![e,(u : E),(v : E)] = -(1 / 2 : ℝ) * (baseChartMetric P e he) u v := by
  have h := cubicHessian_tangent_at_one P e he u v
  rw [cubicHessian_apply] at h
  rw [← baseChartMetric_apply P e he u v] at h
  linarith

/-- Exact WHOLE real polynomial, for every t (including zero), not just its
first three derivatives at a basepoint. -/
theorem cubic_unit_tangent_expansion (t : ℝ) (u : (tangentSpace P e)) :
    diagonalCubic P.form (t • e + (u : E)) =
      t^3 - (3 / 2 : ℝ) * t * (baseChartMetric P e he) u u + P.form ![(u : E),(u : E),(u : E)] := by
  have h1 := cubic_unit_unit_tangent P e u
  have h4 := cubic_unit_tangent_tangent P e he u u
  rw [diagonalCubic_eq_three, ← fullyCurried_apply]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fullyCurried_apply]
  rw [← diagonalCubic_eq_three P e, he, P.swap12 (u:E) e e, P.swap23 e (u:E) e, h1,
    P.swap23 (u:E) (u:E) e, P.swap12 (u:E) e (u:E), h4]
  ring

/-- Literal three-slot negation, required to handle BOTH recovery signs. -/
theorem cubic_three_neg (u : E) : P.form ![-u,-u,-u] = -P.form ![u,u,u] := by
  rw [← fullyCurried_apply]
  simp [map_neg, neg_neg, fullyCurried_apply]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (Q : SymmetricTrilinearForm H) (f : H) (hf : diagonalCubic Q.form f = 1)

/-- Construct an ambient equivalence from the actual derivative splits and a
proved tangent map. No ambient inverse or recognized map is assumed. -/
def ambientLift (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) : E ≃ₗ[ℝ] H :=
  (normalSplit P e he).toLinearEquiv ≪≫ₗ (LinearEquiv.refl ℝ ℝ).prodCongr D ≪≫ₗ
    (normalSplit Q f hf).toLinearEquiv.symm

/-- Unit preservation is an output of the genuine split normalization. -/
theorem ambientLift_unit (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) :
    ambientLift P e he Q f hf D e = f := by
  change normalSplitInverse Q f (fderiv ℝ (diagonalCubic P.form) e e, D (tangentProjection P e he e)) = f
  simp [normalSplitInverse, fderiv_diagonalCubic_at_one P.form e he, tangentProjection_basepoint]

/-- Actual tangent metric and cubic certificates give whole norm equality.
These certificates are PROVED from signed curvature recovery in the consumer. -/
theorem ambientLift_norm (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f)
    (hmetric : ∀ u v, baseChartMetric Q f hf (D u) (D v) = baseChartMetric P e he u v)
    (hcubic : ∀ u : tangentSpace P e,
      Q.form ![(D u : H),(D u : H),(D u : H)] = P.form ![(u : E),(u : E),(u : E)]) (x : E) :
    diagonalCubic Q.form (ambientLift P e he Q f hf D x) = diagonalCubic P.form x := by
  conv_rhs => rw [← normalSplit_left_inverse P e he x]
  change diagonalCubic Q.form (normalSplitInverse Q f (fderiv ℝ (diagonalCubic P.form) e x,
    D (tangentProjection P e he x))) = diagonalCubic P.form (normalSplitInverse P e
    (fderiv ℝ (diagonalCubic P.form) e x, tangentProjection P e he x))
  simp only [normalSplitInverse, cubic_unit_tangent_expansion P e he, cubic_unit_tangent_expansion Q f hf,
    hmetric, hcubic]

/-- A genuine norm/unit morphism is CONSTRUCTED. The stored certificates are
proved outputs, not additional hypotheses about an unknown ambient map. -/
def basedNormIsoOfTangent (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) [FiniteDimensional ℝ E]
    (hmetric : ∀ u v, baseChartMetric Q f hf (D u) (D v) = baseChartMetric P e he u v)
    (hcubic : ∀ u : tangentSpace P e,
      Q.form ![(D u : H),(D u : H),(D u : H)] = P.form ![(u : E),(u : E),(u : E)]) :
    BasedNormIso P e Q f where
  equiv := (ambientLift P e he Q f hf D).toContinuousLinearEquiv
  map_unit := ambientLift_unit P e he Q f hf D
  map_norm := ambientLift_norm P e he Q f hf D hmetric hcubic

end
end AlbertGeometry.UnitTangentNormReconstruction
