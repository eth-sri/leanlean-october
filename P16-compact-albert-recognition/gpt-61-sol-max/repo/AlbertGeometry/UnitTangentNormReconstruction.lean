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
public import Mathlib.Tactic.Simps.Basic

public import AlbertGeometry.LinearSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

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

/- Exact WHOLE real polynomial, for every t (including zero), not just its
first three derivatives at a basepoint. -/
include he in
theorem cubic_unit_tangent_expansion (t : ℝ) (u : (tangentSpace P e)) :
    diagonalCubic P.form (t • e + (u : E)) =
      t^3 - (3 / 2 : ℝ) * t * (logHessianForm P e) u u + P.form ![(u : E),(u : E),(u : E)] := by
  have h0 : P.form ![e,e,e] = 1 := by
    rw [← diagonalCubic_eq_three P e, he]
  have hu : fderiv ℝ (diagonalCubic P.form) e (u : E) = 0 := u.property
  have h1 := hu
  rw [fderiv_diagonalCubic_apply_symmetric] at h1
  have h4 := logHessianForm_apply P
    (show 0 < diagonalCubic P.form e by rw [he]; norm_num) (u : E) (u : E)
  rw [he, hu, cubicHessian_apply] at h4
  norm_num at h4
  rw [diagonalCubic_eq_three, ← fullyCurried_apply]
  simp only [clm_eval, fullyCurried_apply]
  simp only [P.swap12, P.swap23] at *
  simp only [h0]
  linear_combination t^2 * h1 + (3 / 2 : ℝ) * t * h4

/-- Literal three-slot negation, required to handle BOTH recovery signs. -/
theorem cubic_three_neg (u : E) : P.form ![-u,-u,-u] = -P.form ![u,u,u] := by
  rw [← fullyCurried_apply]
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg, fullyCurried_apply]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (Q : SymmetricTrilinearForm H) (f : H) (hf : diagonalCubic Q.form f = 1)

/-- A genuine norm/unit morphism is CONSTRUCTED. The stored certificates are
proved outputs, not additional hypotheses about an unknown ambient map. -/
def basedNormIsoOfTangent (D : tangentSpace P e ≃ₗ[ℝ] tangentSpace Q f) [FiniteDimensional ℝ E]
    (hmetric : ∀ u v : tangentSpace P e,
      logHessianForm Q f (D u) (D v) = logHessianForm P e u v)
    (hcubic : ∀ u : tangentSpace P e,
      Q.form ![(D u : H),(D u : H),(D u : H)] = P.form ![(u : E),(u : E),(u : E)]) : BasedNormIso P e Q f where
  equiv := ((normalSplit P e he).toLinearEquiv.trans
    (((LinearEquiv.refl ℝ ℝ).prodCongr D).trans
      (normalSplit Q f hf).toLinearEquiv.symm)).toContinuousLinearEquiv
  map_unit := by
    change (fderiv ℝ (diagonalCubic P.form) e e / 3) • f +
      (D (tangentProjection P e he e) : H) = f
    simp only [ fderiv_diagonalCubic_at_one P.form e he,
      tangentProjection_basepoint, map_zero, ZeroMemClass.coe_zero,
      div_self (by norm_num : (3 : ℝ) ≠ 0), one_smul, add_zero]
  map_norm x := by
    obtain ⟨⟨t,u⟩, rfl⟩ := (normalSplit P e he).symm.surjective x
    change diagonalCubic Q.form
      ((normalSplit Q f hf).symm
        (((LinearEquiv.refl ℝ ℝ).prodCongr D)
          ((normalSplit P e he) ((normalSplit P e he).symm (t,u))))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change diagonalCubic Q.form ((t / 3) • f + (D u : H)) =
      diagonalCubic P.form ((t / 3) • e + (u : E))
    rw [cubic_unit_tangent_expansion Q f hf, cubic_unit_tangent_expansion P e he,
      hmetric, hcubic]

end
end AlbertGeometry.UnitTangentNormReconstruction
