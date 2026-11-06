module
public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
public import OAI.NumberTheory.DirichletL.Moments.PlainEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentPlainWindowEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm CenteredMomentPlainEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

section
variable {α : Type*} (S : Finset α) (a : α → O)
include α S a
theorem plain_column_integral
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    rowPolynomial S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i})) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold rowPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}) := by
      pm_2910
    _ = _ := by
      pm_2909

theorem plain_column_integrable
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}))
  pm_6954
  pm_3526 rowPolynomial Finset.mul_sum Finset.sum_congr i hi
  ring
end

end SevenEighths.CenteredMomentPlainWindowEnergy

end

end OAI
