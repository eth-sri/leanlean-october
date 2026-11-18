module

public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
public import OAI.NumberTheory.DirichletL.Moments.PlainEnergy

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

theorem plain_column_integral {α : Type*} (S : Finset α) (a : α → O)
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
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul,← height_column_integral V hVc hVs τ _ (ha i).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem plain_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}))
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end SevenEighths.CenteredMomentPlainWindowEnergy

end

end OAI
