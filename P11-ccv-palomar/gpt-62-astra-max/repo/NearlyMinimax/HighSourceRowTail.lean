module

public import NearlyMinimax.HighResponseTensorTail
public import NearlyMinimax.CompleteSourceMassAnnihilation


@[expose] public section

/-! All-count response bounds on every actual row of the complete source
family. The density factors may depend on the full spatial carrier and
density atom, and are independent only of the response atom. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

/-- All rows of the actual complete source satisfy the same Taylor cap,
with their own true variation masses. In particular this holds for sample
counts exceeding the exterior selector degree. -/
theorem sourceRow_reference_all_count_bound {n : ℕ}
    {d : ℕ} [NeZero d] {k D M q : ℕ} (hn : 1 ≤ n)
    {ad bd C lam ℓ N μ a V η ρ pPlus : ℝ}
    (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (hpPlus : 0 ≤ pPlus)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass i)
    {i : SourceRowIndex d D M q ad bd C lam ℓ N μ}
    {reset : SourceRowDensityMark d D M q ad bd C lam ℓ N μ i → Fin n → ℝ}
    (hmReset : ∀ u, Measurable (fun e => reset e u))
    (hReset : ∀ e u, |reset e u| ≤ pPlus)
    {g w : Fin n → ℝ} {φ : Fin n → HighFrameVector d D}
    {c : HighFrameVector d D} (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameVector d D, (∑ γ, |v γ|) ≤ C⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : TernaryVector n) :
    let data := sourceRowData d k D M q ad bd C lam ℓ N μ
    |highMarkedResponseAction ((data).rowLaw i)
      ((data).rowActivation i) a V η
      (fun e => reset (sourceRowDensityProj d D M q ad bd C lam ℓ N μ i e))
      (fun e => coefficientReset c
        ((data).rowVector i e)
        ((data).rowTime i e)) g w φ y| ≤
      (pPlus^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        (data).rowMass i := by
  cases i with
  | inl p =>
    cases p
    · exact responseTensor_reference_all_count_bound hn hC ha hη hρ hηρ hpPlus
        (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inl .unit)) hmReset hReset hc hg hw hφ hp y
    · exact responseTensor_reference_all_count_bound hn hC ha hη hρ hηρ hpPlus
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _)
        (hpos (.inl .coarse)) hmReset hReset hc hg hw hφ hp y
    · exact responseTensor_reference_all_count_bound hn hC ha hη hρ hηρ hpPlus
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d ℓ N _)
        (hpos (.inl .fine)) hmReset hReset hc hg hw hφ hp y
  | inr i =>
    cases i with
    | inl _ =>
      exact responseTensor_reference_all_count_bound hn hC ha hη hρ hηρ hpPlus
        (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inr (.inl ()))) hmReset hReset hc hg hw hφ hp y
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := higherBandFamilyGuardDegree M i.val
      let T := higherBandFamilyUpper d ℓ N μ i.val
      letI := higherBandCarrierMeasure_finite d r ℓ i.property.1 i.val.2
      exact responseTensor_reference_all_count_bound hn hC ha hη hρ hηρ hpPlus
        (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
        (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ i.property.1 i.val.2)
        (hpos (.inr (.inr i))) hmReset hReset hc hg hw hφ hp y

end NearlyMinimax
