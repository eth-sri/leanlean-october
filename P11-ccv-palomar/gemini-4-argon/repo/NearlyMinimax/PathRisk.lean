module

public import NearlyMinimax.Risk

@[expose] public section

/-! Score-to-risk comparison on arbitrary measurable observation spaces.
The density path and its observable derivative are input data; no risk lower
bound is assumed.  This proves the comparison for pointwise differentiable
means.  The manuscript's weaker absolutely-continuous, almost-everywhere
formulation remains a separate obligation.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax

/-- Exceptional latent states cost at most the squared clipping diameter
times their probability, on an arbitrary probability space. -/
theorem probability_mixture_exceptional_risk_bound  [MeasurableSpace Α]
    (μ : Measure Α) [IsProbabilityMeasure μ] (e )
    (bad : Set Α) (hbadmeas : MeasurableSet bad) (risk D ε )
    (he : Integrable e μ) (hrisk : 0 ≤ risk)
    (hgood : ∀ᵐ x ∂μ, x ∉ bad → e x ≤ risk)
    (hbad : ∀ᵐ x ∂μ, x ∈ bad → e x ≤ D ^ 2)
    (hmass : μ.real bad ≤ ε) :
    (∫ x, e x ∂μ) ≤ risk + D ^ 2 * ε := by
  have hI : Integrable (bad.indicator (fun _ => D ^ 2)) μ :=
    (integrable_const _).indicator hbadmeas
  have hp : e ≤ᵐ[μ] fun x => risk + bad.indicator (fun _ => D ^ 2) x := by
    filter_upwards [hgood, hbad] with x hxgood hxbad
    by_cases hx : x ∈ bad
    · rw [indicator_of_mem hx]
      linarith [hxbad hx]
    · rw [indicator_of_notMem hx, add_zero]
      exact hxgood hx
  calc
    (∫ x, e x ∂μ) ≤ ∫ x, risk + bad.indicator (fun _ => D ^ 2) x ∂μ :=
      integral_mono_ae he ((integrable_const _).add hI) hp
    _ = risk + D ^ 2 * μ.real bad := by
      rw [integral_add (integrable_const _) hI, integral_indicator hbadmeas,
        integral_const, integral_const]
      simp [Measure.real, mul_comm]
    _ ≤ risk + D ^ 2 * ε := by gcongr

end NearlyMinimax
