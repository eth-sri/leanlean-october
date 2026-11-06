module

public import NearlyMinimax.Risk
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Score-to-risk comparison on arbitrary measurable observation spaces.
The density path and its observable derivative are input data; no risk lower
bound is assumed. This proves the comparison for pointwise differentiable
means. The manuscript's weaker absolutely-continuous, almost-everywhere
formulation remains a separate obligation.
-/

𝚫
𝚮
𝚨

/-- Exceptional latent states cost at most the squared clipping diameter
times their probability, on an arbitrary probability space. -/
theorem probability_mixture_exceptional_risk_bound [MeasurableSpace Α]
    (μ : Measure Α) [IsProbabilityMeasure μ] e
    bad (hbadmeas : MeasurableSet bad) risk D ε
    (he : Integrable e μ) (hrisk : 0 ≤ risk)
    (hgood : ∀ᵐ x ∂μ, x ∉ bad → e x ≤ risk)
    (hbad : ∀ᵐ x ∂μ, x ∈ bad → e x ≤ 𝘔)
    (hmass : μ.real bad ≤ ε) :
     ∫ x, e x ∂μ ≤ risk + 𝘔 * ε := by
  have hI : Integrable (bad.indicator fun _ => 𝘔 ) μ :=
    (integrable_const _).indicator hbadmeas
  have hp : e ≤ᵐ[μ] fun x => risk + bad.indicator (fun _ => 𝘔) x := by
    filter_upwards [hgood, hbad] with x hxgood hxbad
    by_cases hx : x ∈ bad
    · rw [indicator_of_mem hx]
      grind
    simp_all
  calc
     ∫ x, e x ∂μ ≤ ∫ x, risk + bad.indicator (fun _ => 𝘔) x ∂μ :=
      integral_mono_ae he ((integrable_const _).add hI) hp
    _ = risk + 𝘔 * μ.real bad := by
      rw [𝖻₁ hI, integral_indicator hbadmeas,
        integral_const, integral_const]
      simp [mul_comm]
    _ ≤ risk + 𝘔 * ε := 𝖩₃
