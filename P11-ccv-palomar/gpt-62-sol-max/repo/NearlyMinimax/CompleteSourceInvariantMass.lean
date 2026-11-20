module

public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighUnionInvariantMass


@[expose] public section

/-! The complete singleton, pair, and higher coarse/fine packet source
has a genuine time-independent raw mass law. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
include hD hq hM hCfr hℓ hℓN


section
variable (T : ℝ)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3^d) ≤ 1 / (2+8*((3^d : ℕ):ℝ)^2))
    (t : ℝ) (ht : t ∈ Icc 0 T)
include hsmall ht

/-- Actual canonical append cancellation closes mass-law invariance for
all retained rows, including every higher coarse/fine target. -/
theorem completeSourceMass_prior_law :
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedPrior (highNeighbors d k) (3^d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) =
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedReference (highNeighbors d k) (3^d)
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) := by
  obtain ⟨G, hpos⟩ := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  exact highUnionSourceMass_prior_law_of_append_annihilation C _ G hpos T hsmall
    (completeSourceMass_append_indicator_zero C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) t ht

end

end NearlyMinimax
