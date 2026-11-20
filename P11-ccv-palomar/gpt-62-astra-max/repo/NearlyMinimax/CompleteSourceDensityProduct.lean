module

public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighUnionScorePrimitives


@[expose] public section

/-! Actual response-coordinate elimination makes every appended density
product annihilate under the full source activation, at every sample count. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

/-- Complete actual singleton, pair, and higher coarse/fine rows have
conditional density-product zero mass at every count. -/
theorem completeSourceDensity_product_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    {C : ModelConstants d} (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    {Cfr lam ℓ N μ : ℝ} (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ) {n : ℕ} (x : DesignSample d n) :
    (∫ e, highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C) e *
      ∏ i, highUnionSourceResetDensity C (completeSourceRows C k D M q Cfr lam ℓ N μ)
        j h e (x i) ∂highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)) = 0 := by
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards k hD hq hM lam μ hCfr hℓ hℓN
  apply completeSource_density_action_zero hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN j h
    (fun p => ∏ i, p (x i)) (C.densityUpper^n)
  · exact Finset.measurable_fun_prod _ fun i _ =>
      (highUnionSourceResetDensity_measurable C R G j h).comp (measurable_id.prodMk measurable_const)
  · intro e
    exact finite_density_product_abs_bound _ (by linarith [C.one_lt_densityUpper])
      (fun i => highUnionSourceResetDensity_abs_le C R G j h e (x i))

end NearlyMinimax
