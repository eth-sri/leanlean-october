module

public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.HighSpatialScoreTransfer


@[expose] public section

/-! Genuine original normalized-design factorial transfer for the complete
source generator. All probability, Borel, and integrability conclusions
are derived from primitive raw-state guards and Q^r spatial envelopes. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem high_marked_original_design_spatial_series {ι E : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) {j : HighWindowLabels d k} (n : ℕ)
    {π : Measure E} [SFinite π] {activation : E → ℝ} (hAct : Measurable activation)
    {a V η : ℝ} (ha : a ≠ 0) {pMinus pPlus cMass : ℝ}
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    {p : Covariate d → ℝ} (hpMeas : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    {pReset : E → Covariate d → ℝ} (hpReset : Measurable (Function.uncurry pReset))
    {cReset : E → ι → ℝ} (hcReset : ∀ γ, Measurable (fun e => cReset e γ))
    {g w : Covariate d → ℝ} (hg : Measurable g) (hw : Measurable w)
    {φ : Covariate d → ι → ℝ} (hφ : ∀ γ, Measurable (fun x => φ x γ)) {c : ι → ℝ}
    (hq : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hwo : ∀ x, x ∉ highTorusPatch j → w x = 0)
    (hro : ∀ e x, x ∉ highTorusPatch j → pReset e x = p x)
    {H : (r : ℕ) → (DesignSample d r) → ℝ}
    (hH : ∀ r, Integrable (H r) (Measure.pi (fun _ => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ r u, 0 ≤ H r u)
    (hdom : ∀ r x, (∀ i, x i ∈ highTorusPatch j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x ≤
        H r (highPatchProductChart j x)) :
    let energy := highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c
    Integrable (energy)
      (Measure.pi (fun _ => highNormalizedDesignLaw p)) ∧
    (∫ x, energy x
      ∂Measure.pi (fun _ => highNormalizedDesignLaw p)) ≤
      ∑ r ∈ Finset.range (n + 1),
        (n * highFixedScoreDenominator pMinus cMass * (2 / k) ^ d) ^ r /
          r.factorial * ∫ u, H r u
            ∂Measure.pi (fun _ => volume.restrict (spatialPatchBox d)) := by
  let _ := cubeVolume_isProbability d
  have hm  :=
    (highRawDensityMass_mem_Icc hpMeas hpMinus (Filter.Eventually.of_forall hraw)).1
  have hR r (y : TernaryVector r)  :=
    highMarkedSampleNumerator_measurable π hAct a V η hpMeas hpReset hcReset hg hw hφ c y
  have hRaw r := high_raw_square_patch_integrable_bound hk
    (hR r) (hH r) (hH0 r) (hdom r)
  have hs := high_marked_design_raw_factorial_series n (highTorusPatch_measurableSet ..) hpMinus hcMass hm ha hpMeas
    (highMarkedResponseMass_measurable a V η hg hw hφ c)
    (high_normalized_design_probability hpMeas hpMinus (Filter.Eventually.of_forall hraw)) (fun x => (hraw x).1) hq hwo hro hR (fun r => (hRaw r).1)
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_le_sum
  intro r hr
  have hco : 0 ≤ (n * highFixedScoreDenominator pMinus cMass) ^ r / r.factorial := by
    apply div_nonneg
    · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg n)
        ((by unfold highFixedScoreDenominator; positivity : 0 < highFixedScoreDenominator pMinus cMass)).le) r
    · positivity
  calc
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (hRaw r).2 hco
    _ = _ := by ring

end NearlyMinimax
