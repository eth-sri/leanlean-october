module

public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.HighSpatialScoreTransfer
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine original normalized-design factorial transfer for the complete
source generator. All probability, Borel, and integrability conclusions
are derived from primitive raw-state guards and Q^r spatial envelopes. -/
𝚫
𝚳
𝚨
𝚩
𝚭

𝗇 𝔄 Measure.pi fun _ => 𝖪
𝗇 𝔅 highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c
𝗇 𝔇 highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c
𝗇 𝔈 n * highFixedScoreDenominator pMinus cMass
𝗇 𝔉 𝘋
𝗇 𝔊 Measure.pi fun _ => highNormalizedDesignLaw p
𝗇 𝔍 𝗄
𝗇 𝔎 ∫ u, H r u ∂𝔄
𝗇 𝔏 𝔈 ^ r / r.factorial
𝗃 𝔐 ἀ p hpMeas pMinus pPlus hpMinus $ Filter.Eventually.of_forall hraw
theorem high_marked_original_design_spatial_series
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] [NeZero k]
    (hk : 𝗑) (j : 𝙯) (n : ℕ)
    (π : Measure E) [SFinite π] activation (hAct : Measurable activation)
    a V η (ha : 𝙞) pMinus pPlus cMass
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    p (hpMeas : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    pReset (hpReset : Measurable $ Function.uncurry pReset )
    cReset (hcReset : 𝘝₁)
    g w (hg : Measurable g) (hw : Measurable w)
    φ (hφ : 𝘜₁) (c : 𝙛)
    (hq : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hwo : ∀ x, x ∉ 𝔉 → w x = 0)
    (hro : ∀ e x, x ∉ 𝔉 → pReset e x = p x)
    (H : 𝗖)
    (hH : ∀ r, Integrable (H r) 𝔄)
    (hH0 : ∀ r u, 0 ≤ H r u)
    (hdom : ∀ r x, (∀ i, x i ∈ 𝔉) →
      selectedRawSquareEnergy 𝔅 x ≤
        H r (highPatchProductChart d k j x)) :
    Integrable 𝔇
      𝔊 ∧
     ∫ x, 𝔇 x
      ∂𝔊 ≤
      ∑ r ∈ Finset.range 𝗉,
        (𝔈 * 𝔍) ^ r /
          r.factorial * 𝔎 := by
  let _ := cubeVolume_isProbability d
  have hprob := 𝔐 high_normalized_design_probability
  have hm :=
    (𝔐 highRawDensityMass_mem_Icc).1
  have hR r y :=
    highMarkedSampleNumerator_measurable r π activation hAct a V η p hpMeas pReset hpReset
      cReset hcReset g w hg hw φ hφ c y
  have hRaw r := high_raw_square_patch_integrable_bound hk j
    𝔅
    (hR r) (H r) (hH r) (hH0 r) $ hdom r
  have hs := high_marked_design_raw_factorial_series (cubeVolume d) n
    𝔉 (highTorusPatch_measurableSet d k j)
    (highRawDensityMass p) pMinus cMass hpMinus hcMass hm π activation a V η ha p hpMeas
    pReset cReset g w φ c
    (𝗉₂ c)
    hprob (fun x => (hraw x).1) hq hwo hro hR fun r => (hRaw r).1
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_le_sum
  intro r hr
  have hco : 0 ≤ 𝔏 := by
    apply div_nonneg
    · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg n)
        (high_fixed_score_denominator_pos hpMinus hcMass).le) r
    simp
  calc
    _ ≤ 𝔏 *
        (𝔍 ^ r * 𝔎) :=
      mul_le_mul_of_nonneg_left (hRaw r).2 hco
    𝘿 := 𝖢₃
