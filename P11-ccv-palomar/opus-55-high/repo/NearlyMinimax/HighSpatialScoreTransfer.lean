module

public import NearlyMinimax.HighPatchProductMeasure
public import NearlyMinimax.HighSelectedScoreEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Actual local spatial envelopes transfer through the periodic chart
and the true normalized design likelihood, with source fixed C_sharp.
Both integrability statements are derived from the genuine Q^r envelope. -/
𝚫
𝚳
𝚨
𝚩
𝚱

𝗃 𝔍 ἀ d k j
𝗇 𝔊 (cubeVolume d).restrict 𝔍 highTorusPatch
𝗇 𝔄 Measure.pi fun _ => 𝔊
𝗇 𝔅 Measure.pi fun _ => 𝖪
𝗇 𝔇 ∀ i, x i ∈ 𝔍 highTorusPatch
𝗇 𝔈 Fin r → Covariate d
𝗇 𝔉 𝔍 highPatchProductChart x
theorem high_raw_square_patch_integrable_bound [NeZero k]
    (hk : 𝗑) (j : 𝙯)
    (R : 𝔈 → (Fin r → Fin 3) → ℝ)
    (hR : ∀ y, Measurable fun x => R x y )
    (H : 𝔈 → ℝ)
    (hH : Integrable H 𝔅)
    (hH0 : ∀ u, 0 ≤ H u)
    (hdom : ∀ x, 𝔇 →
      selectedRawSquareEnergy R x ≤ H 𝔉) :
    Integrable (selectedRawSquareEnergy R)
      𝔄 ∧
     ∫ x, selectedRawSquareEnergy R x
      ∂𝔄 ≤
      𝗄 ^ r *
        ∫ u, H u ∂𝔅 := by
  let _ := cubeVolume_isProbability d
  have hrawMeas : Measurable $ selectedRawSquareEnergy R :=
    Finset.measurable_sum _ fun y _ => (hR y).pow_const 2
  have hraw0 x : 0 ≤ selectedRawSquareEnergy R x :=
    Finset.sum_nonneg fun y _ => sq_nonneg _
  have heval := highPatchProductChart_integrable hk j H hH
  have hmem : ∀ᵐ x ∂Measure.pi fun _ : Fin r => 𝔊 ,
      𝔇 :=
    ae_all_iff.mpr fun i => Measure.tendsto_eval_ae_ae.eventually
      $ ae_restrict_mem 𝔍 highTorusPatch_measurableSet
  have hrawI : Integrable (selectedRawSquareEnergy R)
      𝔄 := by
    apply heval.mono' hrawMeas.aestronglyMeasurable
    filter_upwards [hmem] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg $ hraw0 x ]
    simp_all
  refine ⟨hrawI, ?_⟩
  calc
    _ ≤ ∫ x, H 𝔉
        ∂𝔄 :=
      integral_mono_ae hrawI heval $ hmem.mono fun x hx => hdom x hx
    𝖦 := by
      simpa only [Fintype.card_fin] using highPatchProductChart_integral_le hk j H hH hH0
