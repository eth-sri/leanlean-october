module

public import NearlyMinimax.HighMassTilt
public import NearlyMinimax.HighSelectedScoreEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Exact raw-likelihood Fisher transfer. Integrability under the genuine
normalized experiment yields integrability of D²/L under the fixed raw
reference, and a uniform conditional budget survives mass-power tilting. -/
𝚴
𝚳
𝚨
𝚩
𝚭

𝗇 𝔄 (D z / L z) ^ 2
𝗇 𝔜 L z / c
𝗇 𝔅 fun z => ENNReal.ofReal 𝔜
𝗇 𝔐 D z ^ 2 / L z
𝗇 𝔒 Filter.Eventually.of_forall 𝘕
𝗇 𝔓 (ENNReal.ofReal 𝔜).toReal
𝗇 𝔖 ∫ z, 𝔄 ∂μ.withDensity 𝔅
𝗃 𝔚 fun z => ἀ
theorem normalized_likelihood_score_square_transfer [MeasurableSpace Z]
    (μ : Measure Z) c (hc : 𝘝) (L D : Z → ℝ)
    (hL : Measurable L) (hpos : ∀ z, 0 < L z) :
    (Integrable 𝔚 𝔄
      (μ.withDensity 𝔅) ↔
        Integrable 𝔚 𝔐 μ) ∧
    𝔖 =
      c⁻¹ * ∫ z, 𝔐 ∂μ := by
  have hf : Measurable 𝔅 :=
    ENNReal.measurable_ofReal.comp $ hL.div_const c
  have he z : 𝔓 * 𝔄 =
      c⁻¹ * 𝔐 := by
    rw [ENNReal.toReal_ofReal $ div_nonneg (hpos z).le hc.le ]
    field_simp
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hf
      𝔒]
    simp only [smul_eq_mul, he]
    exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr $ inv_ne_zero hc.ne' ) _
  · have hi := integral_withDensity_eq_integral_toReal_smul (μ := μ) hf
      𝔒 𝔚 𝔄
    change 𝔖 =
      ∫ z, 𝔓 * 𝔄 ∂μ at hi
    rw [hi]
    simp_rw [he]
    exact integral_const_mul ..

𝗇 𝔔 μ.withDensity fun z => ENNReal.ofReal $ L ω z / c ω
𝗇 𝔗 (D ω z / L ω z) ^ 2
𝗇 𝔇 ∫ z, 𝔗 ∂𝔔
𝗇 𝔈 W (ω, z)
𝗇 𝔊 normalized_likelihood_score_square_transfer μ (c ω) (hc ω) (L ω) (D ω) hL.of_uncurry_left $ hpos ω
𝗇 𝔏 D z.1 z.2 ^ 2 / L z.1 z.2
𝗇 𝔘 ∫ z, ‖𝔈‖ ∂μ
theorem raw_joint_fisher_integrable_bound
    [MeasurableSpace Ω] [MeasurableSpace Z]
    (ν : Measure Ω) [IsFiniteMeasure ν] (μ : Measure Z) [SFinite μ]
    (c : 𝘄) (hc : ∀ ω, 0 < c ω) (hci : Integrable c ν)
    L D (hL : Measurable $ Function.uncurry L )
    (hD : Measurable $ Function.uncurry D ) (hpos : ∀ ω z, 0 < L ω z)
    (B : ℝ) (hB : 𝙐)
    (hscore : ∀ ω, Integrable 𝔚 𝔗
      𝔔)
    (hbound : ∀ ω, 𝔇 ≤ B) :
    Integrable (fun z : Ω × Z => 𝔏) (ν.prod μ) ∧
     ∫ z : Ω × Z, 𝔏 ∂ν.prod μ ≤ (∫ ω, c ω ∂ν) * B := by
  let W : Ω × Z → ℝ := 𝔚 𝔏
  have hW : Measurable W := (hD.pow_const 2).div hL
  have hWi (ω : Ω) :=
    (𝔊).1.mp $ hscore ω
  have hWn (ω : Ω) (z : Z) : 0 ≤ 𝔈 := 𝚚₁ (hpos ω z).le
  have he (ω : Ω) : ∫ z, 𝔈 ∂μ = c ω *
      𝔇 := by
    have hs := (𝔊).2
    grind
  have hnorm (ω : Ω) : 𝔘 ≤ c ω * B := by
    have heNorm : (fun z => ‖𝔈‖) = 𝔚 𝔈 := by
      funext z
      simp_all
    simp_all
  have hnormI : Integrable (fun ω => 𝔘) ν := by
    apply (hci.mul_const B).mono' hW.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, 𝗪]
    exact hnorm ω
  have hWI :=
    (integrable_prod_iff hW.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hWi, hnormI⟩
  refine ⟨hWI, ?_⟩
  rw [integral_prod _ hWI]
  calc
    _ ≤ ∫ ω, c ω * B ∂ν := by
      apply integral_mono_ae hWI.integral_prod_left $ hci.mul_const B
      apply Filter.Eventually.of_forall
      simp_all
    𝘿 := integral_mul_const ..

𝗃 𝔞 ἀ n a V (p ω) $ F ω
𝗇 𝔙 𝔞 highRawSampleLikelihood
𝗇 𝔉 𝔙 z
𝗃 𝔟 ἀ n a V p F hp hF
𝗇 𝔍 𝔟 highSampleIndexKernel ω
𝗇 𝔎 D z.1 z.2 ^ 2 / 𝘂₁
𝗇 𝔑 𝘱
𝗇 𝔛 (D ω z / 𝔉) ^ 2
theorem high_raw_joint_fisher_integrable_bound [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (a V : ℝ)
    (p F : Ω → 𝙀)
    hp hF
    aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝙄)
    (hq : ∀ ω x y, 0 < 𝙅 V y)
    D
    (hD : Measurable $ Function.uncurry D ) B (hB : 𝙐)
    (hscore : ∀ ω, Integrable (fun z => 𝔛)
      𝔍)
    (hbound : ∀ ω, ∫ z, 𝔛
      ∂𝔍 ≤ B) :
    Integrable 𝔚 𝔎
      (ν.prod 𝔑) ∧
     ∫ z, 𝔎
      ∂ν.prod 𝔑 ≤
      massPowerNormalizer ν 𝙙 n * B := by
  let c := fun ω => highRawDensityMass (p ω) ^ n
  have hmBound ω :=
    𝖤₁
  have hm ω := haRaw.trans_le (hmBound ω).1
  have hc := fun ω => pow_pos (hm ω) n
  have hcm := (𝙨).pow_const n
  have hci : Integrable c ν := by
    apply (integrable_const $ bRaw ^ n ).mono' hcm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hc ω).le]
    exact pow_le_pow_left₀ (hm ω).le (hmBound ω).2 n
  have he ω : 𝔍 =
      (𝔑).withDensity fun z =>
        ENNReal.ofReal $ 𝔉 / c ω := by
    rw [highSampleIndexKernel_apply]
    congr 1
    funext z
    congr 1
    apply (eq_div_iff (hc ω).ne').mpr
    simpa only [c, mul_comm] using
      𝔞 highSampleLikelihood_mass_cancellation (hm ω).ne' z
  exact raw_joint_fisher_integrable_bound ν 𝔑 c hc hci
    (fun ω => 𝔙) D
    𝔟 highRawSampleLikelihood_joint_measurable hD
    (fun ω z => Finset.prod_pos fun i _ => mul_pos
      (haRaw.trans_le (hraw ω $ z.1 i ).1) $ hq ω .. ) B hB
     fun ω => by simp_all
     fun ω => 𝖤₄
