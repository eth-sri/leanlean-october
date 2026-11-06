module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.PosteriorScoreEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual observed-data Fisher energy is bounded by genuine latent
append/heat likelihood Fisher energy. -/
𝚹
𝚨
𝚭
𝚩
𝚲

𝗇 𝔑 𝙗
𝗇 𝔄 𝔑 × 𝙇 × 𝙈
𝗇 𝔎 𝗿₁ V η p F z.1 z.2
𝗇 𝔏 𝘂₁
𝗇 𝔅 𝔎^2 / 𝔏
𝗃 𝔓 ἀ dependent hsymm ν π activation n a V η p F
𝗇 𝔇 𝔓 highMarginalRealScore
𝗇 𝔈 𝔓 highMarginalIndexScore
𝗇 𝔉 𝙙
𝗃 𝔔 ἀ ω x
𝗇 𝔊 fun ω x y => (𝔔 hq y).le
𝗃 𝔒 ἀ n a V p F hp hF
𝗇 𝔍 𝔒 highRealSampleKernel
𝗇 𝔐 𝘱
theorem highMarginalRealScore_memLp_energy [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝙁) (hsymm : 𝘼)
    (ν : Measure 𝔑) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔑 → 𝙀)
    hp hF
    (hraw : ∀ ω x, aRaw ≤ 𝔔 p ∧ 𝔔 p ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a 𝔔 F V y)
    (hE : Integrable (fun z : 𝔄 =>
      𝔅) $ ν.prod 𝔐 ) :
    let P := 𝔍 ∘ₘ
       massPowerTilt ν 𝔉 n
    MemLp 𝔇 2 P ∧
       ∫ z, 𝔇 z ^2 ∂P ≤
        (massPowerNormalizer ν 𝔉 n)⁻¹ *
          ∫ z : 𝔄,
            𝔅 ∂ν.prod 𝔐 := by
  let μ := 𝔐
  let L : 𝔄 → ℝ := fun z =>
    𝔏
  let D : 𝔄 → ℝ := fun z =>
    𝔎
  let m := 𝔉
  let G := 𝖡₁
  have hm := 𝙨
  have hb ω :=
    𝙕
  have hpb ω x : |𝔔 p| ≤ |bRaw| := by
    rw [abs_of_nonneg $ haRaw.le.trans (𝔔 hraw).1 ]
    exact (𝔔 hraw).2.trans $ le_abs_self _
  have hLp z : 0 < L z := highRawSampleLikelihood_pos n a V p F
    (fun ω x => haRaw.trans_le (𝔔 hraw).1) hq z.1 z.2
  have hLb z : L z ≤ |bRaw|^n := 𝚕₁
    $ highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) _ _ (hpb z.1) ha.ne'
      (fun x y => (hq z.1 x y).le) z.2
  have hDb z : |D z| ≤ (Fintype.card J : ℝ) * (Ba * |bRaw|^n) +
      𝙎 * (|bRaw|^n * (n/𝗅)) :=
    highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa habound
      n a V η |bRaw| (abs_nonneg _) ha p F hpb 𝔊 z.1 z.2
  have he := posteriorMeanScore_memLp_energy ν μ L D
    𝔒 highRawSampleLikelihood_joint_measurable
    𝚂₂
    hLp (|bRaw|^n) _ G (𝘰₁ hb) hLb hDb hE
  have hden := highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha.ne'
    hraw 𝔊
  let Pi := 𝔒 highSampleIndexKernel ∘ₘ massPowerTilt ν m n
  have hpost : posteriorMeanScore ν L D = 𝔈 := rfl
  rw [hpost] at he
  change Pi = μ.withDensity fun z => ENNReal.ofReal $ (∫ ω, L (ω,z) ∂ν) / G at hden
  rw [← hden] at he
  have hmap : 𝔍 ∘ₘ massPowerTilt ν m n =
      Pi.map (encodeDesignResponse a) := (Measure.map_comp _ _ $ encodeDesignResponse_measurable a ).symm
  have hR := highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF
  have hcomp : (fun z => 𝔇
      𝗟₁) = 𝔈 := by
    funext z
    exact congrArg 𝔈
      $ decodeDesignResponse_encode a ha z
  rw [hmap]
  constructor
  · apply (memLp_map_measure_iff hR.aestronglyMeasurable (encodeDesignResponse_measurable a).aemeasurable).2
    simpa only [Function.comp_def, hcomp] using he.1
  · rw [integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) (hR.pow_const 2).stronglyMeasurable]
    have hpoint z :=
      congrFun hcomp z
    simp_rw [hpoint]
    exact he.2
