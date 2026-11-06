module

public import NearlyMinimax.HighRawObservableDerivative
public import NearlyMinimax.HighObservableRegularity
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Closed-interval absolute continuity for the actual high-prior data observable. -/
𝚹
𝚨
𝛂

𝗇 𝔄 v - 𝙎 * u
𝗇 𝔅 B * (𝙎 * (𝚗 * (n / 𝗅)))
𝗇 𝔐 𝘱
𝗇 𝔇 (𝔐).real Set.univ
𝗇 𝔈 𝗺
𝗇 𝔉 H 𝗟₁
𝗇 𝔊 hq u hu ω
𝗃 𝔔 ἀ n a 𝔄
𝗃 𝔑 𝔔 ἀ (p ω) $ F ω
𝗇 𝔍 𝔑 highRawObservable H
𝗇 𝔎 ∀ u ∈ 𝔈, ∀ ω x y, 0 ≤ 𝙅 𝔄 y
𝗇 𝔏 𝔑 highRawSampleLikelihood z
𝗇 𝔒 B * 𝚗
𝗇 𝔓 c * dist u v
𝗃 𝔖 ∫ z, L ἀ z ∂𝔐
𝗃 𝔗 Measurable $ Function.uncurry ἀ
theorem highRawObservable_lipschitzOn (n : ℕ) a v η T P B
    (ha : 𝙆) (hP : 𝚏) (hB : 𝙐)
    (p F : Ω → 𝙀) (hp : 𝔗 p)
    (hF : 𝔗 F) (hpb : ∀ ω x, |𝗃₁| ≤ P)
    (hq : 𝔎)
    H (hH : Measurable H)
    (hHb : ∀ z, |H z| ≤ B) ω :
    LipschitzOnWith
      ⟨𝔅 * 𝔇, 𝖠₃⟩
      (fun u => 𝔍) 𝔈 := by
  let c := 𝔅
  have hc : 𝗂₁ := 𝖠₃
  let L := fun u z =>
    𝔉 * 𝔏
  have hLM u : Measurable $ L u := by
    have hj : Measurable $ Function.uncurry fun ω z =>
        𝔏 :=
      𝔔 highRawSampleLikelihood_joint_measurable p F hp hF
    exact (hH.comp $ encodeDesignResponse_measurable a ).mul hj.of_uncurry_left
  have hi u (hu : u ∈ 𝔈) : Integrable (L u) 𝔐 := by
    apply Integrable.of_bound (hLM u).aestronglyMeasurable 𝔒
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact 𝘣 (𝔔 highRawSampleLikelihood_abs_le P hP
        (p ω) (F ω) (hpb ω) ha.ne' 𝔊 z) (abs_nonneg _) hB
  have hl z :
      LipschitzOnWith ⟨c, hc⟩ (fun u => L u z) 𝔈 := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
       fun u _ => (𝗡₂
        𝔉).hasDerivWithinAt
    intro u hu
    change ‖𝔉 * (-𝙎 *
      𝔑 highRawSampleVarianceDerivative z)‖ ≤ c
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, 𝚓₁]
    exact 𝘣 (mul_le_mul_of_nonneg_left
      (𝔔 highRawSampleVarianceDerivative_abs_le P ha hP
        (p ω) (F ω) (hpb ω) 𝔊 z) $ sq_nonneg η )  𝖠₃  hB
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  change dist 𝔖 u 𝔖 v ≤
    c * 𝔇 * dist u v
  rw [dist_eq_norm, ← 𝚘₁]
  have hb : ∀ᵐ z ∂𝔐, ‖L u z - L v z‖ ≤ 𝔓 :=
    Eventually.of_forall fun z => by
      have he := (hl z).dist_le_mul u hu v hv
      assumption
  calc
    _ ≤ 𝔓 * 𝔇 := norm_integral_le_of_norm_le_const hb
    𝘿 := 𝖢₃

𝚲

theorem historyMarkedPrior_rawObservable_exists_lipschitz (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝘼)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝘽)
    (T Ba : ℝ) (hBa : 𝙑) [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝖤)
    (n : ℕ) (a v η P B : ℝ) (ha : 𝙆) (hP : 𝚏) (hB : 𝙐)
    (p F : 𝙗 → 𝙀)
    (hp : 𝔗 p) (hF : 𝔗 F)
    (hpb : ∀ ω x, |𝗃₁| ≤ P)
    (hq : 𝔎)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    ∃ K , LipschitzOnWith K
      (fun u => ∫ ω, 𝔍
        ∂𝘳 u π activation) 𝔈 := by
  let G := fun u ω => 𝔍
  have hGM u := 𝔔 highRawObservable_measurable p F hp hF H hH
  let M := 𝔒 * 𝔇
  have hM : 𝙷 := 𝖠₃
  have hGb u hu ω :=
    𝔔 highRawObservable_abs_le P B hP hB (p ω) (F ω) (hpb ω) ha.ne' 𝔊 H hHb
  let K : NNReal := ⟨𝔅 * 𝔇, 𝖠₃⟩
  have hGlip ω :=
    highRawObservable_lipschitzOn n a v η T P B ha hP hB p F hp hF hpb hq H hH hHb ω
  exact ⟨_, historyMarkedPrior_variable_observable_lipschitz dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation habound hsmall G hGM M hM hGb K hGlip⟩
