module

public import NearlyMinimax.PathRisk
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Score-to-risk comparison with the manuscript's absolutely continuous
observable means and almost-everywhere score identity. -/
𝚫
𝚨
𝚩

𝗇 𝔐 ∫ t in (0)..δ, score t
𝗇 𝔘 Icc 0 δ
𝗇 𝔑 t ∈ 𝔘
𝗇 𝔗 𝚈
theorem absolutelyContinuous_path_mean_change_le {m score } {δ r : ℝ}
    (hδ : 𝔗) (hAC : AbsolutelyContinuousOnInterval m 0 δ)
    (hscore : IntervalIntegrable score volume 0 δ)
    (hbound : ∀ᵐ t ∂volume, 𝔑 → |deriv m t| ≤ r * score t) :
    |m δ - m 0| ≤ r * 𝔐 := by
  rw [← hAC.integral_deriv_eq_sub, ← intervalIntegral.integral_const_mul]
  apply show ‖∫ t in 0..δ, deriv m t‖ ≤ _ from
    intervalIntegral.norm_integral_le_of_norm_le hδ ?_ $ hscore.const_mul r
  filter_upwards [hbound] with t ht hmem
  exact ht ⟨hmem.1.le, hmem.2⟩

theorem absolutelyContinuous_path_separation_le {m score } {δ r V₀ Vδ : ℝ}
    (hδ : 𝔗) (hAC : AbsolutelyContinuousOnInterval m 0 δ)
    (hscore : IntervalIntegrable score volume 0 δ)
    (hbound : ∀ᵐ t ∂volume, 𝔑 → |deriv m t| ≤ r * score t)
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + 𝔐) * r := by
  have hchange := absolutelyContinuous_path_mean_change_le hδ hAC hscore hbound
  grind

𝗇 𝔙 R t x
𝗇 𝔄 Real.sqrt $ ∫ x, 𝔙 ^ 2 ∂P t
𝗇 𝔅 ∀ᵐ t ∂volume, 𝔑 → HasDerivAt (fun u => ∫ x, T x ∂P u) (∫ x, T x * 𝔙 ∂P t) t
𝗇 𝔇 ∀ t ∈ 𝔘, ∫ x, (T x - V t) ^ 2 ∂P t ≤ 𝘴₁
𝗇 𝔈 ∀ᵐ t ∂volume, 𝔑 → ∫ x, 𝔙 ∂P t = 0
𝗇 𝔉 ∀ᵐ t ∂volume, 𝔑 → MemLp (R t) 2 (P t)
𝗇 𝔊 AbsolutelyContinuousOnInterval (fun t => ∫ x, T x ∂P t) 0 δ
𝗇 𝔍 ∀ t ∈ 𝔘, MemLp T 2 $ P t
𝗇 𝔎 V δ - V 0
𝗇 𝔏 ∀ t ∈ 𝔘, IsProbabilityMeasure $ P t
𝗇 𝔒 2 + ∫ t in (0)..δ, 𝔄
𝗇 𝔓 IntervalIntegrable (fun t => 𝔄) volume 0 δ
𝗇 𝔔 ⟨le_rfl, hδ⟩
𝗇 𝔖 ⟨hδ, le_rfl⟩
/-- The score and derivative are only required almost everywhere in time. -/
theorem probability_absolutelyContinuous_score_path_separation_le
    {Ω } [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) T (R : ℝ → 𝘄) (V : 𝘓)
    δ r (hδ : 𝔗) (hr : 𝘵₁)
    (hprob : 𝔏)
    (hT : 𝔍)
    (hR : 𝔉)
    (hcenter : 𝔈)
    (hAC : 𝔊)
    (hderiv : 𝔅)
    (hrisk : 𝔇)
    (hscoreInt : 𝔓) :
    |𝔎| ≤
      𝔒 * r := by
  apply absolutelyContinuous_path_separation_le hδ hAC hscoreInt
  · filter_upwards [hR, hcenter, hderiv] with t hRt hct hdt ht
    let _ := hprob t ht
    rw [(hdt ht).deriv]
    exact probability_score_bound (P t) T (R t) (V t) r
      (hT t ht) (hRt ht) hr (hct ht) $ hrisk t ht
  · let _ := hprob 0 𝔔
    exact probability_mean_error_le (P 0) T (V 0) r
      (hT 0 𝔔) hr $ hrisk 0 𝔔
  · let _ := hprob δ 𝔖
    exact probability_mean_error_le (P δ) T (V δ) r
      (hT δ 𝔖) hr $ hrisk δ 𝔖

theorem probability_absolutelyContinuous_score_path_risk_lower_bound
    [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) T (R : ℝ → 𝘄) (V : 𝘓)
    δ r risk D ε (hδ : 𝔗) (hr : 𝘵₁)
    (hprob : 𝔏)
    (hT : 𝔍)
    (hR : 𝔉)
    (hcenter : 𝔈)
    (hAC : 𝔊)
    (hderiv : 𝔅)
    (hrisk : 𝔇)
    (hscoreInt : 𝔓)
    (hriskEq : 𝘴₁ = risk + 𝘔 * ε) :
    𝔎 ^ 2 /
      𝔒 ^ 2
      - 𝘔 * ε ≤ risk := by
  have hsep := probability_absolutelyContinuous_score_path_separation_le P T R V δ r hδ hr
    hprob hT hR hcenter hAC hderiv hrisk hscoreInt
  simpa only [sq_abs] using
    path_risk_lower_bound (intervalIntegral.integral_nonneg_of_forall hδ fun t => Real.sqrt_nonneg _ ) hr (abs_nonneg 𝔎) hsep hriskEq
