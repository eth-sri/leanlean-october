module

public import NearlyMinimax.PathRisk
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun


@[expose] public section

/-! Score-to-risk comparison with the manuscript's absolutely continuous
observable means and almost-everywhere score identity. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable {m score : ℝ → ℝ} {δ r V₀ Vδ : ℝ} (hδ : 0 ≤ δ) (hAC : AbsolutelyContinuousOnInterval m 0 δ)
    (hscore : IntervalIntegrable score volume 0 δ)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → |deriv m t| ≤ r * score t)
include hδ hAC hscore hbound

theorem absolutelyContinuous_path_mean_change_le :
    |m δ - m 0| ≤ r * ∫ t in 0..δ, score t := by
  rw [← hAC.integral_deriv_eq_sub, ← intervalIntegral.integral_const_mul]
  apply (show ‖∫ t in 0..δ, deriv m t‖ ≤ _ from
    intervalIntegral.norm_integral_le_of_norm_le hδ ?_ (hscore.const_mul r))
  filter_upwards [hbound] with t ht hmem
  exact ht ⟨hmem.1.le, hmem.2⟩

theorem absolutelyContinuous_path_separation_le
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + ∫ t in 0..δ, score t) * r := by
  have hchange := absolutelyContinuous_path_mean_change_le hδ hAC hscore hbound
  grind

end

variable {Ω : Type*} [MeasurableSpace Ω] {P : ℝ → Measure Ω} {T : Ω → ℝ} {R : ℝ → Ω → ℝ} {V : ℝ → ℝ}
    {δ r risk D ε : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hprob : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (P t))
    (hT : ∀ t ∈ Icc 0 δ, MemLp T 2 (P t)) (hR : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → MemLp (R t) 2 (P t))
    (hcenter : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → (∫ x, R t x ∂P t) = 0)
    (hAC : AbsolutelyContinuousOnInterval (fun t => ∫ x, T x ∂P t) 0 δ)
    (hderiv : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → HasDerivAt (fun u => ∫ x, T x ∂P u) (∫ x, T x * R t x ∂P t) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∫ x, (T x - V t) ^ 2 ∂P t) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) volume 0 δ)
include hδ hr hprob hT hR hcenter hAC hderiv hrisk hscoreInt

/-- The score and derivative are only required almost everywhere in time. -/
theorem probability_absolutelyContinuous_score_path_separation_le
    :
    |V δ - V 0| ≤
      (2 + ∫ t in 0..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) * r := by
  apply absolutelyContinuous_path_separation_le hδ hAC hscoreInt
  · filter_upwards [hR, hcenter, hderiv] with t hRt hct hdt ht
    let _ := hprob t ht
    rw [(hdt ht).deriv]
    exact probability_score_bound
      (hT t ht) (hRt ht) hr (hct ht) (hrisk t ht)
  · let _ := hprob 0 ⟨le_rfl, hδ⟩
    exact probability_mean_error_le
      (hT 0 ⟨le_rfl, hδ⟩) hr (hrisk 0 ⟨le_rfl, hδ⟩)
  · let _ := hprob δ ⟨hδ, le_rfl⟩
    exact probability_mean_error_le
      (hT δ ⟨hδ, le_rfl⟩) hr (hrisk δ ⟨hδ, le_rfl⟩)

theorem probability_absolutelyContinuous_score_path_risk_lower_bound

    (hriskEq : r ^ 2 = risk + D ^ 2 * ε) :
    (V δ - V 0) ^ 2 /
      (2 + ∫ t in 0..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) ^ 2
      - D ^ 2 * ε ≤ risk := by
  simpa using path_risk_lower_bound (intervalIntegral.integral_nonneg_of_forall hδ (fun t => Real.sqrt_nonneg _)) hr (abs_nonneg _) (probability_absolutelyContinuous_score_path_separation_le hδ hr hprob hT hR hcenter hAC hderiv hrisk hscoreInt) hriskEq

end NearlyMinimax
