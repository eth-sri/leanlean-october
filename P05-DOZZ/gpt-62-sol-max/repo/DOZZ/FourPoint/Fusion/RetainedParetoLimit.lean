/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedPareto
import Mathlib.Tactic

/-! A normalized Pareto limit from the leading moment and a first-order error. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Eventually near the puncture, `z` avoids both fixed roots and lies in the unit disk. -/
theorem eventually_punctured_unitBall :
    ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ z ≠ 1 ∧ ‖z‖ < 1 := by
  have hn : ContinuousAt norm (0 : ℂ) := continuous_norm.continuousAt
  filter_upwards [self_mem_nhdsWithin, hn.eventually_lt_const (by simp : ‖(0 : ℂ)‖ < 1) |>.filter_mono
    nhdsWithin_le_nhds] with z hz hnorm
  exact ⟨hz, fun he => by simp [he] at hnorm, hnorm⟩

private theorem normalized_limit_of_abs_error {ι : Type*} {l : Filter ι} {D L F r : ι → ℝ} {C Λ : ℝ}
    (hr : ∀ x, 0 ≤ r x) (hL : Tendsto (fun x => L x / r x) l (𝓝 Λ))
    (hF : Tendsto (fun x => F x / r x) l (𝓝 0))
    (hbound : ∀ᶠ x in l, |D x - L x| ≤ C * F x) : Tendsto (fun x => D x / r x) l (𝓝 Λ) := by
  have hE : Tendsto (fun x => (D x - L x) / r x) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using hF.const_mul C)
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs, abs_div, abs_of_nonneg (hr x), mul_div_assoc] using
      div_le_div_of_nonneg_right hx (hr x)
  simpa only [← add_div, sub_add_cancel, zero_add] using hE.add hL

theorem fusion_retained_pareto_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (β e α₁ α₂ α₃ ξ h p κ Λ : ℝ) (hβ : β < Q γ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z) (S₀ : Ω → ℝ≥0∞)
    (hSm : AEMeasurable S₀ P) (hSle : ∀ ω, S₀ ω ≤ twoSidedReflectionMass γ B Z ω)
    (hL : Tendsto (fun z : ℂ => weightedInverseMoment P (p+2*(Q γ-α₁)/γ)
      (fun ω => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ)
      (fun ω => (fusionRadialScale γ e (Q γ-α₁) h Xc z ω)^(2*(Q γ-α₁)/γ)) / ‖z‖^κ)
      (𝓝[≠] (0 : ℂ)) (𝓝 Λ))
    (hF : Tendsto (fun z : ℂ => weightedInverseMoment P (p+1)
      (fun ω => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ)
      (fusionRadialScale γ e (Q γ-α₁) h Xc z) / ‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0)) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let A := fun z ω => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ
    let b := fusionRadialScale γ e ν h Xc
    Tendsto (fun z : ℂ => (∫ v, paretoMassIncrement a p (A z) S₀ (b z) v ∂P.prod P) / ‖z‖^κ)
      (𝓝[≠] (0 : ℂ)) (𝓝 (paretoLeadingCoefficient a p * Λ * (∫⁻ ω, S₀ ω ^ a ∂P).toReal)) := by
  let a := 2*(Q γ-α₁)/γ
  let c := paretoLeadingCoefficient a p
  let J := (∫⁻ ω, S₀ ω ∂P).toReal
  let S := (∫⁻ ω, S₀ ω ^ a ∂P).toReal
  dsimp only
  apply normalized_limit_of_abs_error (C := a*p/(1-a)*J) (F := _)
    (fun z => Real.rpow_nonneg (norm_nonneg z) κ)
    (L := fun z => c * weightedInverseMoment P (p+a)
      (fun ω => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ)
      (fun ω => (fusionRadialScale γ e (Q γ-α₁) h Xc z ω)^a) * S)
  · convert (hL.const_mul c).mul_const S using 1
    funext z
    ring
  · exact hF
  · filter_upwards [eventually_punctured_unitBall] with z ⟨hz₀, hz₁, hzn⟩
    simpa only [mul_right_comm _ J] using (fusion_retained_pareto_increment_error P X hX γ hγ hγ₂
      M hM Xc hc β e α₁ α₂ α₃ ξ h p hβ hα₁ hreflect hα₂ hα₃ hh hp hξ hξ1
      B Z hData S₀ hSm hSle z hz₀ hz₁ hzn.le).2

end DOZZ.Proofs
