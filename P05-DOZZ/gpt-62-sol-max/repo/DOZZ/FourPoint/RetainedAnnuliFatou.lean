/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.BallScaling
public import DOZZ.FourPoint.RetainedAnnuliSeparated

/-! Fatou passage for a product of retained masses, without assuming independence. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Two convergence-in-measure statements share an almost surely convergent subsequence. -/
theorem two_mass_fatou
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f₀ f₁ : ℕ → Ω → ℝ) (g₀ g₁ : Ω → ℝ) (p q : ℝ)
    (hf₀ : TendstoInMeasure P f₀ atTop g₀) (hf₁ : TendstoInMeasure P f₁ atTop g₁)
    (hmeas : ∀ n, AEMeasurable
      (fun ω => (ENNReal.ofReal (f₀ n ω)) ^ p * (ENNReal.ofReal (f₁ n ω)) ^ q) P)
    (hg₀ : ∀ᵐ ω ∂P, 0 < g₀ ω) (hg₁ : ∀ᵐ ω ∂P, 0 < g₁ ω)
    (R : ℕ → ℝ≥0∞) (C : ℝ≥0∞) (hR : Tendsto R atTop (nhds C))
    (hbound : ∀ n,
      (∫⁻ ω, (ENNReal.ofReal (f₀ n ω)) ^ p * (ENNReal.ofReal (f₁ n ω)) ^ q ∂P) ≤ R n) :
    (∫⁻ ω, (ENNReal.ofReal (g₀ ω)) ^ p * (ENNReal.ofReal (g₁ ω)) ^ q ∂P) ≤ C := by
  obtain ⟨s, hs, hsub₀⟩ := hf₀.exists_seq_tendsto_ae
  obtain ⟨t, ht, hsub₁⟩ := (hf₁.comp hs.tendsto_atTop).exists_seq_tendsto_ae
  let ns  := fun n => s (t n)
  have hns  := hs.tendsto_atTop.comp ht.tendsto_atTop
  let F  := fun n ω =>
    (ENNReal.ofReal (f₀ (ns n) ω)) ^ p * (ENNReal.ofReal (f₁ (ns n) ω)) ^ q
  have hlim : ∀ᵐ ω ∂P, liminf (fun n => F n ω) atTop =
      (ENNReal.ofReal (g₀ ω)) ^ p * (ENNReal.ofReal (g₁ ω)) ^ q := by
    filter_upwards [hsub₀, hsub₁, hg₀, hg₁] with ω h₀ h₁ hg₀ hg₁
    have he₀ : Tendsto (fun n => (ENNReal.ofReal (f₀ (ns n) ω)) ^ p) atTop
        (nhds ((ENNReal.ofReal (g₀ ω)) ^ p)) := ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (h₀.comp ht.tendsto_atTop))
    have he₁ : Tendsto (fun n => (ENNReal.ofReal (f₁ (ns n) ω)) ^ q) atTop
        (nhds ((ENNReal.ofReal (g₁ ω)) ^ q)) := ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp h₁)
    exact Tendsto.liminf_eq
      (ENNReal.Tendsto.mul he₀
        (Or.inr (ENNReal.rpow_ne_top_of_ne_zero (LT.lt.ne' (ENNReal.ofReal_pos.mpr hg₁)) ENNReal.ofReal_ne_top)) he₁
        (Or.inr (ENNReal.rpow_ne_top_of_ne_zero (LT.lt.ne' (ENNReal.ofReal_pos.mpr hg₀)) ENNReal.ofReal_ne_top)))
  exact Trans.trans
    (Trans.trans
      (Trans.trans (lintegral_congr_ae (Eventually.mono hlim fun x h => Eq.symm h))
        (lintegral_liminf_le' fun n => hmeas (ns n)))
      (liminf_le_liminf (Eventually.of_forall fun n => hbound (ns n)) isBounded_ge_of_bot isCobounded_ge_of_top))
    (Tendsto.liminf_eq (Tendsto.comp hR hns))

/-- Indicator weights retain exactly the original restricted field mass. -/
theorem fieldChaosMass_indicator
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (ν : Measure S)
    (A U : Set S) (hA : MeasurableSet A) (hAU : A ⊆ U) (γ : ℝ) (ω : Ω) :
    fieldChaosMass P Φ (ν.restrict U) (A.indicator (fun _ => (1 : ℝ≥0))) γ ω =
      fieldChaosMass P Φ (ν.restrict A) (fun _ => 1) γ ω := by
  unfold fieldChaosMass
  have he : (fun x => ((A.indicator (fun _ => (1 : ℝ≥0))) x : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) =
      A.indicator (fun x => ENNReal.ofReal
        (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, ENNReal.coe_one, one_mul]
    · simp only [Set.indicator_of_notMem hx, ENNReal.coe_zero, zero_mul]
  rw [he, lintegral_indicator hA, Measure.restrict_restrict hA,
    inter_eq_left.mpr hAU]
  simp

end DOZZ.Proofs
