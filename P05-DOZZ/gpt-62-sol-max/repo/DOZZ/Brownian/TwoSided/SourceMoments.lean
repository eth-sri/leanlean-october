/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseGamma
public import DOZZ.GMC.SharpMoments.BallScaling
public import DOZZ.Brownian.Lateral.SharpPositive
public import DOZZ.Brownian.LateralUnitBlock.LateralInverse

/-! Charge-uniform reference moments, independent of the chosen source witnesses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Fatou only needs the cutoff estimate after time one; no coarse-cutoff premise is added. -/
theorem twosided_reference_moment_le_of_fine_cutoffs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (p : ℝ) (C : ℝ≥0∞)
    (hbound : ∀ r : ℝ, 1 ≤ r →
      gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 (1 / 8)) p ≤ C) :
    gmcMassMoment P M (Metric.ball 0 (1 / 8)) p ≤ C := by
  let A : Set ℂ := Metric.ball 0 (1 / 8)
  let f : ℕ → Ω → ℝ := fun n ω => (regularizedGMC P Xc γ (n + 1 : ℕ) ω A).toReal
  let g : Ω → ℝ := fun ω => (M ω A).toReal
  have hseq : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hconv : TendstoInMeasure P f atTop g :=
    (regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc A
      Metric.isOpen_ball.measurableSet (1 / 8) Metric.ball_subset_closedBall).comp hseq
  have hfmeas (n : ℕ) : Measurable (f n) :=
    measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ _ A Metric.isOpen_ball.measurableSet
  have hpow (n : ℕ) : AEMeasurable
      (fun ω => ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p) P :=
    (ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp ((hfmeas n).max measurable_const))).aemeasurable
  have hfbound (n : ℕ) : (∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p ∂P) ≤ C := by
    refine le_trans (le_of_eq ?_) (hbound (n + 1 : ℕ) (by exact_mod_cast Nat.le_add_left 1 n))
    unfold gmcMassMoment
    apply lintegral_congr_ae
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ (n + 1 : ℕ)] with ω hω
    let _ := hω
    dsimp only [f]
    rw [max_eq_left ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hfatou := lintegral_ennreal_rpow_le_of_tendstoInMeasure P f g p C hconv hpow
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hfbound
  refine le_trans (le_of_eq ?_) hfatou
  unfold gmcMassMoment
  apply lintegral_congr
  intro ω
  let _ := hM.1 ω
  exact congrArg (fun x : ℝ≥0∞ => x ^ p) (ENNReal.ofReal_toReal (measure_ne_top (M ω) A)).symm

/-- One fixed equator witness at the maximal charge bounds every source witness and every
smaller charge, at any single convex subcritical order. -/
theorem twosided_reference_convex_moments_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → Distr) (hY : IsEquatorGFF P Y)
    (Yc : Ω → ℂ → ℝ → ℝ) (hYc : IsCircleAverage P Y Yc)
    (g : ℝ) (hg : 0 < g) (hg2 : g < 2) (p : ℝ)
    (hp : p < 0 ∨ 1 ≤ p) (hcrit : p < 4 / g ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ g →
      ∀ X : Ω → Distr, ∀ M : Ω → Measure ℂ,
        IsEquatorGFF P X → IsGMCOf P X γ M →
          gmcMassMoment P M (Metric.ball 0 (1 / 8)) p ≤ C := by
  have hfixed : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ r : ℝ, 0 ≤ r →
      gmcMassMoment P (regularizedGMC P Yc g r) (Metric.ball 0 (1 / 8)) p ≤ C := by
    rcases hp with hp | hp
    · obtain ⟨K, hK⟩ := regularizedGMC_reference_inverse_moment_uniform P Y hY Yc hYc
        g hg hg2 (-p) (neg_pos.mpr hp)
      refine ⟨ENNReal.ofReal K, ENNReal.ofReal_lt_top, ?_⟩
      intro r hr
      change (∫⁻ ω, (regularizedGMC P Yc g r ω (Metric.ball 0 (1 / 8))) ^ p ∂P) ≤ _
      simpa only [neg_neg] using hK r hr
    · exact regularizedGMC_reference_moment_uniform_nonnegative P Y hY Yc hYc g p hg
        (le_trans zero_le_one hp) hcrit (by norm_num) le_rfl
  obtain ⟨C, hC, hbound⟩ := hfixed
  refine ⟨C, hC, ?_⟩
  intro γ hγ hγg X M hX hM
  obtain ⟨Xc, hXc, -⟩ := hM.2
  apply twosided_reference_moment_le_of_fine_cutoffs P X hX γ hγ (lt_of_le_of_lt hγg hg2)
    M hM Xc hXc p C
  intro r hr
  exact ((regularizedGMC_convex_moment_le_of_gamma_le P X hX Xc hXc P Y hY Yc hYc γ g r hγ hγg
    (Metric.ball 0 (1 / 8)) Metric.isOpen_ball.measurableSet
    (circleField_covariance_nonneg_reference P X hX Xc hXc r hr) p (hp.imp le_of_lt id))).trans (hbound r (le_trans zero_le_one hr))

end DOZZ.Proofs
