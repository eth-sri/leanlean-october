/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseKahane
public import DOZZ.GMC.Construction.GMCIntensityAdapter
public import DOZZ.GMC.Moments.LimitFatou

/-! # Inverse moments of the limiting chaos on the logarithmic chart

Cutoff masses of bounded sets converge in `L¹`, hence in probability, to the limiting masses, so
Fatou transfers every cutoff-uniform extended moment bound to the limit. Applied to the
cutoff-uniform inverse moments of the reference disk and combined with exact scaling, this gives
every inverse moment of the limiting mass of every disk in the logarithmic chart; in particular
these masses are almost surely positive. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Fatou: a cutoff-uniform bound on an extended moment of a bounded set mass passes to every
`IsGMCOf` limit, for every real order. -/
theorem gmcMassMoment_le_of_cutoff_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hXc : IsCircleAverage P X Xc)
    A (hA : MeasurableSet A) R (hAR : A ⊆ Metric.closedBall (0 : ℂ) R)
    p (C : ℝ≥0∞)
    (hbound : ∀ r : ℝ, 0 ≤ r → gmcMassMoment P (regularizedGMC P Xc γ r) A p ≤ C) :
    gmcMassMoment P M A p ≤ C := by
  let _ : IsProbabilityMeasure P := hX.1
  have hL1 := equatorGFF_GMC_bounded_mass_l1_of_uniform_L1 P X hX γ hγ hγ2 M hM Xc hXc A hA R hAR
  -- convergence in measure of the real masses along the natural cutoffs
  let f : ℕ → Ω → ℝ := fun n ω => (regularizedGMC P Xc γ n ω A).toReal
  let g : Ω → ℝ := fun ω => (M ω A).toReal
  have hfmeas : ∀ n, Measurable (f n) := fun n =>
    measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ n A hA
  have hconv : TendstoInMeasure P f atTop g := by
    intro ε hε
    by_cases hεtop : ε = ⊤
    · have hzero : ∀ n, P {ω | ε ≤ edist (f n ω) (g ω)} = 0 := by
        intro n
        rw [hεtop]
        rw [(show {ω | (⊤ : ℝ≥0∞) ≤ edist (f n ω) (g ω)} = ∅ by ext ω; simp [edist_ne_top]), measure_empty]
      simp [hzero]
    · have hmarkov : ∀ n, P {ω | ε ≤ edist (f n ω) (g ω)} ≤
          (∫⁻ ω, ENNReal.ofReal |f n ω - g ω| ∂P) / ε := by
        intro n
        refine le_trans (measure_mono ?_) (meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable ((hfmeas n).aemeasurable.sub (ENNReal.measurable_toReal.comp_aemeasurable (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM A hA))))) hε.ne' hεtop)
        intro ω hω
        change ε ≤ edist (f n ω) (g ω) at hω
        change ε ≤ ENNReal.ofReal |f n ω - g ω|
        rwa [edist_dist, Real.dist_eq] at hω
      have hdiv : Tendsto (fun n => (∫⁻ ω, ENNReal.ofReal |f n ω - g ω| ∂P) / ε)
          atTop (𝓝 0) := by
        have := ENNReal.Tendsto.div_const (hL1.comp tendsto_natCast_atTop_atTop) (Or.inr hε.ne')
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
        (fun _ => zero_le) hmarkov
  have hfbound : ∀ n, ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p ∂P ≤ C := by
    intro n
    refine le_trans (le_of_eq ?_) (hbound n (Nat.cast_nonneg n))
    unfold gmcMassMoment
    apply lintegral_congr_ae
    filter_upwards [(fun n : ℕ => regularizedGMC_finite_ae P X hX Xc hXc γ (n : ℝ)) n] with ω hω
    rw [max_eq_left ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine le_trans (le_of_eq ?_) (lintegral_ennreal_rpow_le_of_tendstoInMeasure P f g p C hconv (fun n => (ENNReal.continuous_rpow_const.measurable.comp (ENNReal.measurable_ofReal.comp ((hfmeas n).max measurable_const))).aemeasurable) (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hfbound)
  unfold gmcMassMoment
  apply lintegral_congr
  intro ω
  have : IsFiniteMeasure (M ω) := hM.1 ω
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Every inverse moment of the limiting mass of the reference disk is finite. -/
theorem gmc_reference_inverse_moment_lt_top
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    q (hq : 0 < q) :
    gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-q) < ⊤ := by
  obtain ⟨Xc, hXc, -⟩ := hM.2
  obtain ⟨K, hK⟩ := regularizedGMC_reference_inverse_moment_uniform P X hX Xc hXc γ hγ hγ2 q hq
  exact (gmcMassMoment_le_of_cutoff_uniform P X hX γ hγ hγ2 M hM Xc hXc (Metric.ball 0 (1 / 8)) Metric.isOpen_ball.measurableSet (1 / 8) Metric.ball_subset_closedBall (-q) (ENNReal.ofReal K) hK).trans_lt ENNReal.ofReal_lt_top

end DOZZ.Proofs
