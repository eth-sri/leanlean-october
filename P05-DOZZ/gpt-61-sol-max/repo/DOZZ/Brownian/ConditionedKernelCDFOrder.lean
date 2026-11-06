/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelStartRatio
public import Mathlib.Probability.CDF

/-!
# CDF comparison from a monotone likelihood ratio

This is the integration step between the explicit likelihood-ratio calculations and the
single-step stochastic order needed for the ordered coupling. It is stated for general densities
supported on the positive half-line so entrance and transition densities can use the same result.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped Topology

namespace DOZZ.Proofs

/-- The generalized inverse of a real-valued cumulative distribution function. -/
noncomputable def cdfGeneralizedQuantile (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  sInf {x | u ≤ F x}

theorem cdf_superlevel_nonempty
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ} (hu : u < 1) :
    {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu)).exists
  exact ⟨x, hx.le⟩

theorem cdf_superlevel_bddBelow
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 < u) :
    BddBelow {x | u ≤ ProbabilityTheory.cdf μ x} := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1
    ((ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hu))
  refine ⟨a, fun x hx => ?_⟩
  by_contra h
  exact (ha x (le_of_lt (lt_of_not_ge h))).not_ge hx

/-- A shifted CDF bound gives the same additive bound for common-level quantiles. -/
theorem cdfGeneralizedQuantile_le_add_of_cdf_le_shift
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u d : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (h : ∀ x, ProbabilityTheory.cdf μ x ≤ ProbabilityTheory.cdf ν (x + d)) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf ν) u ≤
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u + d := by
  rw [← sub_le_iff_le_add]
  change cdfGeneralizedQuantile (ProbabilityTheory.cdf ν) u - d ≤
    sInf {x | u ≤ ProbabilityTheory.cdf μ x}
  refine le_csInf (cdf_superlevel_nonempty hu1) fun x hx => ?_
  rw [sub_le_iff_le_add]
  exact csInf_le (cdf_superlevel_bddBelow hu) (le_trans hx (h x))

/-- A probability law with no mass at or below zero has strictly positive common-level
generalized quantiles at every level in `(0,1)`. Right continuity of the CDF at zero supplies a
positive lower bound for its superlevel set. -/
theorem cdfGeneralizedQuantile_pos_of_cdf_zero_nonpos
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hzero : ∀ x ≤ 0, ProbabilityTheory.cdf μ x = 0) :
    0 < cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u := by
  have ht := (((ProbabilityTheory.cdf μ).right_continuous 0).mono
    Set.Ioi_subset_Ici_self).tendsto
  rw [hzero 0 le_rfl] at ht
  obtain ⟨x, hx, hxpos⟩ := ((ht.eventually (Iio_mem_nhds hu)).and self_mem_nhdsWithin).exists
  change 0 < sInf {x | u ≤ ProbabilityTheory.cdf μ x}
  refine hxpos.trans_le (le_csInf (cdf_superlevel_nonempty hu1) fun y hy => ?_)
  exact le_of_not_gt fun hyx => not_le_of_gt hx (le_trans hy (ProbabilityTheory.monotone_cdf μ hyx.le))

/-- Pointwise CDF order reverses the order of generalized quantiles whenever the lower CDF reaches
the quantile level and the upper CDF's superlevel set is bounded below. -/
theorem cdfGeneralizedQuantile_antitone
    {F G : ℝ → ℝ} {u : ℝ}
    (hFG : ∀ x, F x ≤ G x)
    (hF : {x | u ≤ F x}.Nonempty)
    (hG : BddBelow {x | u ≤ G x}) :
    cdfGeneralizedQuantile G u ≤ cdfGeneralizedQuantile F u := by
  apply csInf_le_csInf hG hF
  intro x hx
  exact hx.trans (hFG x)

/-- CDF order reverses common-level quantiles of probability laws. -/
theorem cdfGeneralizedQuantile_antitone_of_cdf_le
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (h : ∀ x, ProbabilityTheory.cdf μ x ≤ ProbabilityTheory.cdf ν x) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf ν) u ≤
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u :=
  cdfGeneralizedQuantile_antitone h (cdf_superlevel_nonempty hu1) (cdf_superlevel_bddBelow hu)

/-- Translation of a lower-tail integral under Lebesgue measure. -/
theorem integral_Iic_add_shift {f : ℝ → ℝ} (d z : ℝ) :
    (∫ y in Set.Iic z, f (y + d) ∂(volume : Measure ℝ)) =
      ∫ y in Set.Iic (z + d), f y ∂(volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun x : ℝ => x + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have h := he.setIntegral_map (μ := (volume : Measure ℝ)) f (Set.Iic (z + d))
  rw [Measure.IsAddRightInvariant.map_add_right_eq_self d] at h
  simpa using h.symm

/-- If two probability densities on `(0,∞)` have an increasing likelihood ratio, the second
density assigns no more mass to any lower half-line. -/
theorem integral_Iic_le_of_monotoneDensityRatio
    {f g r : ℝ → ℝ}
    (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ))
    (hnf : ∀ x, 0 ≤ f x)
    (hzero_f : ∀ x, x ≤ 0 → f x = 0)
    (hzero_g : ∀ x, x ≤ 0 → g x = 0)
    (hunit_f : ∫ x, f x = 1) (hunit_g : ∫ x, g x = 1)
    (hfactor : ∀ x, 0 < x → g x = r x * f x)
    (hratio : MonotoneOn r (Set.Ioi 0))
    (z : ℝ) :
    ∫ x in Set.Iic z, g x ∂(volume : Measure ℝ) ≤
      ∫ x in Set.Iic z, f x ∂(volume : Measure ℝ) := by
  by_cases hz : z ≤ 0
  · rw [setIntegral_congr_fun measurableSet_Iic (fun x hx => hzero_g x (hx.trans hz)),
      setIntegral_congr_fun measurableSet_Iic (fun x hx => hzero_f x (hx.trans hz))]
  · have hzpos : 0 < z := lt_of_not_ge hz
    by_cases hrz : r z ≤ 1
    · apply setIntegral_mono_on (μ := (volume : Measure ℝ))
        hg.integrableOn hf.integrableOn measurableSet_Iic
      intro x hx
      by_cases hx0 : x ≤ 0
      · rw [hzero_g x hx0, hzero_f x hx0]
      · have hxpos : 0 < x := lt_of_not_ge hx0
        have hxz : x ≤ z := hx
        rw [hfactor x hxpos]
        have hratio_xz := hratio hxpos (Set.mem_Ioi.mpr hzpos) hxz
        nlinarith [hnf x]
    · have hrz' : 1 < r z := lt_of_not_ge hrz
      have htail :
          ∫ x in Set.Ioi z, f x ∂(volume : Measure ℝ) ≤
            ∫ x in Set.Ioi z, g x ∂(volume : Measure ℝ) := by
        apply setIntegral_mono_on (μ := (volume : Measure ℝ))
          hf.integrableOn hg.integrableOn measurableSet_Ioi
        intro x hx
        have hxpos : 0 < x := lt_trans hzpos hx
        have hrzx := hratio (Set.mem_Ioi.mpr hzpos) (Set.mem_Ioi.mpr hxpos) hx.le
        rw [hfactor x hxpos]
        nlinarith [hnf x]
      have hsplit_f :
          (∫ x in Set.Iic z, f x ∂(volume : Measure ℝ)) +
            ∫ x in Set.Ioi z, f x ∂(volume : Measure ℝ) = 1 := by
        have hs := integral_add_compl (μ := (volume : Measure ℝ))
          (f := f) (s := Set.Iic z) measurableSet_Iic hf
        simpa [compl_Iic, hunit_f] using hs
      have hsplit_g :
          (∫ x in Set.Iic z, g x ∂(volume : Measure ℝ)) +
            ∫ x in Set.Ioi z, g x ∂(volume : Measure ℝ) = 1 := by
        have hs := integral_add_compl (μ := (volume : Measure ℝ))
          (f := g) (s := Set.Iic z) measurableSet_Iic hg
        simpa [compl_Iic, hunit_g] using hs
      linarith

/-- A translated law may have extra mass to the left of zero. If its likelihood ratio against a
normalized positive-half-line law is positive and antitone, then its
full lower-tail distribution function is larger. This is the single-crossing step for the shifted
transition kernels. -/
theorem integral_Iic_ge_of_shiftedAntitoneDensityRatio
    {f g r : ℝ → ℝ}
    (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ))
    (hng : ∀ x, 0 ≤ g x)
    (hzero_f : ∀ x, x ≤ 0 → f x = 0)
    (hunit_f : ∫ x, f x = 1) (hunit_g : ∫ x, g x = 1)
    (hfactor : ∀ x, 0 < x → g x = r x * f x)
    (hrpos : ∀ x, 0 < x → 0 < r x)
    (hratio : AntitoneOn r (Set.Ioi 0))
    (z : ℝ) :
    ∫ x in Set.Iic z, f x ∂(volume : Measure ℝ) ≤
      ∫ x in Set.Iic z, g x ∂(volume : Measure ℝ) := by
  have hnf : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : 0 < x
    · exact nonneg_of_mul_nonneg_right (hfactor x hx ▸ hng x) (hrpos x hx)
    · rw [hzero_f x (le_of_not_gt hx)]
  by_cases hz : z ≤ 0
  · rw [setIntegral_congr_fun measurableSet_Iic (fun x hx => hzero_f x (hx.trans hz))]
    simpa using setIntegral_nonneg measurableSet_Iic (fun x _ => hng x)
  · have hzpos : 0 < z := lt_of_not_ge hz
    by_cases hrz : 1 ≤ r z
    · apply setIntegral_mono_on hf.integrableOn hg.integrableOn measurableSet_Iic
      intro x hx
      by_cases hxpos : 0 < x
      · rw [hfactor x hxpos]
        exact le_mul_of_one_le_left (hnf x) (hrz.trans (hratio hxpos hzpos hx))
      · rw [hzero_f x (le_of_not_gt hxpos)]
        exact hng x
    · have htail : (∫ x in Set.Ioi z, g x) ≤ ∫ x in Set.Ioi z, f x := by
        apply setIntegral_mono_on hg.integrableOn hf.integrableOn measurableSet_Ioi
        intro x hx
        rw [hfactor x (hzpos.trans hx)]
        exact mul_le_of_le_one_left (hnf x)
          ((hratio hzpos (hzpos.trans hx) hx.le).trans (le_of_not_ge hrz))
      have hf' := setIntegral_compl (s := Set.Ioi z) measurableSet_Ioi hf
      have hg' := setIntegral_compl (s := Set.Ioi z) measurableSet_Ioi hg
      rw [compl_Ioi, hunit_f] at hf'
      rw [compl_Ioi, hunit_g] at hg'
      linarith

end DOZZ.Proofs

end
