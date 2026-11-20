/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelStartRatio
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

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

section
variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ}

theorem probability_cdf_superlevel_nonempty (hu : u < 1) : {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  have h : ∀ᶠ x in atTop, u < ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu)
  obtain ⟨x, hx⟩ := h.exists
  exact ⟨x, hx.le⟩

theorem probability_cdf_superlevel_bddBelow (hu : 0 < u) : BddBelow {x | u ≤ ProbabilityTheory.cdf μ x} := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp ((ProbabilityTheory.tendsto_cdf_atBot μ).eventually_lt_const hu)
  refine ⟨a, fun x hx => ?_⟩
  by_contra! hxa
  exact (ha x hxa.le).not_ge hx

end

/-- Right continuity at zero gives a positive lower bound for the superlevel set. -/
theorem cdfGeneralizedQuantile_pos_of_cdf_zero_nonpos
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hzero : ∀ x ≤ 0, ProbabilityTheory.cdf μ x = 0) :
    0 < cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u := by
  have ht : Tendsto (ProbabilityTheory.cdf μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := ((ProbabilityTheory.cdf μ).right_continuous 0).tendsto
    rw [hzero 0 le_rfl] at h
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hm : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  obtain ⟨x, hx, hlt⟩ := (hm.and (ht.eventually_lt_const hu)).exists
  refine lt_of_lt_of_le (show 0 < x from hx) (le_csInf (probability_cdf_superlevel_nonempty hu1) ?_)
  intro y hy
  by_contra! hyx
  exact hlt.not_ge (hy.trans (ProbabilityTheory.monotone_cdf μ hyx.le))

/-- Translation is handled directly on the CDF superlevel sets: there is no need to
construct a translated probability measure to compare its quantiles. -/
theorem cdfGeneralizedQuantile_le_add {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {u d : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hCDF : ∀ x, ProbabilityTheory.cdf μ x ≤ ProbabilityTheory.cdf ν (x + d)) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf ν) u ≤
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u + d := by
  apply sub_le_iff_le_add.mp
  refine le_csInf (probability_cdf_superlevel_nonempty hu1) fun x hx => ?_
  exact sub_le_iff_le_add.mpr (csInf_le (probability_cdf_superlevel_bddBelow hu)
    ((show u ≤ ProbabilityTheory.cdf μ x from hx).trans (hCDF x)))

/-- Translation of a Lebesgue integral over a lower half-line. -/
theorem integral_Iic_add_shift {f : ℝ → ℝ} (d z : ℝ) :
    (∫ y in Iic z, f (y + d)) = ∫ y in Iic (z + d), f y := by
  have he : MeasurableEmbedding (fun x : ℝ => x + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hpre : (fun x : ℝ => x + d) ⁻¹' Iic (z + d) = Iic z := by ext x; simp
  simpa only [(measurePreserving_add_right (volume : Measure ℝ) d).map_eq, hpre] using
    (he.setIntegral_map (μ := (volume : Measure ℝ)) f (Iic (z + d))).symm

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

private theorem integral_Iic_le_of_Ioi_ge {f g : ℝ → ℝ} {z : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hf₁ : ∫ x, f x = 1) (hg₁ : ∫ x, g x = 1)
    (h : ∫ x in Ioi z, g x ≤ ∫ x in Ioi z, f x) :
    ∫ x in Iic z, f x ≤ ∫ x in Iic z, g x := by
  have hF := integral_add_compl (s := Iic z) measurableSet_Iic hf
  have hG := integral_add_compl (s := Iic z) measurableSet_Iic hg
  rw [compl_Iic, hf₁] at hF
  rw [compl_Iic, hg₁] at hG
  linarith

section
variable {f g r : ℝ → ℝ}

/-- If two probability densities on `(0,∞)` have an increasing likelihood ratio, the second
density assigns no more mass to any lower half-line. -/
theorem integral_Iic_le_of_monotoneDensityRatio
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
  · have hz' := lt_of_not_ge hz
    by_cases hr : r z ≤ 1
    · apply setIntegral_mono_on hg.integrableOn hf.integrableOn measurableSet_Iic
      intro x hx
      by_cases hx₀ : 0 < x
      · rw [hfactor x hx₀]
        exact mul_le_of_le_one_left (hnf x) ((hratio hx₀ hz' hx).trans hr)
      · rw [hzero_g x (le_of_not_gt hx₀), hzero_f x (le_of_not_gt hx₀)]
    · apply integral_Iic_le_of_Ioi_ge hg hf hunit_g hunit_f
      apply setIntegral_mono_on hf.integrableOn hg.integrableOn measurableSet_Ioi
      intro x hx
      have hx₀ := hz'.trans hx
      rw [hfactor x hx₀]
      exact le_mul_of_one_le_left (hnf x) ((le_of_not_ge hr).trans (hratio hz' hx₀ hx.le))

/-- An antitone likelihood ratio crosses one at most once. For a positive comparison
point, either the lower masses can be ordered directly, or the upper masses can be ordered
and subtracted from one. The shifted density may have additional mass on the left of zero. -/
theorem integral_Iic_ge_of_shiftedAntitoneDensityRatio (d z : ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (hnf : ∀ x, 0 ≤ f x) (hng : ∀ x, 0 ≤ g x)
    (hzero : ∀ x ≤ 0, f x = 0)
    (hf₁ : ∫ x, f x = 1) (hg₁ : ∫ x, g x = 1)
    (hfactor : ∀ x, 0 < x → g (x + d) = r x * f x)
    (hratio : AntitoneOn r (Ioi 0)) :
    ∫ x in Iic z, f x ≤ ∫ x in Iic z, g (x + d) := by
  have hG : Integrable (fun x => g (x + d)) :=
    (measurePreserving_add_right volume d).integrable_comp_of_integrable hg
  by_cases hz : 0 < z
  · by_cases hr : 1 ≤ r z
    · apply setIntegral_mono_on hf.integrableOn hG.integrableOn measurableSet_Iic
      intro x hx
      by_cases hx₀ : 0 < x
      · rw [hfactor x hx₀]
        exact le_mul_of_one_le_left (hnf x) (hr.trans (hratio hx₀ hz hx))
      · rw [hzero x (le_of_not_gt hx₀)]
        exact hng _
    · apply integral_Iic_le_of_Ioi_ge hf hG hf₁ (by rwa [integral_add_right_eq_self])
      apply setIntegral_mono_on hG.integrableOn hf.integrableOn measurableSet_Ioi
      intro x hx
      have hx₀ := hz.trans hx
      rw [hfactor x hx₀]
      exact mul_le_of_le_one_left (hnf x) ((hratio hz hx₀ hx.le).trans (le_of_not_ge hr))
  · apply setIntegral_mono_on hf.integrableOn hG.integrableOn measurableSet_Iic
    intro x hx
    rw [hzero x (hx.trans (le_of_not_gt hz))]
    exact hng _

end

end DOZZ.Proofs

end
