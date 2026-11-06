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

/-- A probability law with no mass at or below zero has strictly positive common-level
generalized quantiles at every level in `(0,1)`. Right continuity of the CDF at zero supplies a
positive lower bound for its superlevel set. -/
theorem cdfGeneralizedQuantile_pos_of_cdf_zero_nonpos
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hzero : ∀ x ≤ 0, ProbabilityTheory.cdf μ x = 0) :
    0 < cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u := by
  let S := {x | u ≤ ProbabilityTheory.cdf μ x}
  have hnonempty : S.Nonempty := by
    have hev : ∀ᶠ x : ℝ in atTop, u < ProbabilityTheory.cdf μ x :=
      (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (isOpen_Ioi.mem_nhds hu1)
    obtain ⟨x, hx⟩ := Filter.eventually_atTop.1 hev
    refine ⟨max x 0, ?_⟩
    grind
  have hbounded : BddBelow S := by
    refine ⟨0, ?_⟩
    intro x hx
    grind
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop
      (𝓝[Set.Ici 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      change 0 ≤ 1 / ((n : ℝ) + 1)
      positivity
  have hright : Tendsto (ProbabilityTheory.cdf μ)
      (𝓝[Set.Ici 0] 0) _ :=
    ((ProbabilityTheory.cdf μ).right_continuous 0).tendsto
  have hcdf : Tendsto (fun n : ℕ => ProbabilityTheory.cdf μ
      (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h := hright.comp hseq
    aesop
  have hlt : ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.cdf μ (1 / ((n : ℝ) + 1)) < u := by
    exact hcdf.eventually (isOpen_Iio.mem_nhds hu)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hlt
  let x₀ : ℝ := 1 / ((N : ℝ) + 1)
  have hx₀ : 0 < x₀ := by
    positivity
  have hlower : x₀ ≤ sInf S := by
    apply le_csInf hnonempty
    intro x hx
    change u ≤ ProbabilityTheory.cdf μ x at hx
    by_contra hnot
    have hxlt : x < x₀ := lt_of_not_ge hnot
    have hmono := ProbabilityTheory.monotone_cdf μ hxlt.le
    have hsmall := hN N (le_refl N)
    dsimp [x₀] at hxlt ⊢
    linarith
  exact lt_of_lt_of_le hx₀ (by assumption)

/-- Pointwise CDF order reverses the order of generalized quantiles whenever the lower CDF reaches
the quantile level and the upper CDF's superlevel set is bounded below. -/
theorem cdfGeneralizedQuantile_antitone
    {F G : ℝ → ℝ} {u : ℝ}
    (hFG : ∀ x, F x ≤ G x)
    (hF : {x | u ≤ F x}.Nonempty)
    (hG : BddBelow {x | u ≤ G x}) :
    cdfGeneralizedQuantile G u ≤ cdfGeneralizedQuantile F u := by
  apply csInf_le_csInf hG hF
  grind
section
variable {f g r : ℝ → ℝ}
section
variable (hf : Integrable f (volume : Measure ℝ)) (hg : Integrable g (volume : Measure ℝ))
include hf hg

/-- If two probability densities on `(0,∞)` have an increasing likelihood ratio, the second
density assigns no more mass to any lower half-line. -/
theorem integral_Iic_le_of_monotoneDensityRatio
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
  · have hzpos := lt_of_not_ge hz
    by_cases hrz : r z ≤ 1
    · apply setIntegral_mono_on (μ := volume)
        hg.integrableOn hf.integrableOn measurableSet_Iic
      intro x hx
      by_cases hx0 : x ≤ 0
      · simp_all
      · have hxpos := lt_of_not_ge hx0
        rw [hfactor x hxpos]
        have hratio_xz := hratio hxpos (Set.mem_Ioi.mpr hzpos) hx
        nlinarith [hnf x]
    · have hrz' := lt_of_not_ge hrz
      have htail :
          ∫ x in Set.Ioi z, f x ∂volume ≤
            ∫ x in Set.Ioi z, g x ∂volume := by
        apply setIntegral_mono_on (μ := volume)
          hf.integrableOn hg.integrableOn measurableSet_Ioi
        intro x hx
        have hxpos := lt_trans hzpos hx
        have hrzx := hratio (Set.mem_Ioi.mpr hzpos) (Set.mem_Ioi.mpr hxpos) hx.le
        rw [hfactor x hxpos]
        nlinarith [hnf x]
      have hsplit_f :
          (∫ x in Set.Iic z, f x ∂volume) +
            ∫ x in Set.Ioi z, f x ∂volume = 1 := by
        have hs := integral_add_compl (μ := volume)
          (f := f) (s := Set.Iic z) measurableSet_Iic hf
        simp_all
      have hsplit_g :
          (∫ x in Set.Iic z, g x ∂volume) +
            ∫ x in Set.Ioi z, g x ∂volume = 1 := by
        have hs := integral_add_compl (μ := volume)
          (f := g) (s := Set.Iic z) measurableSet_Iic hg
        simp_all
      linarith

/-- If the likelihood ratio of a second positive-half-line density is antitone, then its lower-tail
mass is at least that of the first density. This is the reverse single-crossing direction needed
for the shifted-kernel comparison. -/
theorem integral_Iic_ge_of_antitoneDensityRatio
    (hng : ∀ x, 0 ≤ g x)
    (hzero_f : ∀ x, x ≤ 0 → f x = 0)
    (hzero_g : ∀ x, x ≤ 0 → g x = 0)
    (hunit_f : ∫ x, f x = 1) (hunit_g : ∫ x, g x = 1)
    (hfactor : ∀ x, 0 < x → g x = r x * f x)
    (hrpos : ∀ x, 0 < x → 0 < r x)
    (hratio : AntitoneOn r (Set.Ioi 0))
    (z : ℝ) :
    ∫ x in Set.Iic z, f x ∂(volume : Measure ℝ) ≤
      ∫ x in Set.Iic z, g x ∂(volume : Measure ℝ) := by
  let rinv : ℝ → ℝ := fun x => 1 / r x
  have hInvMono : MonotoneOn rinv (Set.Ioi 0) := by
    intro x hx y hy hxy
    bound
  have hfactor' : ∀ x, 0 < x → f x = rinv x * g x := by
    grind
  exact integral_Iic_le_of_monotoneDensityRatio
    hg hf hng hzero_g hzero_f hunit_g hunit_f hfactor' hInvMono z

end

/-- A translated law may have extra mass to the left of zero. If its positive-half-line mass is
`m≤1` and its likelihood ratio against a normalized positive-half-line law is antitone, then its
full lower-tail distribution function is larger. This is the single-crossing step for the shifted
transition kernels. -/
theorem integral_Iic_ge_of_shiftedAntitoneDensityRatio
    {m : ℝ}
    (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ))
    (hng : ∀ x, 0 ≤ g x)
    (hzero_f : ∀ x, x ≤ 0 → f x = 0)
    (hunit_f : ∫ x, f x = 1) (hunit_g : ∫ x, g x = 1)
    (hmpos : 0 < m) (hmle : m ≤ 1)
    (hpositiveMass : (∫ x in Set.Ioi 0, g x ∂(volume : Measure ℝ)) = m)
    (hfactor : ∀ x, 0 < x → g x = r x * f x)
    (hrpos : ∀ x, 0 < x → 0 < r x)
    (hratio : AntitoneOn r (Set.Ioi 0))
    (z : ℝ) :
    ∫ x in Set.Iic z, f x ∂(volume : Measure ℝ) ≤
      ∫ x in Set.Iic z, g x ∂(volume : Measure ℝ) := by
  let gpos := Set.Ioi 0 |>.indicator (fun x => g x / m)
  have hgpos : Integrable gpos volume := (hg.div_const m).indicator measurableSet_Ioi
  have hngpos : ∀ x, 0 ≤ gpos x := by
    intro x
    by_cases hx : 0 < x
    · simp [gpos, hx]
      bound
    aesop
  have hzero_gpos : ∀ x, x ≤ 0 → gpos x = 0 := by
    aesop
  have hunit_gpos : ∫ x, gpos x ∂volume = 1 := by
    rw [integral_indicator measurableSet_Ioi]
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, hpositiveMass]
    field_simp
  let rpos : ℝ → ℝ := fun x => r x / m
  have hrpos' : ∀ x, 0 < x → 0 < rpos x := by
    intro x hx
    exact div_pos (hrpos x hx) hmpos
  have hfactor' : ∀ x, 0 < x → gpos x = rpos x * f x := by
    intro x hx
    simp [gpos, rpos, hx]
    rw [hfactor x hx]
    field_simp [hmpos.ne']
  have hratio' : AntitoneOn rpos (Set.Ioi 0) := by
    intro x hx y hy hxy
    exact (div_le_div_iff_of_pos_right hmpos).2 (hratio hx hy hxy)
  have hCDFpos := integral_Iic_ge_of_antitoneDensityRatio
    hf hgpos (by
      intro x
      exact hngpos x)
    hzero_f hzero_gpos hunit_f hunit_gpos hfactor' hrpos' hratio' z
  by_cases hz : z ≤ 0
  · rw [setIntegral_congr_fun measurableSet_Iic (fun x hx => hzero_f x (hx.trans hz))]
    simp
    exact setIntegral_nonneg measurableSet_Iic (fun x hx => hng x)
  · have hzpos := lt_of_not_ge hz
    have htailScale :
        (∫ x in Set.Ioi z, g x ∂volume) =
          m * ∫ x in Set.Ioi z, gpos x ∂volume := by
      calc
        (∫ x in Set.Ioi z, g x ∂volume) =
            ∫ x in Set.Ioi z, m * gpos x ∂volume := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              simp [gpos, (lt_trans hzpos hx)]
              field_simp [hmpos.ne']
        _ = m * ∫ x in Set.Ioi z, gpos x ∂volume := by
              rw [integral_const_mul]
    have htailpos_le :
        ∫ x in Set.Ioi z, gpos x ∂volume ≤
          ∫ x in Set.Ioi z, f x ∂volume := by
      have hsplitF :
          (∫ x in Set.Iic z, f x ∂volume) +
            ∫ x in Set.Ioi z, f x ∂volume = 1 := by
        have hs := integral_add_compl (μ := volume)
          (f := f) (s := Set.Iic z) measurableSet_Iic hf
        simpa [compl_Iic, hunit_f] using hs
      have hsplitGpos :
          (∫ x in Set.Iic z, gpos x ∂volume) +
            ∫ x in Set.Ioi z, gpos x ∂volume = 1 := by
        have hs := integral_add_compl (μ := (volume : Measure ℝ))
          (f := gpos) (s := Set.Iic z) measurableSet_Iic hgpos
        simpa [compl_Iic, hunit_gpos] using hs
      linarith
    have htailpos_nonneg :
        0 ≤ ∫ x in Set.Ioi z, gpos x ∂(volume : Measure ℝ) :=
      setIntegral_nonneg measurableSet_Ioi (fun x hx => hngpos x)
    have htailg_le :
        ∫ x in Set.Ioi z, g x ∂volume ≤
          ∫ x in Set.Ioi z, f x ∂volume := by
      rw [htailScale]
      calc
        m * ∫ x in Set.Ioi z, gpos x ∂volume ≤
            ∫ x in Set.Ioi z, gpos x ∂volume :=
              mul_le_of_le_one_left htailpos_nonneg hmle
        _ ≤ ∫ x in Set.Ioi z, f x ∂volume := htailpos_le
    have hsplitG :
        (∫ x in Set.Iic z, g x ∂volume) +
          ∫ x in Set.Ioi z, g x ∂volume = 1 := by
      have hs := integral_add_compl (μ := volume)
        (f := g) (s := Set.Iic z) measurableSet_Iic hg
      simpa [compl_Iic, hunit_g] using hs
    have hsplitF :
        (∫ x in Set.Iic z, f x ∂volume) +
          ∫ x in Set.Ioi z, f x ∂volume = 1 := by
      have hs := integral_add_compl (μ := volume)
        (f := f) (s := Set.Iic z) measurableSet_Iic hf
      simpa [compl_Iic, hunit_f] using hs
    linarith

end

end DOZZ.Proofs

end
