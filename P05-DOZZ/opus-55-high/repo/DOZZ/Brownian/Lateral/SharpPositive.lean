/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.ReferenceIntensity
public import DOZZ.Brownian.Lateral.PositiveUniform
public import DOZZ.Brownian.Lateral.RadialWindowUniform

/-!
# Positive lateral moments from the proved sharp reference induction

Stationarity moves a given lateral interval into a small logarithmic reference chart.
The source annulus is contained in a small reference ball, whose entire positive
subcritical moment range is now proved. Radial independence then transfers that bound
to the given lateral measure. No moment assumption is added to its source predicate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Moving the left logarithmic endpoint to log eight puts the entire source annulus in the
reference disk of radius one eighth, whatever the interval length. -/
theorem lateral_shifted_annulus_subset_reference_ball (a b : ℝ) :
    lateralLogAnnulus (a + (Real.log 8 - a)) (b + (Real.log 8 - a)) ⊆
      Metric.ball (0 : ℂ) (1 / 8) := by
  have he : Real.exp (-(a + (Real.log 8 - a))) = 1 / 8 := by
    rw [show a + (Real.log 8 - a) = Real.log 8 by ring, Real.exp_neg,
      Real.exp_log (by norm_num)]
    simp
  simpa only [he] using lateralLogAnnulus_subset_ball
    (a + (Real.log 8 - a)) _
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- Every nonnegative subcritical moment of the moved source annulus is finite. This is an
actual consequence of the proved reference induction, not a source-moment premise. -/
theorem sourceLateral_shifted_annulus_nonnegative_moment_finite
    (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hS : IsSourceLateralProjection P X γ M Z) (hγ : 0 < γ)
    (a b q : ℝ) (hq : 0 ≤ q) (hcrit : q < 4 / γ ^ 2) :
    (∫⁻ ω, (M ω (lateralLogAnnulus
      (a + (Real.log 8 - a)) (b + (Real.log 8 - a)))) ^ q ∂P) < ⊤ := by
  have hfin := gmc_reference_nonnegative_moment_finite P X hS.1 γ q hγ hq hcrit
    M hS.2.1 (by norm_num) le_rfl
  apply lt_of_le_of_lt _ hfin
  exact lintegral_mono (fun ω => ENNReal.rpow_le_rpow
    (measure_mono (lateral_shifted_annulus_subset_reference_ball a b)) hq)

/-- The full pointwise positive subcritical range holds for every given lateral chaos.
Translation and radial independence remove all source-ball and annular moment premises. -/
theorem lateralGMC_interval_nonnegative_moment_finite
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hq : 0 ≤ q) (hcrit : q < 4 / γ ^ 2) :
    (∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P) < ⊤ := by
  rw [← lateralGMC_interval_moment_translation_eq P γ Z hZ a b q _]
  obtain ⟨X, M, hS⟩ := hZ.2.2.2.2.2.2.2.2
  exact sourceLateral_interval_moment_finite_of_annular P X γ M Z hS hZ.2.2.2.1
    (a + (Real.log 8 - a)) _ q
    (sourceLateral_shifted_annulus_nonnegative_moment_finite P X γ M Z hS hZ.1 a b q hq hcrit)

end

end DOZZ.Proofs
