/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.EntranceLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Bounded measurable tests for the entrance density limit

The finite Doob densities converge pointwise to the entrance density and both have unit mass.
Their overlap therefore tends to one, which upgrades pointwise convergence to convergence against
every bounded measurable test. This includes arbitrary Borel cylinder events, without a boundary
regularity restriction.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Probability densities converging pointwise transport every bounded measurable test. -/
theorem tendsto_lintegral_probabilityDensity_test
    {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (f : ℕ → E → ℝ≥0∞) (g : E → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hfm : ∀ n, (∫⁻ x, f n x ∂μ) = 1) (hgm : (∫⁻ x, g x ∂μ) = 1)
    (hfg : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (F : E → ℝ≥0∞) (hF : Measurable F)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hbound : ∀ x, F x ≤ K) :
    Tendsto (fun n => ∫⁻ x, f n x * F x ∂μ) atTop
      (𝓝 (∫⁻ x, g x * F x ∂μ)) := tendsto_lintegral_probabilityDensity_moving_test μ f g hf hg hfm hgm hfg
    (fun _ => F) F (fun _ => hF) K hK (fun _ => hbound)
    (fun _ => tendsto_const_nhds)

variable (P Q : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q) (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))

include P Q hB ν hν hQ n ds hds xs hxs hxlim in
/-- The finite Doob density converges to the entrance density against any bounded measurable
test along positive starting states tending to zero. -/
theorem brownianDoobFinitePDF_lintegral_tendsto_entrance_test

    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hbound : ∀ ys, F ys ≤ K) :
    Tendsto
      (fun k => ∫⁻ ys, brownianDoobFinitePDF ν n ds (xs k) ys * F ys
        ∂(volume : Measure (Fin n → ℝ)))
      atTop
      (𝓝 (∫⁻ ys, brownianEntranceFinitePDF ν n ds ys * F ys
        ∂(volume : Measure (Fin n → ℝ)))) := have hwithin := tendsto_nhdsWithin_iff.mpr ⟨hxlim, Eventually.of_forall hxs⟩;   tendsto_lintegral_probabilityDensity_test ℙ (fun k ys => brownianDoobFinitePDF ν n ds (xs k) ys) (brownianEntranceFinitePDF ν n ds) (fun k => measurable_brownianDoobFinitePDF ν hν n ds hds (xs k) (hxs k)) (measurable_brownianEntranceFinitePDF ν hν n ds hds) (fun k => lintegral_brownianDoobFinitePDF_one P hB ν hν n ds hds (xs k) (hxs k)) (lintegral_brownianEntranceFinitePDF_one Q ν hν hQ n ds hds) (fun ys => Tendsto.comp (brownianDoobFinitePDF_tendsto_entrance ν hν n ds hds ys) hwithin) F hF K hK hbound

include P Q hB ν hν hQ n ds hds xs hxs hxlim in
/-- The finite Doob probability measures converge on every measurable set to the entrance
finite-dimensional law. -/
theorem brownianDoobFinitePDF_measure_tendsto_entrance_event

    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    Tendsto
      (fun k => (volume.withDensity (brownianDoobFinitePDF ν n ds (xs k))) A)
      atTop
      (𝓝 ((volume.withDensity (brownianEntranceFinitePDF ν n ds)) A)) := by
  have htest := brownianDoobFinitePDF_lintegral_tendsto_entrance_test
    P Q hB ν hν hQ n ds hds xs hxs hxlim
    (A.indicator (fun _ : Fin n → ℝ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hA) 1 ENNReal.one_ne_top
    (fun ys => by
      by_cases hy : ys ∈ A <;> simp [hy])
  have hleft (k : ℕ) :
      (volume.withDensity (brownianDoobFinitePDF ν n ds (xs k))) A =
        ∫⁻ ys, brownianDoobFinitePDF ν n ds (xs k) ys *
          A.indicator (fun _ : Fin n → ℝ => (1 : ℝ≥0∞)) ys ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    apply lintegral_congr
    intro ys
    by_cases hy : ys ∈ A <;> simp [hy]
  have hright :
      (volume.withDensity (brownianEntranceFinitePDF ν n ds)) A =
        ∫⁻ ys, brownianEntranceFinitePDF ν n ds ys *
          A.indicator (fun _ : Fin n → ℝ => (1 : ℝ≥0∞)) ys ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    apply lintegral_congr
    intro ys
    by_cases hy : ys ∈ A <;> simp [hy]
  simpa only [hleft, hright] using htest

end DOZZ.Proofs

end
