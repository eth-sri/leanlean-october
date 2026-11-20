/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.EntranceLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded measurable tests for the entrance density limit

The finite Doob densities converge pointwise to the entrance density and both have unit mass.
Their overlap therefore tends to one, which upgrades pointwise convergence to convergence against
every bounded measurable test. This includes arbitrary Borel cylinder events, without a boundary
regularity restriction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The finite Doob density converges to the entrance density against any bounded measurable
test along positive starting states tending to zero. -/
theorem brownianDoobFinitePDF_lintegral_tendsto_entrance_test
    (P Q : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hbound : ∀ ys, F ys ≤ K) :
    Tendsto
      (fun k => ∫⁻ ys, brownianDoobFinitePDF ν n ds (xs k) ys * F ys
        ∂(volume : Measure (Fin n → ℝ)))
      atTop
      (𝓝 (∫⁻ ys, brownianEntranceFinitePDF ν n ds ys * F ys
        ∂(volume : Measure (Fin n → ℝ)))) := by
  have hwithin : Tendsto xs atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hxlim, Filter.Eventually.of_forall hxs⟩
  exact tendsto_lintegral_probabilityDensity_varying_test (volume : Measure (Fin n → ℝ)) (fun k ys => brownianDoobFinitePDF ν n ds (xs k) ys) (brownianEntranceFinitePDF ν n ds) (fun k => measurable_brownianDoobFinitePDF ν hν n ds hds (xs k) (hxs k)) (measurable_brownianEntranceFinitePDF ν hν n ds hds) (fun k => lintegral_brownianDoobFinitePDF_one P hB ν hν n ds hds (xs k) (hxs k)) (lintegral_brownianEntranceFinitePDF_one Q ν hν hQ n ds hds) (fun ys => (brownianDoobFinitePDF_tendsto_entrance ν hν n ds hds ys).comp hwithin)
    (fun _ => F) F (fun _ => hF) K hK (fun _ => hbound) (fun _ => tendsto_const_nhds)

/-- The finite Doob probability measures converge on every measurable set to the entrance
finite-dimensional law. -/
theorem brownianDoobFinitePDF_measure_tendsto_entrance_event
    (P Q : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
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
  have he (f : (Fin n → ℝ) → ℝ≥0∞) :
      (volume.withDensity f) A = ∫⁻ ys, f ys * A.indicator (fun _ => (1 : ℝ≥0∞)) ys ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    congr with ys
    by_cases hy : ys ∈ A <;> simp [hy]
  simpa only [he] using htest

end DOZZ.Proofs
