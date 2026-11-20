/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.FiniteRandomTestLimit
public import DOZZ.GMC.ConvergenceApproximation

/-! Uniform probability approximation for correlated random compact tests. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- A uniformly negligible probability approximation preserves the cutoff limit.
The approximants may be selected using the same outcome as the chaos. -/
theorem tendstoInMeasure_uniform_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (a : ℕ → ℕ → Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hconv : ∀ k, TendstoInMeasure P (a k) atTop (b k))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ e : ℕ → ℝ≥0∞,
      Tendsto e atTop (𝓝 0) ∧
      (∀ k n, P {ω | ε ≤ ‖f n ω - a k n ω‖} ≤ e k) ∧
      (∀ k, P {ω | ε ≤ ‖b k ω - g ω‖} ≤ e k)) :
    TendstoInMeasure P f atTop g := by
  apply tendstoInMeasure_of_probApprox
  intro ε hε δ hδ
  obtain ⟨e, he, hl, hr⟩ := happrox ε hε
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.mp he δ hδ).exists
  exact ⟨a k, b k, hconv k,
    Eventually.of_forall fun n => by simpa only [dist_eq_norm] using (hl k n).trans hk,
    by simpa only [dist_eq_norm] using (hr k).trans hk⟩

end DOZZ.Proofs
