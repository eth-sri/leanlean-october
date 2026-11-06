/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosConstantTrickCore

/-! The common Gaussian scalar constant trick for concave continuum moments. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Continuum constant trick for concave powers `0 < p < 1`. -/
abbrev kahane_field_constant_trick_concave
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ C p : ℝ) (hC : 0 ≤ C)
    (hp : 0 < p ∧ p < 1)
 :=
  kahane_field_constant_trick_of_abs PX PY Φ Ψ hΦ hΨ ν h hh hhb γ C p (p-p^2) hC
    (by rw [abs_of_neg (by nlinarith [mul_pos hp.1 (sub_pos.mpr hp.2)])]; ring)

end DOZZ.Proofs
