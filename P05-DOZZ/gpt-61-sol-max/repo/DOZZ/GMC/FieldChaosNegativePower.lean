/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosMultiNegativePower

/-! Scalar Kahane comparison as the one-block case of multiblock comparison. -/
public section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Kahane's comparison for all nonpositive powers of continuum field chaos. -/
theorem kahane_field_power_nonpos
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : p ≤ 0)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≤
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  simpa only [Fintype.prod_unique, neg_neg, ENNReal.rpow_eq_pow] using
    kahane_field_multi_negative_power (κ := Fin 1) PX PY Φ Ψ hΦ hΨ ν
      (fun _ => h) (fun _ => hh) (fun _ => hhb) γ (fun _ => -p)
      (fun _ => neg_nonneg.mpr hp) hcov hdiag

end DOZZ.Proofs
