/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosConvexOrder
public import DOZZ.GMC.FieldChaosMultiNegativePower

/-! Continuum Kahane comparison for all convex real powers. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Continuum Kahane comparison for convex powers, with the diagonal covariance condition
separate from the almost-everywhere off-diagonal condition. -/
theorem kahane_field_power_convex
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : p ≤ 0 ∨ 1 ≤ p)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX ≤ ∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≤
      ∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  rcases hp with hp | hp
  · exact kahane_field_power_nonpos PX PY Φ Ψ hΦ hΨ ν h hh hhb γ p hp hcov hdiag
  let := (hΦ.2 0 Fin.elim0).1
  let := (hΨ.2 0 Fin.elim0).1
  by_cases hν0 : ν = 0
  · simp [fieldChaosMass, hν0]
  have : Nonempty S := (nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν0)).nonempty
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := fun e => hν0 (congrArg FiniteMeasure.toMeasure e)
  have hd : ∀ᵐ x ∂(νf : Measure S),
      gaussianVariance PX (fun ω => Φ ω x) ≤ gaussianVariance PY (fun ω => Ψ ω x) := by
    change ∀ᵐ x ∂ν, _
    simpa [gaussianVariance, gaussianCovariance, pow_two] using hdiag
  change (∫⁻ ω, fieldChaosMass PX Φ νf h γ ω ^ p ∂PX) ≤
    ∫⁻ ω, fieldChaosMass PY Ψ νf h γ ω ^ p ∂PY
  rw [← fieldChaosMass_rpow_lintegral PX Φ hΦ νf h hh hhb γ p (by linarith),
    ← fieldChaosMass_rpow_lintegral PY Ψ hΨ νf h hh hhb γ p (by linarith)]
  exact kahane_field_convex_lintegral PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ
    (fun x => x ^ p) (by fun_prop) (fun _ hx => Real.rpow_nonneg hx _) (convexOn_rpow hp) hcov hd

end DOZZ.Proofs
