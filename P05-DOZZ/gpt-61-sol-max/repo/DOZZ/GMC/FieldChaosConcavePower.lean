/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosConvexOrder
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic

/-! Positive subunit Kahane comparison for continuum field chaos. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Kahane's comparison for concave powers `0 < p < 1` of continuum field chaos. -/
theorem kahane_field_power_concave
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 0 < p ∧ p < 1)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX ≤ ∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≥
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  classical
  let := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  by_cases hν0 : ν = 0
  · simp [DOZZ.fieldChaosMass, hν0]
  have : Nonempty S := by
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν0)
    exact ⟨x⟩
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := fun hzero => hν0 (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero)
  change (∫⁻ ω, DOZZ.fieldChaosMass PX Φ (νf : Measure S) h γ ω ^ p ∂PX) ≥
    ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ (νf : Measure S) h γ ω ^ p ∂PY
  let mY := fun ω => (DOZZ.fieldChaosMass PY Ψ (νf : Measure S) h γ ω).toReal
  have hIY : Integrable (fun ω => mY ω ^ p) PY := by
    apply ((fieldChaosMass_toReal_integrable PY Ψ hΨ νf h hh hhb γ).add (integrable_const 1)).mono'
    · apply Measurable.aestronglyMeasurable
      exact Measurable.pow_const ((centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ ν h hh γ).ennreal_toReal) p
    · filter_upwards [] with ω
      change ‖mY ω ^ p‖ ≤ mY ω + 1
      have hn : 0 ≤ mY ω := ENNReal.toReal_nonneg
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg p)]
      by_cases hx : mY ω ≤ 1
      · exact (Real.rpow_le_one ENNReal.toReal_nonneg hx hp.1.le).trans (by linarith only [hn])
      · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hx) hp.2.le).trans (by linarith only)
  have hdiag' : ∀ᵐ x ∂ν, DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
      DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := by
    simpa only [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hdiag
  have hcmp := kahane_field_convex_real_nonzero PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ hcov hdiag'
    (fun x => -(x ^ p)) (by fun_prop) (Real.concaveOn_rpow hp.1.le hp.2.le).neg hIY.neg
  have hIX : Integrable (fun ω => (DOZZ.fieldChaosMass PX Φ (νf : Measure S) h γ ω).toReal ^ p) PX := by
    simpa only [Pi.neg_apply, neg_neg] using hcmp.1.fun_neg
  rw [lintegral_congr_ae (fieldChaosMass_rpow_toReal_ae PX Φ hΦ νf h hh hhb γ p hp.1.le),
    lintegral_congr_ae (fieldChaosMass_rpow_toReal_ae PY Ψ hΨ νf h hh hhb γ p hp.1.le)]
  rw [← ofReal_integral_eq_lintegral_ofReal hIX (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg p),
    ← ofReal_integral_eq_lintegral_ofReal hIY (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg p)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [integral_neg, neg_le_neg_iff] using hcmp.2

end DOZZ.Proofs
