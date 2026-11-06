/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosConvexOrder
public import DOZZ.GMC.KahaneConvexOrderClosure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Continuum Kahane comparison for all convex real powers. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem kahane_field_power_ge_one_nonzero
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 1 ≤ p)
    (hcov : ∀ᵐ q ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω q.1) (fun ω => Φ ω q.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω q.1) (fun ω => Ψ ω q.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω ^ p ∂PX ≤
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω ^ p ∂PY := by
  let := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let mX := fun ω => (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal
  let mY := fun ω => (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal
  rw [lintegral_congr_ae (fieldChaosMass_rpow_toReal_ae PX Φ hΦ ν h hh hhb γ p (by linarith)),
    lintegral_congr_ae (fieldChaosMass_rpow_toReal_ae PY Ψ hΨ ν h hh hhb γ p (by linarith))]
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (mY ω ^ p) ∂PY) = ∞
  · rw [htop]
    exact le_top
  have hF : Measurable (fun x : ℝ => x ^ p) := by fun_prop
  have hIY : Integrable (fun ω => mY ω ^ p) PY := by
    refine ⟨(hF.comp_aemeasurable (fieldChaosMass_toReal_integrable PY Ψ hΨ ν h hh hhb γ).aemeasurable).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => Real.rpow_nonneg ENNReal.toReal_nonneg p)).2
      (lt_top_iff_ne_top.mpr htop)
  have hcmp := kahane_field_convex_real_nonzero PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ hcov hdiag
    (fun x => x ^ p) hF (convexOn_rpow hp) hIY
  rw [← ofReal_integral_eq_lintegral_ofReal hcmp.1 (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg p),
    ← ofReal_integral_eq_lintegral_ofReal hIY (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg p)]
  exact ENNReal.ofReal_le_ofReal hcmp.2

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
  classical
  by_cases hν0 : ν = 0
  · simp [DOZZ.fieldChaosMass, hν0, ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hp)]
  have : Nonempty S := by
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν0)
    exact ⟨x⟩
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := by
    intro hzero
    exact hν0 (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero)
  apply kahane_field_power_ge_one_nonzero PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ p hp
  · exact hcov
  · simpa [νf, DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hdiag



end DOZZ.Proofs
