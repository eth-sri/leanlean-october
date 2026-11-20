/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosConvexOrder
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Positive subunit Kahane comparison for continuum field chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem fieldChaosMass_toReal_subunit_integrable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    Integrable (fun ω => (fieldChaosMass P Φ ν h γ ω).toReal ^ p) P := by
  let := (hΦ.2 0 Fin.elim0).1
  let m := fun ω => (fieldChaosMass P Φ ν h γ ω).toReal
  have hm : Integrable m P := (fieldChaosMass_toReal_integrable_mean P Φ hΦ ν h hh hhb γ).1
  have hf : Measurable (fun x : ℝ => x ^ p) := by fun_prop
  refine (hm.add (integrable_const 1)).mono'
    (hf.comp_aemeasurable hm.aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  rcases le_total (m ω) 1 with hx | hx
  · exact (Real.rpow_le_one ENNReal.toReal_nonneg hx hp.1).trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  · exact (Real.rpow_le_rpow_of_exponent_le hx hp.2).trans (by rw [Real.rpow_one]; exact le_add_of_nonneg_right zero_le_one)

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
  have hX := fieldChaosMass_toReal_subunit_integrable PX Φ hΦ νf h hh hhb γ p ⟨hp.1.le, hp.2.le⟩
  have hY := fieldChaosMass_toReal_subunit_integrable PY Ψ hΨ νf h hh hhb γ p ⟨hp.1.le, hp.2.le⟩
  have hc := kahane_field_test_convex PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ
    (fun x => -(x ^ p)) (by fun_prop) (Real.concaveOn_rpow hp.1.le hp.2.le).neg hcov hd hY.neg
  change (∫⁻ ω, fieldChaosMass PX Φ νf h γ ω ^ p ∂PX) ≥
    ∫⁻ ω, fieldChaosMass PY Ψ νf h γ ω ^ p ∂PY
  rw [← fieldChaosMass_rpow_lintegral PX Φ hΦ νf h hh hhb γ p hp.1.le,
    ← fieldChaosMass_rpow_lintegral PY Ψ hΨ νf h hh hhb γ p hp.1.le,
    ← ofReal_integral_eq_lintegral_ofReal hX (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hY (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by simpa only [integral_neg, neg_le_neg_iff] using hc.2)

end DOZZ.Proofs
