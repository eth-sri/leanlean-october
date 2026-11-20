/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneSpatialL1
public import DOZZ.GMC.FieldChaosFiniteness

/-! Integrability and sampling of finite-cutoff chaos fields. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def fieldWickDensity {Ω S : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω) (x : S) : ℝ :=
  (h x : ℝ) * Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
    DOZZ.gaussianVariance P (fun ω => Φ ω x))

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- The spatial Wick density is jointly measurable. -/
theorem fieldWickDensity_measurable
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (h : S → ℝ≥0) (hh : Measurable h) (γ : ℝ) :
    Measurable (fun p : Ω × S => fieldWickDensity P Φ h γ p.1 p.2) := ((measurable_coe_nnreal_real.comp hh).comp measurable_snd).mul
    (Real.measurable_exp.comp ((measurable_const.mul hΦ.1).sub
      (measurable_const.mul
        ((centeredGaussianField_variance_measurable P Φ hΦ).comp measurable_snd))))

/-- Wick normalization gives joint integrability and the exact spatial mean. -/
theorem fieldWickDensity_integrable_mean [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    Integrable (fun p : Ω × S => fieldWickDensity P Φ h γ p.1 p.2)
      (P.prod (ν.normalize : Measure S)) ∧
    (∫ p : Ω × S, fieldWickDensity P Φ h γ p.1 p.2
      ∂(P.prod (ν.normalize : Measure S))) = ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) := by
  have  := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  have hpoint (x : S) : Integrable (fun ω => fieldWickDensity P Φ h γ ω x) P ∧
      (∫ ω, fieldWickDensity P Φ h γ ω x ∂P) = (h x : ℝ) := by
    have hw := wick_exponential_integrable_expectation P
      (fun ω (_ : Fin 1) => Φ ω x) (hΦ.2 1 (fun _ => x)) (0 : Fin 1) γ
    constructor
    · exact hw.1.const_mul _
    · change (∫ ω, (h x : ℝ) * Real.exp _ ∂P) = _
      rw [integral_const_mul, hw.2, mul_one]
  have hnorm (x : S) : (∫ ω, ‖fieldWickDensity P Φ h γ ω x‖ ∂P) = (h x : ℝ) := by
    simpa only [fieldWickDensity, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))] using (hpoint x).2
  have hint : Integrable (fun p : Ω × S => fieldWickDensity P Φ h γ p.1 p.2)
      (P.prod (ν.normalize : Measure S)) := by
    apply (integrable_prod_iff' (fieldWickDensity_measurable P Φ hΦ h hh γ).aestronglyMeasurable).2
    constructor
    · exact ae_of_all _ fun x => (hpoint x).1
    · simp_rw [hnorm]
      exact centeredGaussianField_bounded_weight_integrable ν h hh hhb
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  simp_rw [(hpoint _).2]

end


section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
  (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
  (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
  (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
include hΦ hh hhb

/-- The real-valued mass is the normalized spatial integral scaled by the reference mass. -/
theorem fieldChaosMass_toReal_ae_eq :
    (fun ω => (fieldChaosMass P Φ ν h γ ω).toReal) =ᵐ[P]
      fun ω => (ν.mass : ℝ) * ∫ x, fieldWickDensity P Φ h γ ω x ∂(ν.normalize : Measure S) := by
  filter_upwards [centeredGaussianField_ae_integrable_weighted_wick P Φ hΦ ν h hh hhb γ] with ω hω
  rw [fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hω, ENNReal.toReal_ofReal
    (mul_nonneg (NNReal.coe_nonneg _) (integral_nonneg fun _ =>
      mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)))] <;> rfl

/-- Wick normalization makes the first moment independent of the Gaussian field. -/
theorem fieldChaosMass_toReal_integrable_mean :
    Integrable (fun ω => (fieldChaosMass P Φ ν h γ ω).toReal) P ∧
    (∫ ω, (fieldChaosMass P Φ ν h γ ω).toReal ∂P) =
      (ν.mass : ℝ) * ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) := by
  let := (hΦ.2 0 Fin.elim0).1
  have hI := fieldWickDensity_integrable_mean P Φ hΦ ν h hh hhb γ
  have he := fieldChaosMass_toReal_ae_eq P Φ hΦ ν h hh hhb γ
  refine ⟨(hI.1.integral_prod_left.const_mul _).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_const_mul, ← integral_prod _ hI.1, hI.2]

/-- For nonnegative powers, the moment can be taken on either the finite masses or their reals. -/
theorem fieldChaosMass_rpow_lintegral (p : ℝ) (hp : 0 ≤ p) :
    (∫⁻ ω, ENNReal.ofReal ((fieldChaosMass P Φ ν h γ ω).toReal ^ p) ∂P) =
      ∫⁻ ω, fieldChaosMass P Φ ν h γ ω ^ p ∂P := by
  apply lintegral_congr_ae
  filter_upwards [centeredGaussianField_fieldChaosMass_ne_top_ae P Φ hΦ ν h hh hhb γ] with ω hω
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp, ENNReal.ofReal_toReal hω]

end

end DOZZ.Proofs
