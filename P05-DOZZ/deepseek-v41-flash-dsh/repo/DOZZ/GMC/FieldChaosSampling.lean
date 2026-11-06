/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.SharedHyp

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

/-- The spatial Wick density is jointly measurable. -/
theorem fieldWickDensity_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (h : S → ℝ≥0) (hh : Measurable h) (γ : ℝ) :
    Measurable (fun p : Ω × S => fieldWickDensity P Φ h γ p.1 p.2) := by
  exact ((measurable_coe_nnreal_real.comp hh).comp measurable_snd).mul
    (Real.measurable_exp.comp ((measurable_const.mul hΦ.1).sub
      (measurable_const.mul
        ((centeredGaussianField_variance_measurable P Φ hΦ).comp measurable_snd))))

/-- Wick normalization gives joint integrability and the exact spatial mean. -/
theorem fieldWickDensity_integrable_mean
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : BoundedWeight h) (γ : ℝ) :
    Integrable (fun p : Ω × S => fieldWickDensity P Φ h γ p.1 p.2)
      (P.prod (ν.normalize : Measure S)) ∧
    (∫ p : Ω × S, fieldWickDensity P Φ h γ p.1 p.2
      ∂(P.prod (ν.normalize : Measure S))) = ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) := by
  have : IsProbabilityMeasure P := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
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

end DOZZ.Proofs
