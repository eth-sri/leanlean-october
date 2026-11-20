/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosAffineMax
public import DOZZ.GMC.KahaneConvexOrderClosure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Continuum Kahane comparison for general convex tests. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem fieldChaosMass_toReal_pos_ae {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Nonempty S] (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hw : 0 < (∫ x, (h x : ℝ) ∂(ν.normalize : Measure S))) :
    ∀ᵐ ω ∂P, 0 < (fieldChaosMass P Φ ν h γ ω).toReal := by
  filter_upwards [centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    P Φ hΦ ν hν h hh hhb γ hw, centeredGaussianField_fieldChaosMass_ne_top_ae P Φ hΦ ν h hh hhb γ]
    with ω ho ht
  exact ENNReal.toReal_pos ho.ne' ht

section
variable {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S] [Nonempty S]
  (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
  (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
  (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h)
  (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
include hΦ hΨ hν hh hhb

section
variable (F : ℝ → ℝ) (hF : Measurable F)
include hF

/-- Comparison for convex real tests, whenever the expectation on the larger side is finite. -/
theorem kahane_field_test_convex (hconvex : ConvexOn ℝ (Ici 0) F)
    (hcov : ∀ᵐ q ∂(ν : Measure S).prod ν,
      gaussianCovariance PX (fun ω => Φ ω q.1) (fun ω => Φ ω q.2) ≤
        gaussianCovariance PY (fun ω => Ψ ω q.1) (fun ω => Ψ ω q.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      gaussianVariance PX (fun ω => Φ ω x) ≤ gaussianVariance PY (fun ω => Ψ ω x))
    (hy : Integrable (fun ω => F ((fieldChaosMass PY Ψ ν h γ ω).toReal)) PY) :
    Integrable (fun ω => F ((fieldChaosMass PX Φ ν h γ ω).toReal)) PX ∧
      (∫ ω, F ((fieldChaosMass PX Φ ν h γ ω).toReal) ∂PX) ≤
        ∫ ω, F ((fieldChaosMass PY Ψ ν h γ ω).toReal) ∂PY := by
  let := (hΦ.2 0 Fin.elim0).1
  let := (hΨ.2 0 Fin.elim0).1
  by_cases hzero : (∫ x, (h x : ℝ) ∂(ν.normalize : Measure S)) = 0
  · simp only [centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PX Φ ν h hh hhb γ hzero, centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PY Ψ ν h hh hhb γ hzero, ENNReal.toReal_zero, integrable_const, integral_const, probReal_univ,
      one_smul, le_refl, and_self]
  have hw : 0 < (∫ x, (h x : ℝ) ∂(ν.normalize : Measure S)) :=
    lt_of_le_of_ne (integral_nonneg fun _ => NNReal.coe_nonneg _) (Ne.symm hzero)
  have hX := fieldChaosMass_toReal_integrable_mean PX Φ hΦ ν h hh hhb γ
  have hY := fieldChaosMass_toReal_integrable_mean PY Ψ hΨ ν h hh hhb γ
  apply convex_comparison_of_affine_max_order PX PY _ _ hX.1 hY.1
    (fieldChaosMass_toReal_pos_ae PX Φ hΦ ν hν h hh hhb γ hw)
    (fieldChaosMass_toReal_pos_ae PY Ψ hΨ ν hν h hh hhb γ hw)
    (hX.2.trans hY.2.symm) _ F hF hconvex hy
  intro n a b
  have hscale (x : ℝ) : affineMax (fun i => a i * (ν.mass : ℝ)) b x =
      affineMax a b ((ν.mass : ℝ) * x) := by simp only [affineMax, mul_assoc]
  rw [integral_congr_ae ((fieldChaosMass_toReal_ae_eq PX Φ hΦ ν h hh hhb γ).mono fun ω e =>
    congrArg (affineMax a b) e), integral_congr_ae
    ((fieldChaosMass_toReal_ae_eq PY Ψ hΨ ν h hh hhb γ).mono fun ω e => congrArg (affineMax a b) e)]
  simpa only [hscale] using kahane_field_normalized_affine_max PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ
    (fun i => a i * (ν.mass : ℝ)) b hcov hdiag

/-- Nonnegative convex tests satisfy Kahane order also for infinite expectation on the larger side. -/
theorem kahane_field_convex_lintegral (hn : ∀ x, 0 ≤ x → 0 ≤ F x)
    (hconvex : ConvexOn ℝ (Ici 0) F)
    (hcov : ∀ᵐ q ∂(ν : Measure S).prod ν,
      gaussianCovariance PX (fun ω => Φ ω q.1) (fun ω => Φ ω q.2) ≤
        gaussianCovariance PY (fun ω => Ψ ω q.1) (fun ω => Ψ ω q.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      gaussianVariance PX (fun ω => Φ ω x) ≤ gaussianVariance PY (fun ω => Ψ ω x)) :
    (∫⁻ ω, ENNReal.ofReal (F ((fieldChaosMass PX Φ ν h γ ω).toReal)) ∂PX) ≤
      ∫⁻ ω, ENNReal.ofReal (F ((fieldChaosMass PY Ψ ν h γ ω).toReal)) ∂PY := by
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (F ((fieldChaosMass PY Ψ ν h γ ω).toReal)) ∂PY) = ∞
  · simp [htop]
  have hy := ae_of_all PY fun ω => hn (fieldChaosMass PY Ψ ν h γ ω).toReal ENNReal.toReal_nonneg
  have hyint : Integrable (fun ω => F ((fieldChaosMass PY Ψ ν h γ ω).toReal)) PY :=
    ⟨(hF.comp_aemeasurable (fieldChaosMass_toReal_integrable_mean PY Ψ hΨ ν h hh hhb γ).1.aemeasurable).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hy).mpr (lt_top_iff_ne_top.mpr htop)⟩
  have hc := kahane_field_test_convex PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ F hF hconvex hcov hdiag hyint
  rw [← ofReal_integral_eq_lintegral_ofReal hc.1 (ae_of_all _ fun ω => hn _ ENNReal.toReal_nonneg),
    ← ofReal_integral_eq_lintegral_ofReal hyint hy]
  exact ENNReal.ofReal_le_ofReal hc.2

end

end

theorem kahane_field_laplace_of_nonzero_finite_measure_eq
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c)
    (γ s : ℝ) (_hs : 0 ≤ s)
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal)) ∂PX ≤
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal)) ∂PY := by
  apply kahane_field_convex_lintegral PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ (fun x => Real.exp (-s * x))
    (by fun_prop) (fun _ _ => Real.exp_nonneg _) _ hcov hdiag
  simpa [Function.comp_def, LinearMap.mul_apply'] using
    (convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ (-s))).subset (by simp) (convex_Ici 0)

end DOZZ.Proofs
