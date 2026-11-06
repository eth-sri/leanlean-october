/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosAffineMax
public import DOZZ.GMC.KahaneConvexOrderClosure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! A shared convex-order interface for real finite-cutoff chaos masses. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Finite chaos mass has an integrable real representative. -/
theorem fieldChaosMass_toReal_integrable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    Integrable (fun ω => (DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω).toReal) P := by
  apply (((fieldWickDensity_integrable_mean P Φ hΦ ν h hh hhb γ).1.integral_prod_left).const_mul
    (ν.mass : ℝ)).congr
  filter_upwards [centeredGaussianField_ae_integrable_weighted_wick P Φ hΦ ν h hh hhb γ] with ω hω
  rw [fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hω,
    ENNReal.toReal_ofReal (mul_nonneg (NNReal.coe_nonneg _) (integral_nonneg fun _ =>
      mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)))]
  rfl

/-- Finite field masses and their real representatives have the same nonnegative moments. -/
theorem fieldChaosMass_rpow_toReal_ae
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 0 ≤ p) :
    (fun ω => DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω ^ p) =ᵐ[P]
      (fun ω => ENNReal.ofReal ((DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω).toReal ^ p)) :=
  (centeredGaussianField_fieldChaosMass_ne_top_ae P Φ hΦ ν h hh hhb γ).mono fun ω hω => by
    simpa only [ENNReal.ofReal_toReal hω] using
      ENNReal.ofReal_rpow_of_nonneg (ENNReal.toReal_nonneg (a := DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω)) hp

/-- The finite affine-max comparison extends to every convex test with an integrable
expectation on the covariance-dominating side. -/
theorem kahane_field_convex_real_nonzero
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hcov : ∀ᵐ q ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω q.1) (fun ω => Φ ω q.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω q.1) (fun ω => Ψ ω q.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) 
    (F : ℝ → ℝ) (hF : Measurable F) (hconvex : ConvexOn ℝ (Ici 0) F)
    (hIY : Integrable (fun ω => F (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal) PY) :
    Integrable (fun ω => F (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal) PX ∧
      (∫ ω, F (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal ∂PX) ≤
        ∫ ω, F (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal ∂PY := by
  classical
  let  := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let  := (hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  by_cases hw0 : ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) = 0
  · simp_rw [centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PX Φ ν h hh hhb γ hw0,
      centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral PY Ψ ν h hh hhb γ hw0]
    exact ⟨integrable_const _, by simp⟩
  have hwpos  :=
    lt_of_le_of_ne (integral_nonneg fun _ => NNReal.coe_nonneg _) (Ne.symm hw0)
  let c : ℝ := ν.mass
  let mX : ΩX → ℝ := fun ω => c * ∫ x, fieldWickDensity PX Φ h γ ω x
    ∂(ν.normalize : Measure S)
  let mY : ΩY → ℝ := fun ω => c * ∫ x, fieldWickDensity PY Ψ h γ ω x
    ∂(ν.normalize : Measure S)
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have hmX := ((fieldWickDensity_integrable_mean PX Φ hΦ ν h hh hhb γ).1.integral_prod_left).const_mul c
  have hmY := ((fieldWickDensity_integrable_mean PY Ψ hΨ ν h hh hhb γ).1.integral_prod_left).const_mul c
  have hmX0 (ω : ΩX) : 0 ≤ mX ω :=
    mul_nonneg hc (integral_nonneg fun _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
  have hmY0 (ω : ΩY) : 0 ≤ mY ω :=
    mul_nonneg hc (integral_nonneg fun _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
  have hrepX : ∀ᵐ ω ∂PX, DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω = ENNReal.ofReal (mX ω) := by
    filter_upwards [centeredGaussianField_ae_integrable_weighted_wick PX Φ hΦ ν h hh hhb γ] with ω hω
    exact fieldChaosMass_eq_ofReal_normalized_integral PX Φ ν h γ ω hω
  have hrepY : ∀ᵐ ω ∂PY, DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω = ENNReal.ofReal (mY ω) := by
    filter_upwards [centeredGaussianField_ae_integrable_weighted_wick PY Ψ hΨ ν h hh hhb γ] with ω hω
    exact fieldChaosMass_eq_ofReal_normalized_integral PY Ψ ν h γ ω hω
  have hposX : ∀ᵐ ω ∂PX, 0 < mX ω := by
    filter_upwards [hrepX, centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
      PX Φ hΦ ν hν h hh hhb γ hwpos] with ω hω hpω
    simp_all
  have hposY : ∀ᵐ ω ∂PY, 0 < mY ω := by
    filter_upwards [hrepY, centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
      PY Ψ hΨ ν hν h hh hhb γ hwpos] with ω hω hpω
    simp_all
  have hmean : (∫ ω, mX ω ∂PX) = ∫ ω, mY ω ∂PY := by
    dsimp [mX, mY]
    rw [integral_const_mul, integral_const_mul,
      ← integral_prod _ (fieldWickDensity_integrable_mean PX Φ hΦ ν h hh hhb γ).1,
      ← integral_prod _ (fieldWickDensity_integrable_mean PY Ψ hΨ ν h hh hhb γ).1,
      (fieldWickDensity_integrable_mean PX Φ hΦ ν h hh hhb γ).2,
      (fieldWickDensity_integrable_mean PY Ψ hΨ ν h hh hhb γ).2]
  have horder (n : ℕ) (a b : Fin (n + 1) → ℝ) :
      (∫ ω, affineMax a b (mX ω) ∂PX) ≤ ∫ ω, affineMax a b (mY ω) ∂PY := by
    have hscale (x : ℝ) : affineMax (fun i => a i * c) b x = affineMax a b (c * x) := by
      unfold affineMax
      congr 1
      funext i
      ring
    have hcmp := kahane_field_normalized_affine_max PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ
      (fun i => a i * c) b hcov hdiag
    simpa only [hscale] using hcmp
  have hFX : (fun ω => F (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal) =ᵐ[PX]
      (fun ω => F (mX ω)) := hrepX.mono fun ω hω =>
    congrArg F (by rw [hω, ENNReal.toReal_ofReal (hmX0 ω)])
  have hFY : (fun ω => F (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal) =ᵐ[PY]
      (fun ω => F (mY ω)) := hrepY.mono fun ω hω =>
    congrArg F (by rw [hω, ENNReal.toReal_ofReal (hmY0 ω)])
  obtain ⟨hi, hle⟩ := convex_comparison_of_affine_max_order PX PY mX mY hmX hmY hposX hposY
    hmean horder F hF hconvex (hIY.congr hFY)
  exact ⟨hi.congr hFX.symm, by simpa only [integral_congr_ae hFX, integral_congr_ae hFY] using hle⟩

end DOZZ.Proofs
