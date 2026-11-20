/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ExteriorIntegral
public import DOZZ.FourPoint.Fusion.SpatialFunctions
public import DOZZ.FourPoint.Fusion.MassPositiveFinite
public import DOZZ.FourPoint.TaylorFixedDisk

/-! # Uniform bounds on the signed exterior expectation -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exterior rooted Taylor expectation is uniformly bounded by the preceding inverse moment. -/
theorem fusion_exterior_expectation_bound {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 →
      Integrable (fun ω => ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
        (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
          fusionSecondKernel mixed γ α₁ α₂ α₃ z x ∂M ω)) P ∧
      ‖fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := coulomb_inverse_moment_uniform_roots P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] α₃ p hp
  refine ⟨16 * C, by positivity, ?_⟩
  intro z hz hz4
  let I := fun ω => coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃
  have hIm : AEMeasurable I P := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _
  have hzunit := three_roots_in_unit_disk (by linarith : ‖z‖ ≤ 1)
  have hib : (∫⁻ ω, I ω ^ (-p) ∂P) ≤ ENNReal.ofReal C := hbound _ hzunit
  have hit : (∫⁻ ω, I ω ^ (-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hib
  have hmaj : Integrable (fun ω => 16 * (I ω ^ (-p)).toReal) P :=
    (integrable_toReal_of_lintegral_ne_top (hIm.pow_const _) hit).const_mul 16
  let B := (Metric.ball (0 : ℂ) (1 / 2))ᶜ
  let f := fun x : ℂ => fusionSecondKernel mixed γ α₁ α₂ α₃ z x
  have hf := measurable_fusionSecondKernel_at mixed γ α₁ α₂ α₃ z
  have hsample : AEMeasurable (fun ω => ∫ x in B, f x ∂M ω) P := by
    have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet.compl
    have hfB : Measurable (B.indicator f) := hf.indicator hB
    simp_rw [← integral_indicator hB]
    exact (measurable_integral_of_measurable_measure
      (measurable_id : Measurable (id : Measure ℂ → Measure ℂ)) hfB.stronglyMeasurable).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
  have hF : AEStronglyMeasurable (fun ω => ((I ω ^ (-p - 1)).toReal : ℂ) * (∫ x in B, f x ∂M ω)) P :=
    ((Complex.measurable_ofReal.comp_aemeasurable (hIm.pow_const _).ennreal_toReal).mul hsample).aestronglyMeasurable
  have hdom : ∀ᵐ ω ∂P, ‖((I ω ^ (-p - 1)).toReal : ℂ) * (∫ x in B, f x ∂M ω)‖ ≤
      16 * (I ω ^ (-p)).toReal := by
    filter_upwards [fusion_gammaHalfMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz hz4,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hω hωz hω0 hω1
    simpa only [show -p - 1 + 1 = -p by ring] using
      fusion_exterior_inverse_integral_bound mixed γ α₁ α₂ α₃ (-p - 1) z hz4 (M ω) hω.1 hω.2.lt_top hωz hω0 hω1
  refine ⟨hmaj.mono' hF hdom, ?_⟩
  calc
    _ ≤ ∫ ω, 16 * (I ω ^ (-p)).toReal ∂P := norm_integral_le_of_norm_le hmaj hdom
    _ = 16 * (∫⁻ ω, I ω ^ (-p) ∂P).toReal := by
      rw [integral_const_mul, integral_toReal (hIm.pow_const _) (ae_lt_top' (hIm.pow_const _) hit)]
    _ ≤ 16 * C := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hib).trans_eq (ENNReal.toReal_ofReal hC.le)

end DOZZ.Proofs
