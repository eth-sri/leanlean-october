/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ExteriorExpectation
public import DOZZ.FourPoint.Fusion.RootedCoulombComplex

/-! # Splitting the literal signed spatial expectation -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The full spatial expectation is the sum of its local and exterior expectations.
The integrability needed for this signed split follows from rooting and the mass bound. -/
theorem fusion_secondSpatial_expectation_split {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hβ : γ ^ 2 / 2 < γ * α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p univ z =
      fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2)) z +
      fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ z := by
  let I := fun ω => ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ)
  let f := fusionSecondKernel mixed γ α₁ α₂ α₃ z
  simp only [fusionSecondSpatial, Measure.restrict_univ]
  let B := Metric.ball (0 : ℂ) (1 / 2)
  have hf := measurable_fusionSecondKernel_at mixed γ α₁ α₂ α₃ z
  have hβ2 : γ * α₁ < 2 := by
    have h := (lt_div_iff₀ hγ).mp hα₁
    nlinarith
  have hfi := fusion_localSecondKernel_integrable mixed γ α₁ α₂ α₃ (by positivity) hβ hβ2 z hz
  have hzunit := three_roots_in_unit_disk (by linarith : ‖z‖ ≤ 1)
  have hm := fusion_gammaHalfMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz hz4
  obtain ⟨hfLocal, hiLocal, _, _⟩ := fusion_rooted_coulomb_complex_integral P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] ![z, 0, 1] hzunit α₃ (-p - 1) (by linarith)
    (hm.mono fun _ h => h.2.lt_top) (B.indicator f) (hf.indicator Metric.isOpen_ball.measurableSet) hfi
  have hiL : Integrable (fun ω => I ω * (∫ x in B, f x ∂M ω)) P := by
    simpa only [integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)] using hiLocal
  obtain ⟨C, _, hb⟩ := fusion_exterior_expectation_bound mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  have hiR : Integrable (fun ω => I ω * (∫ x in Bᶜ, f x ∂M ω)) P := (hb z hz hz4).1
  have heq : (fun ω => I ω * (∫ x, f x ∂M ω)) =ᵐ[P]
      (fun ω => I ω * (∫ x in B, f x ∂M ω) + I ω * (∫ x in Bᶜ, f x ∂M ω)) := by
    filter_upwards [hfLocal, hm,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hωL hω hωz hω0 hω1
    have hL : IntegrableOn f B (M ω) := (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mp hωL
    have hk : (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω) < ⊤ := by
      rw [← fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z (M ω) hωz hω0 hω1]
      exact hω.2.lt_top
    have hR : IntegrableOn f Bᶜ (M ω) := ⟨(measurable_fusionSecondKernel_at mixed γ α₁ α₂ α₃ z).aestronglyMeasurable,
      (hasFiniteIntegral_iff_norm _).mpr ((fusion_exteriorSecondKernel_lintegral_bound mixed γ α₁ α₂ α₃ z hz4 (M ω)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk))⟩
    have hfull : Integrable f (M ω) := by
      have h := hL.union hR
      simpa only [Set.union_compl_self, integrableOn_univ] using h
    rw [← integral_add_compl (show MeasurableSet B from Metric.isOpen_ball.measurableSet) hfull, mul_add]
  calc
    _ = ∫ ω, (I ω * (∫ x in B, f x ∂M ω) + I ω * (∫ x in Bᶜ, f x ∂M ω)) ∂P := integral_congr_ae heq
    _ = _ := integral_add hiL hiR

end DOZZ.Proofs
