/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.OuterMassLimit
public import DOZZ.Statements.GMC.EquatorGFFGMCIntensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-! Removing the deterministic circle boundary from the literal retained region. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- Every fixed circle has zero mass for the supplied equator chaos almost surely. -/
theorem reflected_gmc_sphere_null
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) c r :
    ∀ᵐ ω ∂P, M ω (Metric.sphere c r) = 0 := by
  have hint := equatorGFF_GMC_intensity P X hX γ hγ hγ₂ M hM
    (Metric.sphere c r) Metric.isClosed_sphere.measurableSet
  rw [(show gmcReferenceMeasure (Metric.sphere c r) = 0 by unfold gmcReferenceMeasure; exact withDensity_absolutelyContinuous _ _ (MeasureTheory.Measure.addHaar_sphere volume c r))] at hint
  exact (lintegral_eq_zero_iff'
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ₂ M hM
      (Metric.sphere c r) Metric.isClosed_sphere.measurableSet)).mp hint

/-- Closed and open exteriors agree for every nonnegative weight when the circle is null. -/
theorem reflected_exterior_integral_open (μ : Measure ℂ) r
    (hcircle : μ (Metric.sphere (0 : ℂ) r) = 0) (f : ℂ → ℝ≥0∞) :
    (∫⁻ x in {x : ℂ | r ≤ ‖x‖}, f x ∂μ) =
      ∫⁻ x in {x : ℂ | r < ‖x‖}, f x ∂μ := by
  rw [Measure.restrict_congr_set (show ({x : ℂ | r ≤ ‖x‖} : Set ℂ) =ᵐ[μ] {x : ℂ | r < ‖x‖} by filter_upwards [(by exact measure_eq_zero_iff_ae_notMem.mp hcircle)] with x hx; exact propext ⟨fun h => lt_of_le_of_ne h (show ‖x‖ ≠ r by simpa only [Metric.mem_sphere, dist_zero_right] using hx).symm, fun h => h.le⟩)]


/-- Removing the fixed root at one gives the open region used by lateral comparison. -/
theorem reflected_open_exterior_remove_roots (μ : Measure ℂ) r (hr : 0 < r)
    (h1 : μ {1} = 0) (f : ℂ → ℝ≥0∞) :
    (∫⁻ x in {x : ℂ | r < ‖x‖}, f x ∂μ) =
      ∫⁻ x in {x : ℂ | r < ‖x‖} ∩ ({0, 1} : Set ℂ)ᶜ, f x ∂μ := by
  have he : ({x : ℂ | r < ‖x‖} : Set ℂ) =ᵐ[μ]
      {x : ℂ | r < ‖x‖} ∩ ({0, 1} : Set ℂ)ᶜ := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp h1)] with x hx
    apply propext
    constructor
    · intro h
      exact ⟨h, by simp [(show x ≠ 0 by intro hh; simp only [hh, norm_zero, not_lt_of_ge hr.le] at h), (by simpa only [mem_singleton_iff] using hx)]⟩
    · exact fun h => h.1
  rw [Measure.restrict_congr_set he]


/-- The supplied ordinary GMC has precisely the open retained mass almost surely. -/
theorem reflected_source_outerMass_eq_comparison_region
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α₁ α₂ α₃ ξ z (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) :
    ∀ᵐ ω ∂P, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) < ‖x‖} ∩ ({0, 1} : Set ℂ)ᶜ,
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω := by
  have reflected_outerMass_eq_comparison_region (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0) (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) (hs : μ (Metric.sphere (0 : ℂ) (‖z‖ ^ (1 - ξ))) = 0) : gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ = ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) < ‖x‖} ∩ ({0, 1} : Set ℂ)ᶜ, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
    rw [(show gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ = ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) < ‖x‖}, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ by rw [reflected_outerMass_eq_kernel_integral γ α₁ α₂ α₃ ξ z μ h0 h1 hz]; exact reflected_exterior_integral_open μ _ hs _)]
    exact reflected_open_exterior_remove_roots μ _ ((norm_nonneg z).trans_lt hz) h1 _
  filter_upwards [reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 0 0,
    reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 1 0,
    reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 0 (‖z‖ ^ (1 - ξ))]
      with ω h0 h1 hs
  simp only [Metric.sphere_zero] at h0 h1
  exact reflected_outerMass_eq_comparison_region (M ω) h0 h1 hz hs

end DOZZ.Proofs
