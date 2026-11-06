/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.GMC.Moments.InversionLaw
public import DOZZ.GMC.Moments.InfinityChart
public import DOZZ.GMC.Construction.RootedCircleMassLimit
@[expose] public section
open MeasureTheory Set
open scoped Distributions ENNReal
namespace DOZZ.Proofs



/-- The rho mass is a measurable functional of its measure argument. -/
theorem rho_measure_measurable γ α₁ α₂ α₃ :
    Measurable (fun μ : Measure ℂ => rho γ μ α₁ α₂ α₃) := by
  apply Measure.measurable_lintegral
  unfold normPlus
  fun_prop

/-- The GMC inversion law `DOZZ.equatorGFF_GMC_inversion_law` proves the exchange of the first and
third charges. -/
theorem unitVolumeStructureConstant_swap13
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (M : Ω → Measure ℂ) γ α₁ α₂ α₃ (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    unitVolumeStructureConstant P M γ α₁ α₂ α₃ =
      unitVolumeStructureConstant P M γ α₃ α₂ α₁ := by
  have rho_map_inversion (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0) : rho γ (μ.map (fun x => x⁻¹)) α₁ α₂ α₃ = rho γ μ α₃ α₂ α₁ := by
    have rho_inversion_density x (hx0 : x ≠ 0) (hx1 : x ≠ 1) : normPlus x⁻¹ ^ (γ * (α₁ + α₂ + α₃)) / (‖x⁻¹‖ ^ (γ * α₁) * ‖x⁻¹ - 1‖ ^ (γ * α₂)) = normPlus x ^ (γ * (α₃ + α₂ + α₁)) / (‖x‖ ^ (γ * α₃) * ‖x - 1‖ ^ (γ * α₂)) := by
      have h0 := norm_pos_iff.mpr hx0
      have h1 := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
      rw [normPlus_inv_identity hx0, norm_inv, (show ‖x⁻¹ - 1‖ = ‖x - 1‖ / ‖x‖ by rw [inversion_distance hx0, one_mul, norm_sub_rev]), Real.div_rpow (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖) : 0 < normPlus x).le h0.le,
        Real.inv_rpow h0.le, Real.div_rpow h1.le h0.le]
      rw [(show α₃ + α₂ + α₁ = α₁ + α₂ + α₃ by ring), (show γ * (α₁ + α₂ + α₃) = γ * α₁ + γ * α₂ + γ * α₃ by ring), Real.rpow_add h0, Real.rpow_add h0]
      field_simp [(Real.rpow_pos_of_pos h0 (γ * α₁)).ne',
        (Real.rpow_pos_of_pos h0 (γ * α₂)).ne',
        (Real.rpow_pos_of_pos h0 (γ * α₃)).ne',
        (Real.rpow_pos_of_pos h1 (γ * α₂)).ne']
    unfold rho
    rw [lintegral_map (show Measurable (fun x => ENNReal.ofReal (normPlus x ^ (γ * (α₁ + α₂ + α₃)) / (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂)))) by unfold normPlus; fun_prop) measurable_inv]
    apply lintegral_congr_ae
    filter_upwards [(show ∀ᵐ x ∂μ, x ≠ 0 by rw [ae_iff]; simpa only [not_not, ofPred_eq_eq_singleton] using h0), (show ∀ᵐ x ∂μ, x ≠ 1 by rw [ae_iff]; simpa only [not_not, ofPred_eq_eq_singleton] using h1)] with x hx0 hx1
    rw [rho_inversion_density x hx0 hx1]
  have hmass := gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM
  have he : (∫⁻ ω, ENNReal.rpow
      (rho γ ((M ω).map (fun x : ℂ => x⁻¹)) α₁ α₂ α₃) (-sExp γ α₁ α₂ α₃) ∂P) =
      ∫⁻ ω, ENNReal.rpow (rho γ (M ω) α₃ α₂ α₁) (-sExp γ α₁ α₂ α₃) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hmass 0, hmass 1] with ω h0 h1
    rw [rho_map_inversion (M ω) h0 h1]
  unfold unitVolumeStructureConstant
  rw [(show sExp γ α₃ α₂ α₁ = sExp γ α₁ α₂ α₃ by unfold sExp; ring)]
  congr 2
  simpa only [ENNReal.rpow_eq_pow] using (he.symm.trans (equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM (fun μ => ENNReal.rpow (rho γ μ α₁ α₂ α₃) (-sExp γ α₁ α₂ α₃)) (by simpa only [ENNReal.rpow_eq_pow, Function.comp_def] using ENNReal.continuous_rpow_const.measurable.comp (rho_measure_measurable γ α₁ α₂ α₃)))).symm
end DOZZ.Proofs
