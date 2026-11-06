/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.GMC.Moments.InversionLaw
public import DOZZ.GMC.Moments.InfinityChart
public import DOZZ.GMC.Construction.RootedCircleMassLimit
import DOZZ.ShiftEquations.Mobius.InversionMoment
@[expose] public section
open MeasureTheory Set
open scoped Distributions ENNReal
namespace DOZZ.Proofs
section
variable (γ α₁ α₂ α₃ : ℝ)

/-- The canonical three-root density exchanges zero and infinity under inversion. -/
theorem rho_inversion_density (x : ℂ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    normPlus x⁻¹ ^ (γ * (α₁ + α₂ + α₃)) /
      (‖x⁻¹‖ ^ (γ * α₁) * ‖x⁻¹ - 1‖ ^ (γ * α₂)) =
    normPlus x ^ (γ * (α₃ + α₂ + α₁)) /
      (‖x‖ ^ (γ * α₃) * ‖x - 1‖ ^ (γ * α₂)) := by
  have hn : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)
  have h0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  have hd : ‖x⁻¹ - 1‖ = ‖x - 1‖ / ‖x‖ := by
    rw [inversion_distance hx0, one_mul, norm_sub_rev]
  rw [normPlus_inv_identity hx0, norm_inv, hd, Real.div_rpow hn.le h0.le,
    Real.inv_rpow h0.le, Real.div_rpow h1.le h0.le]
  have hs : γ * (α₁ + α₂ + α₃) = γ * α₁ + γ * α₂ + γ * α₃ := by ring
  have ht : α₃ + α₂ + α₁ = α₁ + α₂ + α₃ := by ring
  rw [ht, hs, Real.rpow_add h0, Real.rpow_add h0]
  field_simp

/-- Canonical mass after pushing a root-atomless measure through inversion. -/
theorem rho_map_inversion (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    rho γ (μ.map (fun x : ℂ => x⁻¹)) α₁ α₂ α₃ = rho γ μ α₃ α₂ α₁ := by
  have hw : Measurable (fun x : ℂ => ENNReal.ofReal
      (normPlus x ^ (γ * (α₁ + α₂ + α₃)) /
        (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂)))) := by
    unfold normPlus
    fun_prop
  unfold rho
  rw [lintegral_map hw measurable_inv]
  have ha0 : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]; simpa using h0
  have ha1 : ∀ᵐ x ∂μ, x ≠ 1 := by
    rw [ae_iff]; simpa using h1
  apply lintegral_congr_ae
  filter_upwards [ha0, ha1] with x hx0 hx1
  rw [rho_inversion_density γ α₁ α₂ α₃ x hx0 hx1]

/-- The rho mass is a measurable functional of its measure argument. -/
theorem rho_measure_measurable :
    Measurable (fun μ : Measure ℂ => rho γ μ α₁ α₂ α₃) := by
  apply Measure.measurable_lintegral
  unfold normPlus
  fun_prop

end

/-- The GMC inversion law `DOZZ.equatorGFF_GMC_inversion_law` proves the exchange of the first and
third charges. -/
theorem unitVolumeStructureConstant_swap13
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    unitVolumeStructureConstant P M γ α₁ α₂ α₃ =
      unitVolumeStructureConstant P M γ α₃ α₂ α₁ := by
  have hs : sExp γ α₃ α₂ α₁ = sExp γ α₁ α₂ α₃ := by unfold sExp; ring
  have hH : Measurable (fun μ : Measure ℂ =>
      ENNReal.rpow (rho γ μ α₁ α₂ α₃) (-sExp γ α₁ α₂ α₃)) := by
    simpa only [ENNReal.rpow_eq_pow, Function.comp_def] using
      ENNReal.continuous_rpow_const.measurable.comp (rho_measure_measurable γ α₁ α₂ α₃)
  have hlaw := equatorGFF_GMC_inversion_law P X hX γ hγ hγ2 M hM
    (fun μ => ENNReal.rpow ..) hH
  have hmass := DOZZ.Proofs.gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM
  have he : (∫⁻ ω, ENNReal.rpow
      (rho γ ((M ω).map (fun x : ℂ => x⁻¹)) α₁ α₂ α₃) (-sExp γ α₁ α₂ α₃) ∂P) =
      ∫⁻ ω, ENNReal.rpow (rho γ (M ω) α₃ α₂ α₁) (-sExp γ α₁ α₂ α₃) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hmass 0, hmass 1] with ω h0 h1
    rw [rho_map_inversion γ α₁ α₂ α₃ (M ω) h0 h1]
  unfold unitVolumeStructureConstant
  simp_all
end DOZZ.Proofs
