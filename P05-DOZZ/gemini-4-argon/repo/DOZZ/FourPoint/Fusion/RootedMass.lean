/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootedMass
public import DOZZ.GMC.SharpMoments.SeibergWeight
import DOZZ.GMC.Construction.RootedMeasureKernel
import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # The charge shift in the fusion coefficient -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs




/-- The rooted mass used in fusion has the shifted-charge interpretation almost surely. -/
theorem fusion_gammaHalfRootedMass_eq_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) α₁ α₂ α₃ :
    ∀ᵐ ω ∂P, gammaHalfRootedMass γ α₁ α₂ α₃ M ω =
      coulombMass γ (M ω) ![α₁ + γ / 2, α₂] ![0, 1] α₃ := by
  have fusion_rootedMass_charge_shift (μ : Measure ℂ) (hμ : μ {0} = 0) : coulombMass γ (gmcRootedMeasure γ 0 μ) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ = coulombMass γ μ ![α₁ + γ / 2, α₂] ![0, 1] α₃ := by
    have fusion_coulombWeight_root_zero {x} (hx : x ≠ 0) : ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel 0 x)) * coulombWeight γ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ x = coulombWeight γ ![α₁ + γ / 2, α₂] ![0, 1] α₃ x := by
      have fusion_rootDensity_zero : Real.exp (γ ^ 2 * gffKernel 0 x) = (normPlus x / ‖x‖) ^ (γ ^ 2) := by
        have hn := norm_pos_iff.mpr hx
        have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        rw [Real.rpow_def_of_pos (div_pos hp hn), Real.log_div hp.ne' hn.ne']
        simp only [gffKernel, zero_sub, norm_neg, normPlus, norm_zero, max_eq_left zero_le_one,
          Real.log_one, add_zero]
        congr 1
        ring
      have hd : 0 < normPlus x / ‖x‖ := div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (norm_pos_iff.mpr hx)
      rw [fusion_rootDensity_zero]
      simp only [coulombWeight, Fin.prod_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, sub_zero]
      rw [coulombWeight_rpow_ofReal hd, coulombWeight_rpow_ofReal hd,
        coulombWeight_rpow_ofReal hd]
      rw [← mul_assoc, ← mul_assoc, coulombWeight_ofReal_rpow_mul hd,
        ← mul_assoc, coulombWeight_ofReal_rpow_mul hd]
      rw [(show γ ^ 2 + γ * (-γ / 2) + γ * α₁ = γ * (α₁ + γ / 2) by ring)]
    rw [coulombMass_eq_lintegral_coulombWeight, gmcRootedMeasure,
      lintegral_withDensity_eq_lintegral_mul μ (by exact ENNReal.measurable_ofReal.comp ((measurable_const.mul (measurable_pointRootPotential.comp (measurable_const.prodMk measurable_id))).exp)) (measurable_coulombWeight _ _ _ _),
      coulombMass_eq_lintegral_coulombWeight]
    apply lintegral_congr_ae
    have hx : ∀ᵐ x ∂μ, x ≠ (0 : ℂ) := by
      rw [ae_iff]
      simpa using hμ
    filter_upwards [hx] with x hx
    exact fusion_coulombWeight_root_zero hx
  filter_upwards [gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0] with ω hω
  exact fusion_rootedMass_charge_shift (M ω) hω

end DOZZ.Proofs
