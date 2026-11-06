/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfKernel
public import DOZZ.GMC.SharpMoments.SeibergWeight
import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # The real fusion kernel and the Coulomb mass -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs


/-- The mass in the fusion moment is the integral of the displayed real kernel. -/
theorem fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z (μ : Measure ℂ)
    (hz : μ {z} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ =
      ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
  have fusion_gammaHalfKernel_weight x (hxz : x ≠ z) (hx0 : x ≠ 0) (hx1 : x ≠ 1) : ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) = coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ x := by
    have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have h0 := norm_pos_iff.mpr hx0
    have h1 := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
    have hz := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    simp only [coulombWeight, Fin.prod_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, sub_zero]
    rw [coulombWeight_rpow_ofReal (div_pos hp hz),
      coulombWeight_rpow_ofReal (div_pos hp h0),
      coulombWeight_rpow_ofReal (div_pos hp h1), coulombWeight_rpow_ofReal hp]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hp h0).le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hp hz).le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (div_pos hp hz).le _)
        (mul_nonneg (Real.rpow_nonneg (div_pos hp h0).le _)
          (Real.rpow_nonneg (div_pos hp h1).le _)))]
    congr 1
    unfold gammaHalfKernel
    rw [Real.div_rpow hp.le hz.le, Real.div_rpow hp.le h0.le, Real.div_rpow hp.le h1.le, (show γ * (α₁ + α₂ + α₃ - γ / 2) = γ * (-γ / 2) + γ * α₁ + γ * α₂ + γ * α₃ by ring), Real.rpow_add hp, Real.rpow_add hp, Real.rpow_add hp, (show γ * (-γ / 2) = -(γ ^ 2 / 2) by ring), Real.rpow_neg hz.le]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rw [coulombMass_eq_lintegral_coulombWeight]
  apply lintegral_congr_ae
  filter_upwards [(show ∀ᵐ x ∂μ, x ≠ z by rw [ae_iff]; simpa using hz), (show ∀ᵐ x ∂μ, x ≠ (0 : ℂ) by rw [ae_iff]; simpa using h0), (show ∀ᵐ x ∂μ, x ≠ (1 : ℂ) by rw [ae_iff]; simpa using h1)] with x hxz hx0 hx1
  exact (fusion_gammaHalfKernel_weight x hxz hx0 hx1).symm

/-- The fusion kernel is jointly measurable in the negative insertion and the integration point. -/
theorem fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃ :
    Measurable (fun q : ℂ × ℂ => gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2) := by
  unfold gammaHalfKernel normPlus
  fun_prop

/-- Away from the limiting root, the moving rooted kernel converges pointwise. -/
theorem fusion_rootedKernel_tendsto γ α₁ α₂ α₃ y x (hx : x ≠ 0) :
    Filter.Tendsto (fun z : ℂ => gammaHalfKernel γ α₁ α₂ α₃ z x *
        Real.exp (γ ^ 2 * gffKernel (y * z) x)) (nhds 0)
      (nhds (gammaHalfKernel γ α₁ α₂ α₃ 0 x * Real.exp (γ ^ 2 * gffKernel 0 x))) := by
  have hk : ContinuousAt (fun z => gammaHalfKernel γ α₁ α₂ α₃ z x) 0 := by
    unfold gammaHalfKernel
    apply ContinuousAt.div_const
    apply ContinuousAt.mul_const
    apply ContinuousAt.rpow_const
    · fun_prop
    · left
      simpa only [sub_zero] using norm_ne_zero_iff.mpr hx
  have hg : ContinuousAt (fun z => gffKernel (y * z) x) 0 := by
    unfold gffKernel normPlus
    apply ContinuousAt.add
    · apply ContinuousAt.add
      · apply ContinuousAt.neg
        apply ContinuousAt.log
        · fun_prop
        · simpa only [mul_zero, zero_sub, norm_neg] using norm_ne_zero_iff.mpr hx
      · apply ContinuousAt.log
        · fun_prop
        · simp
    · exact continuousAt_const
  have hc : ContinuousAt (fun z => Real.exp (γ ^ 2 * gffKernel (y * z) x)) 0 :=
    Real.continuous_exp.continuousAt.comp
      ((continuousAt_const : ContinuousAt (fun _ : ℂ => γ ^ 2) 0).mul hg)
  simpa only [Pi.mul_apply, mul_zero] using hk.tendsto.mul hc.tendsto

end DOZZ.Proofs
