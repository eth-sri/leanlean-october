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
section
variable (γ α₁ α₂ α₃ : ℝ)

/-- Off the insertion points, the real fusion kernel is the Coulomb weight. -/
theorem fusion_gammaHalfKernel_weight (z x : ℂ)
    (hxz : x ≠ z) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) =
      coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ x := by
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left ..)
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
  rw [Real.div_rpow hp.le hz.le, Real.div_rpow hp.le h0.le, Real.div_rpow hp.le h1.le]
  have he : γ * (α₁ + α₂ + α₃ - γ / 2) =
      γ * (-γ / 2) + γ * α₁ + γ * α₂ + γ * α₃ := by ring
  rw [he, Real.rpow_add hp, Real.rpow_add hp, Real.rpow_add hp]
  have he' : γ * (-γ / 2) = -(γ ^ 2 / 2) := by ring
  rw [he', Real.rpow_neg hz.le]
  field_simp

/-- The mass in the fusion moment is the integral of the displayed real kernel. -/
theorem fusion_gammaHalfMass_kernel (z : ℂ) (μ : Measure ℂ)
    (hz : μ {z} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ =
      ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
  apply lintegral_congr_ae
  have haz : ∀ᵐ x ∂μ, x ≠ z := by rw [ae_iff]; simpa using hz
  have ha0 : ∀ᵐ x ∂μ, x ≠ 0 := by rw [ae_iff]; simpa using h0
  have ha1 : ∀ᵐ x ∂μ, x ≠ 1 := by rw [ae_iff]; simpa using h1
  filter_upwards [haz, ha0, ha1] with x hxz hx0 hx1
  exact (fusion_gammaHalfKernel_weight γ α₁ α₂ α₃ z x hxz hx0 hx1).symm

/-- The fusion kernel is jointly measurable in the negative insertion and the integration point. -/
theorem fusion_measurable_gammaHalfKernel :
    Measurable (fun q : ℂ × ℂ => gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2) := by
  unfold gammaHalfKernel normPlus
  fun_prop

/-- Away from the limiting root, the moving rooted kernel converges pointwise. -/
theorem fusion_rootedKernel_tendsto (y x : ℂ) (hx : x ≠ 0) :
    Filter.Tendsto (fun z : ℂ => gammaHalfKernel γ α₁ α₂ α₃ z x *
        Real.exp (γ ^ 2 * gffKernel (y * z) x)) (nhds 0)
      (nhds (gammaHalfKernel γ α₁ α₂ α₃ 0 x * Real.exp (γ ^ 2 * gffKernel 0 x))) := by
  have hk : ContinuousAt (fun z => gammaHalfKernel γ α₁ α₂ α₃ z x) 0 := by
    apply ContinuousAt.div_const
    apply ContinuousAt.mul_const
    apply ContinuousAt.rpow_const
    · fun_prop
    simp_all
  have hg : ContinuousAt (fun z => gffKernel (y * z) x) 0 := by
    unfold gffKernel normPlus
    apply ContinuousAt.add
    · apply ContinuousAt.add
      · apply ContinuousAt.neg
        apply ContinuousAt.log
        · fun_prop
        simp_all
      · apply ContinuousAt.log
        · fun_prop
        · simp
    fun_prop
  have hc : ContinuousAt (fun z => Real.exp (γ ^ 2 * gffKernel (y * z) x)) 0 :=
    by fun_prop
  simpa using hk.tendsto.mul hc.tendsto

end

end DOZZ.Proofs
