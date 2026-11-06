/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Kernel
public import DOZZ.FourPoint.Reflected.MassFiniteness
import DOZZ.FourPoint.RootedPairMoments
import Mathlib.Tactic

/-! # Convergence of the literal dual retained mass

The source exterior mass converges to rho with first charge α₁−2/γ.
Root atomlessness and subcritical moment finiteness refer to the supplied GMC.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The actual dual Coulomb mass restricted outside the moving fusion disk. -/
noncomputable def dualOuterMass (γ α₁ α₂ α₃ : ℝ) (μ : Measure ℂ) (z : ℂ) (ξ : ℝ) : ℝ≥0∞ :=
  coulombMass γ (μ.restrict {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖})
    ![-2 / γ, α₁, α₂] ![z, 0, 1] α₃

/-- The zero-kernel integral is the literal rho with effective charge `α₁-γ/2`. -/
theorem dual_zero_kernel_integral_eq_rho γ α₁ α₂ α₃ (hγ : γ ≠ 0) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂μ) =
      rho γ μ (α₁ - 2 / γ) α₂ α₃ := by
  unfold rho
  apply lintegral_congr_ae
  filter_upwards [(show ∀ᵐ x ∂μ, x ≠ 0 by rw [ae_iff]; simpa only [not_not, Set.ofPred_eq_eq_singleton] using h0), (show ∀ᵐ x ∂μ, x ≠ 1 by rw [ae_iff]; simpa only [not_not, Set.ofPred_eq_eq_singleton] using h1)] with x hx0 hx1
  exact congrArg ENNReal.ofReal (dual_zero_kernel_weight γ α₁ α₂ α₃ hγ x hx0 hx1)

/-- The moving root is absent from the retained region, so no atom assumption at `z` is needed. -/
theorem dual_outerMass_eq_kernel_integral γ α₁ α₂ α₃ ξ (hγ : γ ≠ 0) z
    (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) :
    dualOuterMass γ α₁ α₂ α₃ μ z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hzD : z ∉ D := not_le.mpr hz
  unfold dualOuterMass
  exact (dual_kernel_integral_eq_coulombMass γ α₁ α₂ α₃ hγ z (μ.restrict D) (show (μ.restrict D) {z} = 0 by rw [Measure.restrict_apply (measurableSet_singleton z), singleton_inter_of_notMem hzD, measure_empty]) (by apply le_zero_iff.mp; rw [Measure.restrict_apply (measurableSet_singleton 0)]; exact (measure_mono inter_subset_left).trans_eq h0) (by apply le_zero_iff.mp; rw [Measure.restrict_apply (measurableSet_singleton 1)]; exact (measure_mono inter_subset_left).trans_eq h1)).symm


/-- Almost-sure convergence of the actual retained GMC mass in the reflected chart. -/
theorem dual_outerMass_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X) γ
    (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α₁ α₂ α₃ ξ (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (hα₁ : α₁ - 2 / γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, Tendsto (fun z : ℂ => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (rho γ (M ω) (α₁ - 2 / γ) α₂ α₃)) := by
  have dual_outerMass_tendsto (hγ : γ ≠ 0) (μ : Measure ℂ) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (h0 : μ {0} = 0) (h1 : μ {1} = 0) (hfin : rho γ μ (α₁ - 2 / γ) α₂ α₃ ≠ ⊤) : Tendsto (fun z : ℂ => dualOuterMass γ α₁ α₂ α₃ μ z ξ) (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds (rho γ μ (α₁ - 2 / γ) α₂ α₃)) := by
    have heq := dual_zero_kernel_integral_eq_rho γ α₁ α₂ α₃ hγ μ h0 h1
    have ht := dual_outer_kernel_integral_tendsto γ α₁ α₂ α₃ ξ hγ μ hξ hξ₁ h0
      (by rw [heq]; exact hfin)
    rw [heq] at ht
    apply ht.congr'
    filter_upwards [(show Tendsto (fun z : ℂ => ‖z‖) (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) by simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one), self_mem_nhdsWithin] with z hz hz0
    exact (dual_outerMass_eq_kernel_integral γ α₁ α₂ α₃ ξ hγ z μ h0 h1 (by simpa only [Real.rpow_one] using (Real.rpow_lt_rpow_of_exponent_gt (norm_pos_iff.mpr hz0) hz (by linarith only [hξ] : 1 - ξ < 1)))).symm
  filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1,
    reflected_rho_ae_finite P X hX γ hγ hγ₂ M hM (α₁ - 2 / γ) α₂ α₃
      hα₁ hα₂ hα₃] with ω h0 h1 hf
  exact dual_outerMass_tendsto hγ.ne' (M ω) hξ hξ₁ h0 h1 hf.ne



end DOZZ.Proofs
