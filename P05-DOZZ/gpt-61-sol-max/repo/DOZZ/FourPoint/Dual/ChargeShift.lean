/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RootedIdentity
public import DOZZ.FourPoint.Dual.OuterInverseLimit
public import DOZZ.FourPoint.RetainedMass
import Mathlib.Tactic
/-! # Exact circle tilts of the supplied dual retained mass -/
public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The common charge-shift identity at the dual degenerate charge. -/
theorem dual_outerMass_circle_tilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (a m α₁ α₂ α₃ ξ q : ℝ) (hm : 0 ≤ m) (z : ℂ)
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (houtside : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) *
      dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) =
      ∫⁻ ω, dualOuterMass γ (α₁ + a) α₂ α₃ (M ω) z ξ ^ (-q) ∂P := by
  simpa only [retainedCoulombMass, dualOuterMass] using
    retained_coulombMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc (-2 / γ)
      a m α₁ α₂ α₃ ξ q hm z hr houtside

/-- The tilted retained moment converges to the rho with shifted charge, in the full complex
punctured limit. Choosing `a = 2*(Q-alpha1)` gives the reflected leading coefficient. -/
theorem dual_tilted_outer_inverse_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (a α₁ α₂ α₃ ξ q h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ + a - 2 / γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ => ∫⁻ ω,
      ENNReal.ofReal (Real.exp (a * Xc ω 0 (-Real.log ‖z‖ + h) -
        (-Real.log ‖z‖ + h) * a ^ 2 / 2)) *
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (∫⁻ ω, rho γ (M ω) (α₁ + a - 2 / γ) α₂ α₃ ^ (-q) ∂P)) := by
  have ht := dual_outerMass_inverse_moment_tendsto P X hX γ hγ hγ₂ M hM
    (α₁ + a) α₂ α₃ ξ q hξ hξ₁ hq hα₁ hα₂ hα₃
  have hn : Tendsto (fun z : ℂ => ‖z‖)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [hn.eventually (gt_mem_nhds zero_lt_one), self_mem_nhdsWithin] with z hz hz0
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hm : 0 ≤ -Real.log ‖z‖ + h := by
    have hl := Real.log_nonpos hp.le hz.le
    linarith only [hl, hh]
  have hr : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp hz.le
      (by linarith only [hξ] : 1 - ξ ≤ 1)
  have he : Real.exp (-(-Real.log ‖z‖ + h)) ≤ ‖z‖ := by
    have hb : -(-Real.log ‖z‖ + h) ≤ Real.log ‖z‖ := by linarith only [hh]
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hb
  exact (dual_outerMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc
    a (-Real.log ‖z‖ + h) α₁ α₂ α₃ ξ q hm z
    (Real.rpow_pos_of_pos hp _) (he.trans hr)).symm

end DOZZ.Proofs
