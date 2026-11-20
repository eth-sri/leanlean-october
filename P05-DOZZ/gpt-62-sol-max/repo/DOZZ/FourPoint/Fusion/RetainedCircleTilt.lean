/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedMassLimit
public import DOZZ.FourPoint.Fusion.RetainedInverseMass
public import DOZZ.FourPoint.Reflected.CircleTilt
import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic

/-! Circle tilt of a retained exterior mass, for either choice of moving charge. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Outside the tilting circle, its exponential density is the exact zero-root ratio power. -/
private theorem retained_circle_density_outside (γ a m : ℝ) (x : ℂ)
    (hx : 0 < ‖x‖) (hm : Real.exp (-m) ≤ ‖x‖) :
    Real.exp (γ * a * (Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖))) =
      (normPlus x / ‖x‖) ^ (γ * a) := by
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [max_eq_right hm, Real.rpow_def_of_pos (div_pos hp hx), Real.log_div hp.ne' hx.ne']
  congr 1
  ring

/-- The density changes the first ordinary charge and retains the moving degenerate root. -/
theorem fusion_coulombWeight_charge_shift (γ β a α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hx : x ≠ 0) :
    ENNReal.ofReal ((normPlus x / ‖x‖) ^ (γ * a)) *
      coulombWeight γ ![β, α₁, α₂] ![z, 0, 1] α₃ x =
        coulombWeight γ ![β, α₁ + a, α₂] ![z, 0, 1] α₃ x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd : 0 < normPlus x / ‖x‖ := div_pos hp hn
  simp only [coulombWeight, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, sub_zero]
  rw [coulombWeight_rpow_ofReal hd, coulombWeight_rpow_ofReal hd]
  have he : γ * (α₁ + a) = γ * a + γ * α₁ := by ring
  rw [he, Real.rpow_add hd, ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd _).le]
  ring

/-- Circle tilting of the literal retained mass is exactly the charge shift whenever the
retained region lies outside that circle. No atom assumptions on the underlying measure enter. -/
private theorem fusionOuterMass_circle_density_shift (γ β a m α₁ α₂ α₃ ξ : ℝ)
    (μ : Measure ℂ) (z : ℂ) (hr : 0 < ‖z‖ ^ (1 - ξ))
    (hm : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    fusionOuterMass γ β α₁ α₂ α₃
      (μ.withDensity (fun x : ℂ => ENNReal.ofReal
        (Real.exp (γ * a * (Real.log (normPlus x) -
          Real.log (max (Real.exp (-m)) ‖x‖)))))) z ξ =
      fusionOuterMass γ β (α₁ + a) α₂ α₃ μ z ξ := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hd : Measurable (fun x : ℂ => ENNReal.ofReal
      (Real.exp (γ * a * (Real.log (normPlus x) -
        Real.log (max (Real.exp (-m)) ‖x‖))))) := by
    unfold normPlus
    fun_prop
  unfold fusionOuterMass
  rw [restrict_withDensity hD,
    coulombMass_eq_lintegral_coulombWeight,
    lintegral_withDensity_eq_lintegral_mul _ hd (measurable_coulombWeight _ _ _ _),
    coulombMass_eq_lintegral_coulombWeight]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hD] with x hx
  have hn : 0 < ‖x‖ := hr.trans_le hx
  dsimp only [Pi.mul_apply]
  rw [retained_circle_density_outside γ a m x hn (hm.trans hx)]
  exact fusion_coulombWeight_charge_shift γ β a α₁ α₂ α₃ z x
    (norm_pos_iff.mp hn)



/-- Exact Cameron-Martin identification of the inverse outer moment at arbitrary real circle time. -/
theorem fusionOuterMass_circle_tilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (β a m α₁ α₂ α₃ ξ q : ℝ) (hm : 0 ≤ m) (z : ℂ)
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (houtside : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) *
      fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) =
      ∫⁻ ω, fusionOuterMass γ β (α₁ + a) α₂ α₃ (M ω) z ξ ^ (-q) ∂P := by
  rw [reflected_lintegral_circleTilt P X hX γ hγ hγ₂ M hM Xc hXc a m hm
    (fun μ => fusionOuterMass γ β α₁ α₂ α₃ μ z ξ ^ (-q))
    ((fusionOuterMass_measurable γ β α₁ α₂ α₃ ξ z).pow_const (-q))]
  apply lintegral_congr
  intro ω
  rw [fusionOuterMass_circle_density_shift γ β a m α₁ α₂ α₃ ξ (M ω) z hr houtside]

/-- At a nonzero insertion in the unit disk, the retained region lies outside the
restart circle. The retained radius is itself positive and at most one. -/
theorem retained_circle_window {z : ℂ} {h ξ : ℝ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1)
    (hh : 0 ≤ h) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    let m := -Real.log ‖z‖ + h
    let r := ‖z‖ ^ (1 - ξ)
    0 ≤ m ∧ 0 < r ∧ Real.exp (-m) ≤ r ∧ r ≤ 1 := by
  have hp := norm_pos_iff.mpr hz0
  have hm := Real.log_nonpos hp.le hz
  have hx : Real.exp (-(-Real.log ‖z‖ + h)) ≤ ‖z‖ := by
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr (show -(-Real.log ‖z‖ + h) ≤ Real.log ‖z‖ by linarith)
  have hr : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp hz
      (show 1 - ξ ≤ 1 by linarith)
  exact ⟨by linarith, Real.rpow_pos_of_pos hp _, hx.trans hr, by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hp.le hz (sub_nonneg.mpr hξ1)⟩

/-- The retained exterior inverse moment after the Gaussian circle tilt. -/
theorem fusion_tilted_outer_inverse_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (χ a α₁ α₂ α₃ ξ q h : ℝ) (hγχ : 0 ≤ γ * χ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ + a - χ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ => ∫⁻ ω,
      ENNReal.ofReal (Real.exp (a * Xc ω 0 (-Real.log ‖z‖ + h) -
        (-Real.log ‖z‖ + h) * a ^ 2 / 2)) *
        fusionOuterMass γ (-χ) α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (∫⁻ ω, rho γ (M ω) (α₁ + a - χ) α₂ α₃ ^ (-q) ∂P)) := by
  have ht := fusionOuterMass_inverse_moment_limit P X hX γ hγ hγ₂ M hM
    χ (α₁ + a) α₂ α₃ ξ q hγχ hξ hξ₁ hq hα₁ hα₂ hα₃
  have hn : Tendsto (fun z : ℂ => ‖z‖)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) :=
    (tendsto_norm_zero (E := ℂ)).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [hn.eventually_lt_const zero_lt_one, self_mem_nhdsWithin] with z hz hz0
  obtain ⟨hm, hr, hout, _⟩ := retained_circle_window hz0 hz.le hh hξ.le hξ₁.le
  exact (fusionOuterMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc (-χ)
    a (-Real.log ‖z‖ + h) α₁ α₂ α₃ ξ q hm z hr hout).symm

end DOZZ.Proofs
