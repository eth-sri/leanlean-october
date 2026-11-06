/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CircleTilt
public import DOZZ.FourPoint.Reflected.OuterInverseLimit
public import DOZZ.FourPoint.RootedPairMoments
public import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic
/-! # The literal retained-region charge shift under a circle tilt -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Outside the tilting circle, its exponential density is the exact zero-root ratio power. -/
theorem reflected_circle_density_outside (γ a m : ℝ) x
    (hx : 0 < ‖x‖) (hm : Real.exp (-m) ≤ ‖x‖) :
    Real.exp (γ * a * (Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖))) =
      (normPlus x / ‖x‖) ^ (γ * a) := by
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [max_eq_right hm, Real.rpow_def_of_pos (div_pos hp hx), Real.log_div hp.ne' hx.ne']
  congr 1
  ring

/-- The density changes the first ordinary charge and retains the moving degenerate root. -/
theorem reflected_coulombWeight_charge_shift (γ a α₁ α₂ α₃ : ℝ) z x
    (hx : x ≠ 0) :
    ENNReal.ofReal ((normPlus x / ‖x‖) ^ (γ * a)) *
      coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ x =
        coulombWeight γ ![-γ / 2, α₁ + a, α₂] ![z, 0, 1] α₃ x := by
  have hd : 0 < normPlus x / ‖x‖ := div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (norm_pos_iff.mpr hx)
  simp only [coulombWeight, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, sub_zero]
  rw [coulombWeight_rpow_ofReal hd, coulombWeight_rpow_ofReal hd, (show γ * (α₁ + a) = γ * a + γ * α₁ by ring), Real.rpow_add hd, ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd _).le]
  ring


/-- The retained mass is a measurable functional of the measure, with no spatial clipping. -/
theorem reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z :
    Measurable (fun μ : Measure ℂ => gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ) := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hh := Measure.measurable_lintegral
    ((measurable_coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).indicator hD)
  have he : (fun μ : Measure ℂ => ∫⁻ x,
      D.indicator (coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) x ∂μ) =
      fun μ => gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ := by
    funext μ
    rw [lintegral_indicator hD]
    rfl
  rwa [he] at hh

/-- Exact Cameron-Martin identification of the inverse outer moment at arbitrary real circle time. -/
theorem reflected_outerMass_circle_tilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hXc : IsCircleAverage P X Xc)
    (a m α₁ α₂ α₃ ξ q : ℝ) (hm : 0 ≤ m) z
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (houtside : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) *
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) =
      ∫⁻ ω, gammaHalfOuterMass γ (α₁ + a) α₂ α₃ (M ω) z ξ ^ (-q) ∂P := by
  have reflected_outerMass_circle_density_shift (μ : Measure ℂ) z (hr : 0 < ‖z‖ ^ (1 - ξ)) (hm : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) : gammaHalfOuterMass γ α₁ α₂ α₃ (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * a * (Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖)))))) z ξ = gammaHalfOuterMass γ (α₁ + a) α₂ α₃ μ z ξ := by
    have hD : MeasurableSet ({x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖} : Set ℂ) := (isClosed_le continuous_const continuous_norm).measurableSet
    unfold gammaHalfOuterMass
    rw [restrict_withDensity hD,
      coulombMass_eq_lintegral_coulombWeight,
      lintegral_withDensity_eq_lintegral_mul _ (by unfold normPlus; fun_prop) (measurable_coulombWeight _ _ _ _),
      coulombMass_eq_lintegral_coulombWeight]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hD] with x hx
    have hn := hr.trans_le hx
    dsimp only [Pi.mul_apply]
    rw [reflected_circle_density_outside γ a m x hn (hm.trans hx)]
    exact reflected_coulombWeight_charge_shift γ a α₁ α₂ α₃ z x
      (norm_pos_iff.mp hn)
  rw [reflected_lintegral_circleTilt P X hX γ hγ hγ₂ M hM Xc hXc a m hm
    (fun μ => gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ ^ (-q))
    ((reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).pow_const (-q))]
  apply lintegral_congr
  intro ω
  rw [reflected_outerMass_circle_density_shift (M ω) z hr houtside]

/-- The tilted retained moment converges to the rho with shifted charge, in the full complex
punctured limit. Choosing `a = 2*(Q-alpha1)` gives the reflected leading coefficient. -/
theorem reflected_tilted_outer_inverse_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hXc : IsCircleAverage P X Xc)
    (a α₁ α₂ α₃ ξ q h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ + a - γ / 2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ => ∫⁻ ω,
      ENNReal.ofReal (Real.exp (a * Xc ω 0 (-Real.log ‖z‖ + h) -
        (-Real.log ‖z‖ + h) * a ^ 2 / 2)) *
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (∫⁻ ω, rho γ (M ω) (α₁ + a - γ / 2) α₂ α₃ ^ (-q) ∂P)) := by
  apply (reflected_outerMass_inverse_moment_tendsto P X hX γ hγ hγ₂ M hM (α₁ + a) α₂ α₃ ξ q hξ hξ₁ hq hα₁ hα₂ hα₃).congr'
  filter_upwards [(show Tendsto (fun z : ℂ => ‖z‖) (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) by simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one), self_mem_nhdsWithin] with z hz hz0
  have hp := norm_pos_iff.mpr hz0
  exact (reflected_outerMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc
    a (-Real.log ‖z‖ + h) α₁ α₂ α₃ ξ q (by linarith only [(Real.log_nonpos hp.le hz.le), hh]) z
    (Real.rpow_pos_of_pos hp _) ((show Real.exp (-(-Real.log ‖z‖ + h)) ≤ ‖z‖ by simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr (show -(-Real.log ‖z‖ + h) ≤ Real.log ‖z‖ by linarith only [hh])).trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp hz.le (by linarith only [hξ] : 1 - ξ ≤ 1)))).symm

end DOZZ.Proofs
