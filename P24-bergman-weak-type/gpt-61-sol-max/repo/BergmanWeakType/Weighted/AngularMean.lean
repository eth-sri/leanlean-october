/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.CompactIntegral
import BergmanWeakType.Definitions
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Tactic

variable {r : ℝ}

/-! # Differentiation of angular means and radial divergence -/



noncomputable section

open MeasureTheory Set Real


namespace BergmanWeakType.Weighted

abbrev PolarField := ℝ → ℝ → ℝ
local notation "PolarContinuous" F:max =>
  ContinuousOn (Function.uncurry F) (SProd.sprod unitIco univ)

variable {F Fr : PolarField}

def angularMean (F : PolarField) (r : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, F r θ

theorem continuousOn_angularMean {S : Set ℝ} (hF : ContinuousOn (Function.uncurry F) (S ×ˢ univ)) :
    ContinuousOn (angularMean F) S :=
  by
  rw [continuousOn_iff_continuous_domRestrict]
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hF.comp_continuous (continuous_subtype_val.prodMap continuous_id) (by simp)

theorem hasDerivAt_angularMean (hr : r ∈ unitIoo) (hF : PolarContinuous F)
    (hFr : PolarContinuous Fr)
    (hd : ∀ r ∈ unitIoo, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr r θ) r) :
    HasDerivAt (angularMean F) (angularMean Fr r) r :=
  by
  unfold angularMean
  simpa [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le two_pi_pos.le] using
    (hasDerivAt_integral_mul_of_continuousOn_nhds (μ := volume.restrict (Icc (0 : ℝ) (2 * π))) isCompact_Icc
      (ae_restrict_mem measurableSet_Icc) (Ioo_mem_nhds hr.1 hr.2) (integrable_const (1 : ℝ))
      (hF.mono (prod_mono Ioo_subset_Ico_self (subset_univ _)))
      (hFr.mono (prod_mono Ioo_subset_Ico_self (subset_univ _))) fun θ _ u hu ↦ hd u hu θ).const_mul _

def intervalIntegrable_polar_slice (hF : PolarContinuous F) (hr : r ∈ unitIco) :=
  (continuousOn_univ.mp (hF.uncurry_left r hr)).intervalIntegrable (μ := volume) 0 (2 * π)

/-- Joint continuity, two polar derivatives, and angular periodicity on the unit disk. -/
structure PolarRegularity (F Fr Frr Ft Ftt : PolarField) : Prop where
  hF : PolarContinuous F
  hFr : PolarContinuous Fr
  hFrr : PolarContinuous Frr
  hFt : PolarContinuous Ft
  hFtt : PolarContinuous Ftt
  hFd : ∀ r ∈ unitIoo, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr r θ) r
  hFrd : ∀ r ∈ unitIoo, ∀ θ, HasDerivAt (fun r ↦ Fr r θ) (Frr r θ) r
  hFdt : ∀ r ∈ unitIoo, ∀ θ, HasDerivAt (F r) (Ft r θ) θ
  hFtd : ∀ r ∈ unitIoo, ∀ θ, HasDerivAt (Ft r) (Ftt r θ) θ
  hperiodFt : ∀ r ∈ unitIoo, Ft r (2 * π) = Ft r 0

/-- A polar divergence inequality with periodic angular derivative makes the angular mean
nonincreasing, including at the origin. -/
theorem antitoneOn_angularMean_of_polar_flux {Frr Ft Ftt : PolarField} {w w' : ℝ → ℝ}
    (h : PolarRegularity F Fr Frr Ft Ftt) (hw : ContinuousOn w unitIco) (hwd : ∀ r ∈ unitIoo, HasDerivAt w (w' r) r)
    (hwpos : ∀ r ∈ unitIoo, 0 < w r)
    (hineq : ∀ r ∈ unitIoo, ∀ θ, r * w r * Frr r θ + (w r + r * w' r) * Fr r θ + w r / r * Ftt r θ ≤ 0) :
    AntitoneOn (angularMean F) unitIco :=
  by
  rcases h with ⟨hF, hFr, hFrr, _, hFtt, hFd, hFrd, _, hFtd, hperiod⟩
  have hflux : AntitoneOn (fun r ↦ r * w r * angularMean Fr r) unitIco :=
    by
    apply
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1)
        ((continuousOn_id.mul hw).mul (continuousOn_angularMean hFr))
    · intro r hr
      have hr  := by simpa using hr
      exact (((hasDerivAt_id r).mul (hwd r hr)).mul (hasDerivAt_angularMean hr hFr hFrr hFrd)).hasDerivWithinAt
    · intro r hr
      have hr  := by simpa using hr
      have hr'  := (Ioo_subset_Ico_self hr)
      have hir := intervalIntegrable_polar_slice hFr hr'
      have hirr := intervalIntegrable_polar_slice hFrr hr'
      have hitt := intervalIntegrable_polar_slice hFtt hr'
      have hz := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hFtd r hr θ) hitt
      rw [hperiod r hr, sub_self] at hz
      have hn := integral_nonpos (μ := volume.restrict (Ioc 0 (2 * π))) (hineq r hr)
      rw [← intervalIntegral.integral_of_le two_pi_pos.le] at hn
      simp (disch := apply_rules [IntervalIntegrable.add, IntervalIntegrable.const_mul]) only
        [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, hz, mul_zero, add_zero] at hn
      have hm := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr two_pi_pos.le) hn
      dsimp [angularMean]
      nlinarith
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) (continuousOn_angularMean hF)
  · intro r hr
    exact (hasDerivAt_angularMean (by simpa using hr) hF hFr hFd).hasDerivWithinAt
  · intro r hr
    have hr  := by simpa using hr
    have hle := hflux (show (0 : ℝ) ∈ unitIco by simp) (Ioo_subset_Ico_self hr) hr.1.le
    simp at hle
    exact nonpos_of_mul_nonpos_right hle (mul_pos hr.1 (hwpos r hr))

end BergmanWeakType.Weighted
