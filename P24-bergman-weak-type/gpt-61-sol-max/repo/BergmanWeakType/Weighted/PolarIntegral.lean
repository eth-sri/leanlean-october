/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Measure
import Mathlib.Tactic

variable {α : ℝ}

/-! # Polar integration for normalized weighted disk area -/




open MeasureTheory


namespace BergmanWeakType

noncomputable def radialDensity (α r : ℝ) : ℝ := (α + 1) * (1 - r ^ 2) ^ α

variable {E : Type*} [RCLike E]

theorem weightedDensity_nonneg_ae  (hα : -1 < α) :
    ∀ᵐ z ∂diskArea, 0 ≤ radialDensity α ‖z‖ := by
  unfold radialDensity
  filter_upwards [ae_mem_disk] with z hz
  apply mul_nonneg (by linarith)
  have hz' : ‖z‖ < 1 := by exact?
  bound

theorem integrable_weightedDensity_smul  (hα : -1 < α) {f : ℂ → E}
    (hf : Integrable f (weightedArea α)) :
    Integrable (fun z ↦ (radialDensity α ‖z‖) • f z) diskArea := by
  have hi := (integrable_withDensity_iff_integrable_smul' (by
    fun_prop [radialDensity]
  )
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hf
  apply hi.congr
  filter_upwards [weightedDensity_nonneg_ae hα] with z hz
  simp_all [radialDensity]

theorem integral_weightedArea_eq_diskArea  (hα : -1 < α)
    (f : ℂ → E) :
    ∫ z, f z ∂weightedArea α =
      ∫ z, (radialDensity α ‖z‖) • f z ∂diskArea := by
  rw [weightedArea, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [weightedDensity_nonneg_ae hα] with z hz
  simp_all [radialDensity]

theorem integral_weightedArea_eq_circleAverage  (hα : -1 < α)
    {f : ℂ → E} (hf : Integrable f (weightedArea α)) :
    ∫ z, f z ∂weightedArea α = ∫ r in unitIoo,
      (2 * r * radialDensity α r) • Real.circleAverage f 0 r := by
  rw [integral_weightedArea_eq_diskArea hα,
    integral_diskArea_eq_circleAverage (integrable_weightedDensity_smul hα hf)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  rw [mul_smul (2 * r)]
  congr 1
  rw [← Real.circleAverage_fun_smul]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hz'  := by simpa [abs_of_pos hr.1] using hz
  dsimp only
  rw [hz']

end BergmanWeakType
