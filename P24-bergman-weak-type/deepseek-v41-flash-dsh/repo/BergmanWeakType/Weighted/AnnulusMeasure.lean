/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure

/-! # Exact masses of weighted outer annuli -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

theorem weightedArea_outerAnnulus {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    weightedArea α {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} =
      ENNReal.ofReal ((1 - r ^ 2) ^ (α + 1)) := by
  rw [← weightedArea_norm_gt hα hr hr1]
  apply measure_congr
  filter_upwards [ae_mem_disk_weightedArea α] with z hz
  simp only [(by simpa [disk] using hz : ‖z‖ < 1), and_true]

theorem weightedArea_outerAnnulus_pos {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    0 < weightedArea α {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} := by
  rw [weightedArea_outerAnnulus hα hr hr1]
  apply ENNReal.ofReal_pos.mpr
  exact Real.rpow_pos_of_pos (by nlinarith) _

end BergmanWeakType
