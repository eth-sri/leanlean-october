/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.KernelNorms
public import DOZZ.Hypergeom.Planar.TwoPointRpow

/-! Exact integrability tests for the two differentiated planar kernels. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

/-- Exact integrability criterion for the Wirtinger derivative kernel. -/
theorem integrable_planarWirtingerKernel_iff (k β : ℝ) (hk : 0 < k) (z : ℂ) (hz : z ≠ 0) :
    Integrable (DOZZ.planarWirtingerKernel k β z) volume ↔ k < β ∧ β < 2 := by
  have hmeas : Measurable (DOZZ.planarWirtingerKernel k β z) := by
    change Measurable (fun u : ℂ =>
      ((‖u - z‖ ^ k : ℝ) : ℂ) / ((z - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ)))
    fun_prop
  rw [← integrable_norm_iff hmeas.aestronglyMeasurable, integrable_congr (by
    filter_upwards [Measure.ae_ne volume 0, Measure.ae_ne volume z] with u hu0 huz
    have hnorm0 : 0 ≤ ‖u‖ := norm_nonneg u
    calc
      _ =
          ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β := (norm_planarWirtingerKernel_eq k β z u hu0 huz)
      _ = ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) := by
        rw [div_eq_mul_inv, Real.rpow_neg hnorm0]
        ring)]
  rw [integrableOn_two_point_rpow_iff (-β) (k - 2) z hz] <;> grind

end DOZZ.Proofs
