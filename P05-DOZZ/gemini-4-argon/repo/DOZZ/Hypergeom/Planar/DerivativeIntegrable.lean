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
theorem integrable_planarWirtingerKernel_iff k β (hk : 0 < k) z (hz : z ≠ 0) :
    Integrable (DOZZ.planarWirtingerKernel k β z) volume ↔ k < β ∧ β < 2 := by
  have hmeas : Measurable (DOZZ.planarWirtingerKernel k β z) := by
    change Measurable (fun u : ℂ =>
      ((‖u - z‖ ^ k : ℝ) : ℂ) / ((z - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ)))
    fun_prop
  rw [← integrable_norm_iff hmeas.aestronglyMeasurable]
  have heq : (fun u => ‖DOZZ.planarWirtingerKernel k β z u‖) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume z] with u hu0 huz
    calc
      ‖DOZZ.planarWirtingerKernel k β z u‖ =
          ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β := (norm_planarWirtingerKernel_eq k β z u hu0 huz)
      _ = ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) := by
        rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg u)]
        ring
  rw [integrable_congr heq, integrableOn_two_point_rpow_iff (-β) (k - 2) z hz]
  constructor
  · rintro ⟨hβ, hk, hsum⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hkb, hβ⟩
    exact ⟨by linarith, by linarith, by linarith⟩

end DOZZ.Proofs
