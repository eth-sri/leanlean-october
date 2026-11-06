/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionFixedCoarse
public import DOZZ.GFFStructure.CircleCovariance

/-! Uniform mixed logarithmic bounds on annular inversion charts. -/

@[expose] public section

open Set Metric Real
open DOZZ.Proofs.CirclePotential

namespace DOZZ.Proofs


/-- Fine target and pulled-source circles obey one common logarithmic covariance estimate
throughout a bounded annulus, including equal centers. -/
theorem inversion_mixed_log_bound_on_annulus
    {x y : ℂ} {m R r s : ℝ} (hm : 0 < m) (hR : 0 ≤ R)
    (hxlo : 2 * m ≤ ‖x‖) (hylo : 2 * m ≤ ‖y‖)
    (hxhi : ‖x‖ ≤ R) (hyhi : ‖y‖ ≤ R)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hε : Real.exp (-r) ≤ min m 1) :
    |circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r)) -
      Real.log (1 / max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))))| ≤
      (2 * (|Real.log m| + Real.log (R + 1)) + 2) +
        (Real.log 3 + 2 * Real.log (1 + R)) := by
  have inversion_log_norm_bound_on_annulus {u : ℂ} (hlo : m ≤ ‖u‖) (hhi : ‖u‖ ≤ R + 1) : |Real.log ‖u‖| ≤ |Real.log m| + Real.log (R + 1) := by
    apply abs_le.mpr
    constructor
    · linarith only [(Real.log_le_log hm hlo), neg_abs_le (Real.log m), (Real.log_nonneg (by linarith only [hR]) : 0 ≤ Real.log (R + 1))]
    · linarith only [(Real.log_le_log (hm.trans_le hlo) hhi), abs_nonneg (Real.log m)]
  apply inversion_circleAverage_mixed_log_bound hR hxhi hyhi hr hs (norm_pos_iff.mp (by linarith only [hm, hylo])) (inversion_log_norm_bound_on_annulus (show m ≤ ‖y‖ by linarith only [hm, hylo]) (hyhi.trans (le_add_of_nonneg_right zero_le_one)))
  intro u hu
  have hux : ‖u - x‖ = Real.exp (-r) := by
    simpa only [mem_sphere_iff_norm] using hu
  have hulo : m ≤ ‖u‖ := by
    have ht := norm_sub_le u (u - x)
    rw [sub_sub_cancel, hux] at ht
    linarith only [ht, hxlo, (hε.trans (min_le_left _ _))]
  have huhi : ‖u‖ ≤ R + 1 := by
    have ht := norm_add_le x (u - x)
    rw [add_sub_cancel, hux] at ht
    linarith only [ht, hxhi, (hε.trans (min_le_right _ _))]
  exact ⟨norm_pos_iff.mp (hm.trans_le hulo),
    inversion_log_norm_bound_on_annulus hulo huhi⟩

/-- The same annular bound controls a fine transformed circle against the source coarse
barrier at the same target center. -/
theorem inversion_mixed_coarse_center_bound_on_annulus
    {x} {m R r s} (hm : 0 < m) (hR : 0 ≤ R)
    (hxlo : 2 * m ≤ ‖x‖) (hxhi : ‖x‖ ≤ R)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hε : Real.exp (-s) ≤ min m 1)
    (hscales : Real.exp (-s) ≤ Real.exp (-r)) :
    |circleAverage (fun u => innerPot x⁻¹ r u⁻¹) x (Real.exp (-s)) - r| ≤
      (2 * (|Real.log m| + Real.log (R + 1)) + 2) +
        (Real.log 3 + 2 * Real.log (1 + R)) := by
  simpa only [sub_self, norm_zero, max_eq_right hscales,
    max_eq_right (Real.exp_pos (-r)).le, (show Real.log (1 / Real.exp (-r)) = r by rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp])] using (inversion_mixed_log_bound_on_annulus hm hR hxlo hxlo hxhi hxhi hs hr hε)

/-- Separated mixed circle covariances approach the invariant point kernel at the sum of
the target and source circle radii. -/
theorem inversion_mixed_offDiagonal_point_error_le
    {x y} {r s} (hy : y ≠ 0)
    (hsmall : Real.exp (-r) < ‖x‖)
    (hsep : Real.exp (-s) * ((‖x‖ + Real.exp (-r)) * ‖y‖) ≤
      ‖x - y‖ - Real.exp (-r))
    (hsepTarget : Real.exp (-r) ≤ ‖x - y‖) :
    |circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r)) - gffKernel x y| ≤
      Real.exp (-s) + Real.exp (-r) := by
  have hpoint : |circleAverage (fun u => gffKernel u y) x (Real.exp (-r)) -
      gffKernel x y| ≤ Real.exp (-r) := by
    have hcircle : circleAverage (fun u => gffKernel u y) x (Real.exp (-r)) =
        gffKernel x y + (regAvg x r - Real.log (normPlus x)) := by
      rw [← integral_circleMeasure_eq_circleAverage (x := x) (r := r)
        (f := fun u => gffKernel u y) (by fun_prop [gffKernel, normPlus])]
      simp_rw [gffKernel_comm]
      rw [CirclePotential.integral_gffKernel_circleMeasure]
      unfold innerPot gffKernel
      rw [norm_sub_rev y x, max_eq_left hsepTarget]
      ring
    rw [hcircle]
    simpa only [add_sub_cancel_left, regAvg] using
      abs_circleAverage_log_normPlus_sub_le x (Real.exp_pos (-r))
  exact (abs_sub_le _ _ _).trans (add_le_add (inversion_circleAverage_mixed_offDiagonal_le hy (Real.exp_pos (-r)) hsmall s hsep) hpoint)

end DOZZ.Proofs
