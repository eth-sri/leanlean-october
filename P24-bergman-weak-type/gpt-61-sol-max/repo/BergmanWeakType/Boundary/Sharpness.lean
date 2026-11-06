/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Boundary.CapMass
import Mathlib.Tactic

/-! # The explicit boundary lower bound for the complex weighted projection -/




open MeasureTheory
open scoped Topology

attribute [fun_prop] ENNReal.continuous_ofReal

namespace BergmanWeakType

/-- The boundary concentration lower bound uses ordinary integrable complex inputs. -/
theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) :=
  by
  rcases hα.eq_or_lt with rfl | hα
  · exact le_trans (by norm_num [boundaryConstant]) (one_le_weightedProjection_constant 0 neg_one_lt_zero)
  have hα' := neg_one_lt_zero.trans hα
  have hlim := (tendsto_integral_capProfile hα).const_mul (α + 1)
  rw [← mul_div_assoc, ← div_mul_eq_mul_div] at hlim
  have hlim :=
    ENNReal.tendsto_ofReal
      (hlim.congr'
        (Filter.Eventually.mono (self_mem_nhdsWithin  (s := Set.Ioi 0)) fun R hR ↦
          (weightedArea_boundaryCap_rescaled hα hR).symm))
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with R hR
  change 0 < R at hR
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply le_sInf
  intro C hC
  have hc : ContinuousAt (fun t : ℝ ↦ ENNReal.ofReal ((R + 1 - t) ^ (-(α + 2))) * weightedArea α (boundaryCap R)) 1 :=
    by fun_prop (disch := first | finiteness | (left; continuity))
  have hlim := hc.tendsto.mono_left (show 𝓝[<] 1 ≤ 𝓝 1 from nhdsWithin_le_nhds)
  simp only [add_sub_cancel_right] at hlim
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
  rcases ht with ⟨ht0, ht1⟩
  have ha : (t : ℂ) ∈ disk := by
    simp [abs_of_nonneg ht0.le]
    exact ht1
  apply column_le_weakBound hα' hC ha Set.inter_subset_left
  · intro z hz
    rw [norm_weightedKernel]
    apply
      Real.rpow_le_rpow_of_nonpos
        ((sub_pos.mpr ((mem_disk_iff z).mp hz.1)).trans_le (kernel_denominator_norm_lower z ha)) (by
          have hz1 := ((mem_disk_iff z).mp hz.1).le
          have hzR : ‖1 - z‖ < R := by simpa [dist_eq_norm, norm_sub_rev] using hz.2
          have heq : 1 - z * star (t : ℂ) = 1 - z + (1 - t) * z := by simp_all <;> ring
          rw [heq]
          calc
            _ ≤ ‖1 - z‖ + ‖(1 - t) * z‖ := norm_add_le _ _
            _ = ‖1 - z‖ + (1 - t) * ‖z‖ := by
              rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (sub_pos.mpr ht1)]
            _ ≤ R + 1 - t := by nlinarith
        ) (by linarith)
  · bound

end BergmanWeakType
