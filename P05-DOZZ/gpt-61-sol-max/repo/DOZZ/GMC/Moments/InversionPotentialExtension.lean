/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionMixedPotential
import Mathlib.Tactic

/-! Continuous extension of the inverse point/source-circle potential across zero. -/

@[expose] public section

open MeasureTheory
open DOZZ.Proofs.CirclePotential

namespace DOZZ.Proofs

variable (y : ℂ) (s : ℝ)

include y s in
/-- The inverse circle potential in coordinates that are regular at zero. -/
noncomputable def inversionCirclePotential  (x : ℂ) : ℝ :=
  -Real.log (max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖)) +
    Real.log (normPlus x) + regAvg y s

include y s in
/-- The clipped argument never vanishes, including at zero. -/
theorem inversionCirclePotential_clip_pos  (x : ℂ) :
    0 < max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖) := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hx)).trans_le (le_max_right _ _)

include y s in
/-- The inverse point/source-circle potential extends continuously to the whole plane. -/
theorem continuous_inversionCirclePotential  :
    Continuous (inversionCirclePotential y s) := by
  have hclip : Continuous (fun x : ℂ => max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖)) :=
    (continuous_const.sub (continuous_id.mul continuous_const)).norm.max
      (continuous_const.mul continuous_norm)
  exact ((hclip.log (fun x => (inversionCirclePotential_clip_pos y s x).ne')).neg.add
    continuous_log_normPlus).add continuous_const

include y s in
/-- Away from zero the continuous extension is the literal inverted circle potential. -/
theorem inversionCirclePotential_eq_innerPot  {x : ℂ} (hx : x ≠ 0) :
    inversionCirclePotential y s x = innerPot y s x⁻¹ := by
  have hn  := norm_pos_iff.mpr hx
  have hdist : ‖x⁻¹ - y‖ = ‖1 - x * y‖ / ‖x‖ := by
    have hm : x * (x⁻¹ - y) = 1 - x * y := by
      rw [mul_sub, mul_inv_cancel₀ hx]
    have he := congrArg norm hm
    rw [norm_mul] at he
    grind
  have hmax : max ‖x⁻¹ - y‖ (Real.exp (-s)) =
      max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖) / ‖x‖ := by
    rw [hdist, ← max_div_div_right hn.le, mul_div_cancel_right₀ _ hn.ne']
  have hp : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left _ _)
  unfold inversionCirclePotential innerPot
  rw [hmax, Real.log_div (inversionCirclePotential_clip_pos y s x).ne' hn.ne',
    normPlus_inv_identity hx, Real.log_div hp.ne' hn.ne']
  ring

end DOZZ.Proofs
