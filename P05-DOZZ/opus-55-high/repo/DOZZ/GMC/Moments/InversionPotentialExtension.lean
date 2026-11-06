/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionMixedPotential

/-! Continuous extension of the inverse point/source-circle potential across zero. -/

@[expose] public section

open MeasureTheory
open DOZZ.Proofs.CirclePotential

namespace DOZZ.Proofs

/-- The inverse circle potential in coordinates that are regular at zero. -/
noncomputable def inversionCirclePotential (y : ℂ) (s : ℝ) (x : ℂ) : ℝ :=
  -Real.log (max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖)) +
    Real.log (normPlus x) + regAvg y s
section
variable (y : ℂ) (s : ℝ)

/-- The clipped argument never vanishes, including at zero. -/
theorem inversionCirclePotential_clip_pos (x : ℂ) :
    0 < max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖) := by
  by_cases hx : x = 0
  · simp_all
  positivity

/-- The inverse point/source-circle potential extends continuously to the whole plane. -/
theorem continuous_inversionCirclePotential :
    Continuous (inversionCirclePotential y s) := by
  have hclip : Continuous (fun x => max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖)) :=
    by fun_prop
  exact ((hclip.log (fun x => (inversionCirclePotential_clip_pos y s x).ne')).neg.add
    continuous_log_normPlus).add continuous_const

/-- Away from zero the continuous extension is the literal inverted circle potential. -/
theorem inversionCirclePotential_eq_innerPot {x : ℂ} (hx : x ≠ 0) :
    inversionCirclePotential y s x = innerPot y s x⁻¹ := by
  have hn := norm_pos_iff.mpr hx
  have hdist : ‖x⁻¹ - y‖ = ‖1 - x * y‖ / ‖x‖ := by
    have hm : x * (x⁻¹ - y) = 1 - x * y := by
      field_simp
    have he := congrArg norm hm
    rw [norm_mul] at he
    grind
  have hmax : max ‖x⁻¹ - y‖ (Real.exp (-s)) =
      max ‖1 - x * y‖ (Real.exp (-s) * ‖x‖) / ‖x‖ := by
    rw [hdist, ← max_div_div_right hn.le, mul_div_cancel_right₀ _ hn.ne']
  have hp : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left ..)
  unfold inversionCirclePotential innerPot
  rw [hmax, Real.log_div (inversionCirclePotential_clip_pos y s x).ne' hn.ne',
    normPlus_inv_identity hx, Real.log_div hp.ne' hn.ne']
  ring

end

end DOZZ.Proofs
