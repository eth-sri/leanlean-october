/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.ConstantCarrier
public import DOZZ.FourPoint.Reflected.RestartPast
import Mathlib.Tactic
/-! The copied exterior mass is an observable of the stopped inward past and outward half. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Evaluate the inward/outward pair without imposing a matching endpoint on arbitrary inputs. -/
noncomputable def dualPastRadialValue (p : BrownianPath × BrownianPath) (t : ℝ) : ℝ :=
  if 0 ≤ t then p.1 (Real.toNNReal t) else p.2 (Real.toNNReal (-t))



/-- The literal radial Wick factor evaluated on a past pair. -/
noncomputable def dualPastReinsertionWeight (γ : ℝ) (p : BrownianPath × BrownianPath) (x : ℂ) : ℝ :=
  if ‖x‖ = 0 then 0 else Real.exp
    (γ*dualPastRadialValue p (-Real.log ‖x‖)-γ*Q γ*|Real.log ‖x‖|)

/-- The past Wick factor is jointly measurable on arbitrary path pairs. -/
theorem dual_past_reinsertion_weight_measurable γ :
    Measurable (fun p : (BrownianPath × BrownianPath) × ℂ => dualPastReinsertionWeight γ p.1 p.2) := by
  have hl : Measurable (fun p : (BrownianPath × BrownianPath) × ℂ => Real.log ‖p.2‖) := by fun_prop
  exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    measurable_const (Real.measurable_exp.comp ((measurable_const.mul ((show Measurable (fun p : (BrownianPath × BrownianPath) × ℝ => dualPastRadialValue p.1 p.2) by exact Measurable.ite (measurableSet_le measurable_const measurable_snd) (continuous_eval.measurable.comp ((measurable_fst.comp measurable_fst).prodMk (by fun_prop))) (continuous_eval.measurable.comp ((measurable_snd.comp measurable_fst).prodMk (by fun_prop)))).comp (measurable_fst.prodMk hl.neg))).sub
      (measurable_const.mul (continuous_abs.measurable.comp hl))))

/-- Every exterior point beyond the restarted disk uses only the stopped past radial data. -/
theorem dual_past_reinsertion_weight_eq (γ : ℝ) (A : TwoSidedPath) (T : ℝ≥0)
    (x : ℂ) (hx : Real.exp (-(T : ℝ)) ≤ ‖x‖) :
    dualPastReinsertionWeight γ (stopBrownianPath (radialPositiveHalf A) T, radialNegativeHalf A) x =
      reflected_global_reinsertionWeight γ A x := by
  have dual_past_radial_value_eq (t : ℝ) (ht : t ≤ T) : dualPastRadialValue (stopBrownianPath (radialPositiveHalf A) T, radialNegativeHalf A) t = A t := by
    unfold dualPastRadialValue
    by_cases ht0 : 0 ≤ t
    · rw [ite_eq_left ht0]
      simp only [stopBrownianPath, ContinuousMap.coe_mk, min_eq_left ((Real.toNNReal_le_iff_le_coe).mpr ht),
        radialPositiveHalf, ContinuousMap.comp_apply]
      change A (Real.toNNReal t : ℝ) = A t
      rw [Real.coe_toNNReal t ht0]
    · rw [ite_eq_right ht0]
      simp only [radialNegativeHalf, ContinuousMap.comp_apply]
      change A (-(Real.toNNReal (-t) : ℝ)) = A t
      rw [Real.coe_toNNReal (-t) (neg_nonneg.mpr (le_of_not_ge ht0)), neg_neg]
  have ht : -Real.log ‖x‖ ≤ T := by
    have hh := Real.log_le_log (Real.exp_pos _) hx
    rw [Real.log_exp] at hh
    linarith only [hh]
  simp only [dualPastReinsertionWeight, reflected_global_reinsertionWeight,
    ite_eq_right ((Real.exp_pos _).trans_le hx).ne', dual_past_radial_value_eq _ ht]

end DOZZ.Proofs
