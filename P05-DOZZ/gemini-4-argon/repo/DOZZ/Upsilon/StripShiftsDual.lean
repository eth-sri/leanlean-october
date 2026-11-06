/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.StripShifts
public import DOZZ.Upsilon.IntegralBounds
public import DOZZ.Upsilon.IntegralHolomorphy
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Dual strip shift from the parameter symmetry of the defining integral
-/

@[expose] public section

open Complex MeasureTheory Set

namespace DOZZ.Proofs







/-- The second strip shift, obtained by exchanging the two hyperbolic factors in the
defining integral and applying the first shift at parameter `4 / γ`. -/
theorem exp_upsilonLog_shift_binv {γ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {z : ℂ} (hz0 : 0 < z.re) (hzγ : z.re < γ / 2) :
    Complex.exp (upsilonLog γ (z + 2 / γ)) =
      lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) *
        Complex.exp (upsilonLog γ z) := by
  have dual_Q : Q (4 / γ) = Q γ := by
    unfold Q
    field_simp [hγ.ne']
    ring
  have dual_log_integrand z t : upsilonLogIntegrand (4 / γ) z t = upsilonLogIntegrand γ z t := by
    have hγne := hγ.ne'
    rw [upsilonLogIntegrand, dual_Q, (show t * (4 / γ) / 4 = t / γ by field_simp [hγne]), (show t / (4 / γ) = t * γ / 4 by field_simp [hγne])]
    congr 1
    congr 1
    rw [mul_comm (Real.sinh (t / γ) : ℂ) (Real.sinh (t * γ / 4) : ℂ)]
  have dual_upsilonLog z : upsilonLog (4 / γ) z = upsilonLog γ z := by
    unfold upsilonLog
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact dual_log_integrand z t
  have dual_forward_overlap_bound {z : ℂ} (hz : z.re < γ / 2) : z.re < 2 / (4 / γ) := by
    rw [(show (2 : ℝ) / (4 / γ) = γ / 2 by field_simp [hγ.ne']; ring)]
    exact hz
  have dual_integrableOn {x : ℝ} (hx0 : 0 < x) (hxQ : x < Q (4 / γ)) : IntegrableOn (fun t => upsilonLogIntegrand (4 / γ) (x : ℂ) t) (Ioi 0) := by
    apply (upsilonLogIntegrand_integrableOn hγ hγ2 (x : ℂ) (by simpa using hx0) (by simpa using (by rwa [dual_Q] at hxQ))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (dual_log_integrand (x : ℂ) t).symm
  have dual_log_differentiableOn : DifferentiableOn ℂ (fun z => upsilonLog (4 / γ) z) {z | 0 < z.re ∧ z.re < Q (4 / γ)} := by
    rw [(show {z : ℂ | 0 < z.re ∧ z.re < Q (4 / γ)} = {z | 0 < z.re ∧ z.re < Q γ} by rw [dual_Q]), (show (fun z => upsilonLog (4 / γ) z) = (fun z => upsilonLog γ z) by funext z; exact dual_upsilonLog z)]
    exact (upsilonLog_differentiableOn hγ hγ2)
  let δ := 4 / γ
  have hδhalf : δ / 2 = 2 / γ := by
    dsimp [δ]
    field_simp [hγ.ne']
    norm_num
  have hδcast : (δ : ℂ) = (4 / γ : ℂ) := by
    change ((4 / γ : ℝ) : ℂ) = (4 : ℂ) / (γ : ℂ)
    exact Complex.ofReal_div 4 γ
  have hδhalfC : ((δ : ℂ) / 2) = (2 : ℂ) / (γ : ℂ) := by
    rw [hδcast]
    field_simp [Complex.ofReal_ne_zero.mpr hγ.ne']
    norm_num
  have hdualLog w : upsilonLog δ w = upsilonLog γ w := by
    simpa [δ] using dual_upsilonLog w
  calc
    Complex.exp (upsilonLog γ (z + 2 / γ)) =
        Complex.exp (upsilonLog δ (z + δ / 2)) := by
          rw [← hδhalfC, hdualLog]
    _ = lFun (δ / 2 * z) * ((δ / 2 : ℝ) : ℂ) ^ (1 - (δ : ℂ) * z) *
        Complex.exp (upsilonLog δ z) := (exp_upsilonLog_shift_b_of_integrable (γ := δ) (by dsimp [δ]; positivity) (by simpa [δ] using dual_log_differentiableOn) (by intro x hx0 hxQ; simpa [δ] using dual_integrableOn hx0 (by simpa [δ] using hxQ)) hz0 (by simpa [δ] using dual_forward_overlap_bound hzγ))
    _ = lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) *
        Complex.exp (upsilonLog γ z) := by
          rw [hδhalf, hδhalfC, hdualLog, hδcast, (show ((2 / γ : ℝ) : ℂ) ^ (1 - (4 / γ : ℂ) * z) = ((γ / 2 : ℝ) : ℂ) ^ ((4 / γ : ℂ) * z - 1) by rw [(show ((2 / γ : ℝ) : ℂ) = ((γ / 2 : ℝ) : ℂ)⁻¹ by exact_mod_cast (by field_simp [hγ.ne'])), (show 1 - (4 / γ : ℂ) * z = -((4 / γ : ℂ) * z - 1) by ring), Complex.inv_cpow_ofReal_nonneg (by positivity : 0 ≤ γ / 2), Complex.cpow_neg]; simp)]

end DOZZ.Proofs

end
