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

variable {γ : ℝ}








/-- The second strip shift, obtained by exchanging the two hyperbolic factors in the
defining integral and applying the first shift at parameter `4 / γ`. -/
theorem exp_upsilonLog_shift_binv (hγ : 0 < γ) (hγ2 : γ < 2)
    {z : ℂ} (hz0 : 0 < z.re) (hzγ : z.re < γ / 2) :
    Complex.exp (upsilonLog γ (z + 2 / γ)) =
      lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) *
        Complex.exp (upsilonLog γ z) := by
  have dual_forward_overlap_bound {z : ℂ} (hz : z.re < γ / 2) : z.re < 2 / (4 / γ) := by nlinarith
  have dual_Q : Q (4 / γ) = Q γ := by
    unfold Q
    field_simp [hγ.ne']
    ring
  have dual_log_integrand (z : ℂ) (t : ℝ) : upsilonLogIntegrand (4 / γ) z t = upsilonLogIntegrand γ z t := by
    have h₁ : t * (4 / γ) / 4 = t / γ := by ring
    have h₂ : t / (4 / γ) = t * γ / 4 := by nlinarith
    rw [upsilonLogIntegrand, dual_Q, h₁, h₂]
    congr 1
    ring
  have dual_integrableOn {x : ℝ} (hx0 : 0 < x) (hxQ : x < Q (4 / γ)) : IntegrableOn (fun t : ℝ => upsilonLogIntegrand (4 / γ) (x : ℂ) t)
        (Ioi 0) := by
    have hxQ' : x < Q γ := by rwa [dual_Q] at hxQ
    have h := upsilonLogIntegrand_integrableOn hγ hγ2 (x : ℂ) (by simpa using hx0)
      (by simpa using hxQ')
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (dual_log_integrand (x : ℂ) t).symm
  have dual_upsilonLog (z : ℂ) : upsilonLog (4 / γ) z = upsilonLog γ z := by
    unfold upsilonLog
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact dual_log_integrand z t
  have dual_log_differentiableOn : DifferentiableOn ℂ (fun z => upsilonLog (4 / γ) z)
        {z | 0 < z.re ∧ z.re < Q (4 / γ)} := by
    have hfun : (fun z : ℂ => upsilonLog (4 / γ) z) =
        (fun z => upsilonLog γ z) := by
      funext z
      exact dual_upsilonLog z
    have hset : {z : ℂ | 0 < z.re ∧ z.re < Q (4 / γ)} =
        {z | 0 < z.re ∧ z.re < Q γ} := by rw [dual_Q]
    rw [hset, hfun]
    exact upsilonLog_differentiableOn hγ hγ2
  let δ := 4 / γ
  have hδ : 0 < δ := by positivity
  have hzδ : z.re < 2 / δ := by
    simpa [δ] using dual_forward_overlap_bound hzγ
  have hInt : ∀ x : ℝ, 0 < x → x < Q δ →
      IntegrableOn (fun t : ℝ => upsilonLogIntegrand δ (x : ℂ) t) (Ioi 0) := by
    intro x hx0 hxQ
    simpa [δ] using dual_integrableOn hx0 (by simpa [δ] using hxQ)
  have hforward := exp_upsilonLog_shift_b_of_integrable
    (γ := δ) hδ (by simpa [δ] using dual_log_differentiableOn) hInt hz0 hzδ
  have hδhalf : δ / 2 = 2 / γ := by ring
  have hδcast : (δ : ℂ) = (4 / γ : ℂ) := by
    change ((4 / γ : ℝ) : ℂ) = (4 : ℂ) / (γ : ℂ)
    exact Complex.ofReal_div 4 γ
  have hδhalfC : ((δ : ℂ) / 2) = (2 : ℂ) / (γ : ℂ) := by grind
  have hdualLog (w : ℂ) : upsilonLog δ w = upsilonLog γ w := by
    simpa [δ] using dual_upsilonLog w
  have hbase : ((2 / γ : ℝ) : ℂ) = ((γ / 2 : ℝ) : ℂ)⁻¹ := by simp
  have hpower :
      ((2 / γ : ℝ) : ℂ) ^ (1 - (4 / γ : ℂ) * z) =
        ((γ / 2 : ℝ) : ℂ) ^ ((4 / γ : ℂ) * z - 1) := by
    have hexp : 1 - (4 / γ : ℂ) * z = -((4 / γ : ℂ) * z - 1) := by ring
    rw [hbase, hexp, Complex.inv_cpow_ofReal_nonneg (by positivity : 0 ≤ γ / 2),
      Complex.cpow_neg]
    simp
  calc
    Complex.exp (upsilonLog γ (z + 2 / γ)) =
        Complex.exp (upsilonLog δ (z + δ / 2)) := by
          rw [← hδhalfC, hdualLog]
    _ = lFun (δ / 2 * z) * ((δ / 2 : ℝ) : ℂ) ^ (1 - (δ : ℂ) * z) *
        Complex.exp (upsilonLog δ z) := hforward
    _ = lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) *
        Complex.exp (upsilonLog γ z) := by
          rw [hδhalf, hδhalfC, hdualLog, hδcast, hpower]

end DOZZ.Proofs

end
