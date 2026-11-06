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

public section

open Complex MeasureTheory Set

namespace DOZZ.Proofs

variable {γ : ℝ} (hγ : 0 < γ)

include γ hγ
private theorem dual_Q  : Q (4 / γ) = Q γ := by
  unfold Q
  field_simp <;> ring


private theorem dual_log_integrand
    (z : ℂ) (t : ℝ) :
    upsilonLogIntegrand (4 / γ) z t = upsilonLogIntegrand γ z t := by
  have hγne  := hγ.ne'
  have h₁ : t * (4 / γ) / 4 = t / γ := by field_simp [hγne]
  have h₂ : t / (4 / γ) = t * γ / 4 := by field_simp [hγne]
  rw [upsilonLogIntegrand, dual_Q hγ, h₁, h₂]
  congr 1
  ring


private theorem dual_upsilonLog  (z : ℂ) :
    upsilonLog (4 / γ) z = upsilonLog γ z := by
  unfold upsilonLog
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact dual_log_integrand hγ z t


private theorem dual_log_differentiableOn
    (hγ2 : γ < 2) :
    DifferentiableOn ℂ (fun z => upsilonLog (4 / γ) z)
      {z | 0 < z.re ∧ z.re < Q (4 / γ)} := by
  have hlog := upsilonLog_differentiableOn hγ hγ2
  have hfun : (fun z : ℂ => upsilonLog (4 / γ) z) =
      (fun z => upsilonLog γ z) := by
    funext z
    exact dual_upsilonLog hγ z
  have hset : {z : ℂ | 0 < z.re ∧ z.re < Q (4 / γ)} =
      {z | 0 < z.re ∧ z.re < Q γ} := by rw [dual_Q hγ]
  rw [hset, hfun]
  exact hlog


private theorem dual_integrableOn  (hγ2 : γ < 2)
    {x : ℝ} (hx0 : 0 < x) (hxQ : x < Q (4 / γ)) :
    IntegrableOn (fun t : ℝ => upsilonLogIntegrand (4 / γ) (x : ℂ) t)
      (Ioi 0) := by
  have hxQ' : x < Q γ := by rwa [dual_Q hγ] at hxQ
  have h := upsilonLogIntegrand_integrableOn hγ hγ2 (x : ℂ) (hx0)
    (hxQ')
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (dual_log_integrand hγ (x : ℂ) t).symm


private theorem dual_forward_overlap_bound  {z : ℂ}
    (hz : z.re < γ / 2) : z.re < 2 / (4 / γ) := by
  bound


/-- The second strip shift, obtained by exchanging the two hyperbolic factors in the
defining integral and applying the first shift at parameter `4 / γ`. -/
theorem exp_upsilonLog_shift_binv  (hγ2 : γ < 2)
    {z : ℂ} (hz0 : 0 < z.re) (hzγ : z.re < γ / 2) :
    Complex.exp (upsilonLog γ (z + 2 / γ)) =
      lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) *
        Complex.exp (upsilonLog γ z) := by
  let δ : ℝ := 4 / γ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hzδ : z.re < 2 / δ := dual_forward_overlap_bound hγ hzγ
  have hInt : ∀ x : ℝ, 0 < x → x < Q δ →
      IntegrableOn (fun t : ℝ => upsilonLogIntegrand δ (x : ℂ) t) (Ioi 0) := by
    intro x hx0 hxQ
    simpa [δ] using dual_integrableOn hγ hγ2 hx0 (hxQ)
  have hforward := exp_upsilonLog_shift_b_of_integrable
    (γ := δ) hδ (dual_log_differentiableOn hγ hγ2) hInt hz0 hzδ
  have hδhalf : δ / 2 = 2 / γ := by
    dsimp [δ]
    field_simp [hγ.ne']
    norm_num
  have hδcast : (δ : ℂ) = (4 / γ : ℂ) := by
    continuity
  have hδhalfC : ((δ : ℂ) / 2) = (2 : ℂ) / (γ : ℂ) := by
    assumption_mod_cast
  have hdualLog (w : ℂ) : upsilonLog δ w = upsilonLog γ w := dual_upsilonLog hγ w
  have hbase : ((2 / γ : ℝ) : ℂ) = ((γ / 2 : ℝ) : ℂ)⁻¹ := by
    simp_all
  have hpower :
      ((2 / γ : ℝ) : ℂ) ^ (1 - (4 / γ : ℂ) * z) =
        ((γ / 2 : ℝ) : ℂ) ^ ((4 / γ : ℂ) * z - 1) := by
    have hexp : 1 - (4 / γ : ℂ) * z = -((4 / γ : ℂ) * z - 1) := by ring
    rw [hbase, hexp, Complex.inv_cpow_ofReal_nonneg (by positivity : 0 ≤ γ / 2),
      Complex.cpow_neg]
    simp
  simp_all
omit γ hγ


end DOZZ.Proofs

end
