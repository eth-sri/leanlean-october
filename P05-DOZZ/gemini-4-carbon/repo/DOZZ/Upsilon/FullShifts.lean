/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.StripShifts
import DOZZ.Upsilon.StripShiftsDual
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Entire Upsilon shift identities
-/

@[expose] public section

noncomputable section
open Complex Set Filter Topology

namespace DOZZ.Proofs

variable {U : ℂ → ℂ}
variable {γ : ℝ}

private def upsFwd (γ : ℝ) (c : ℂ) (e : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.Gamma (c * z) * (Complex.Gamma (1 - c * z))⁻¹ * ((γ / 2 : ℝ) : ℂ) ^ e z

private def upsInv (γ : ℝ) (c : ℂ) (e : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((γ / 2 : ℝ) : ℂ) ^ (-e z) * Complex.Gamma (1 - c * z) * (Complex.Gamma (c * z))⁻¹


private lemma ups_shift_core (hγ : 0 < γ) (hU : IsUpsilon γ U)
    (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') (hcc' : c * c' = 1) (hQ : c + c' = Q γ)
    (e : ℂ → ℂ) (he : Differentiable ℂ e)
    (hstrip : ∀ z : ℂ, 0 < z.re → z.re < c' →
      Complex.exp (upsilonLog γ (z + (c : ℂ))) =
        lFun ((c : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ e z * Complex.exp (upsilonLog γ z)) :
    (∀ z : ℂ, z.re < c' → upsInv γ (c : ℂ) e z * U (z + (c : ℂ)) = U z) ∧
      ∀ z : ℂ, (∀ n : ℕ, (c : ℂ) * z ≠ -(n : ℂ)) →
        U (z + (c : ℂ)) = lFun ((c : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ e z * U z := by
  have ups_cancel (c : ℂ) (e : ℂ → ℂ) {z : ℂ} (hΓ : Complex.Gamma (c * z) ≠ 0) (hΓ1 : Complex.Gamma (1 - c * z) ≠ 0) : upsInv γ c e z * upsFwd γ c e z = 1 := by
    have hpow : ((γ / 2 : ℝ) : ℂ) ^ e z ≠ 0 :=
      Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 (by positivity)))
    dsimp [upsInv, upsFwd]; rw [Complex.cpow_neg]
    field_simp [hpow, hΓ, hΓ1]
  have hb0 : ((γ / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hcre (z : ℂ) : ((c : ℂ) * z).re = c * z.re := by simp [Complex.mul_re]
  let o : Set ℂ := {z | 0 < z.re ∧ z.re < c'}
  have hoOpen : IsOpen o := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt c')
  let z₀ : ℂ := ((c' / 2 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ o := ⟨by simp [z₀, hc'], by simp [z₀]; linarith⟩
  have hright : ∀ z : ℂ, 0 < z.re → U (z + (c : ℂ)) = upsFwd γ (c : ℂ) e z * U z := by
    let s : Set ℂ := {z | 0 < z.re}
    have hf : DifferentiableOn ℂ (fun z => U (z + (c : ℂ))) s := fun z _ =>
      (DifferentiableAt.fun_comp' z (hU.1 _) (by fun_prop)).differentiableWithinAt
    have hg : DifferentiableOn ℂ (fun z => upsFwd γ (c : ℂ) e z * U z) s := fun z (hz : 0 < z.re) => by
      have hRe : 0 < ((c : ℂ) * z).re := by rw [hcre]; positivity
      have hG1 := DifferentiableAt.fun_comp' z
        (Complex.differentiableAt_Gamma _ fun n hn =>
          (Complex.Gamma_ne_zero_of_re_pos hRe) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n))
        (by fun_prop : DifferentiableAt ℂ (fun w => (c : ℂ) * w) z)
      have hG2 := DifferentiableAt.fun_comp' z Complex.differentiable_one_div_Gamma.differentiableAt
        (by fun_prop : DifferentiableAt ℂ (fun w => 1 - (c : ℂ) * w) z)
      have hG3 : DifferentiableAt ℂ (fun w => ((γ / 2 : ℝ) : ℂ) ^ e w) z :=
        DifferentiableAt.const_cpow (he z) (Or.inl hb0)
      exact (((hG1.mul hG2).mul hG3).mul (hU.1 z)).differentiableWithinAt
    have heq : EqOn (fun z => U (z + (c : ℂ))) (fun z => upsFwd γ (c : ℂ) e z * U z) o := fun z hz => by
      have hzQ : z.re < Q γ := by linarith [hz.2]
      have hzc0 : 0 < (z + (c : ℂ)).re := by simp [add_pos hz.1 hc]
      have hzcQ : (z + (c : ℂ)).re < Q γ := by simp; linarith [hz.2]
      dsimp only
      rw [hU.2 _ hzc0 hzcQ, hstrip z hz.1 hz.2, ← hU.2 z hz.1 hzQ]
      simp [upsFwd, lFun, div_eq_mul_inv, mul_assoc]
    intro z hz
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hf.analyticOnNhd (Complex.isOpen_re_gt 0)) (hg.analyticOnNhd (Complex.isOpen_re_gt 0))
      (convex_halfSpace_re_gt 0).isPreconnected hz₀.1
      (Filter.mem_of_superset (hoOpen.mem_nhds hz₀) heq) hz
  have hleft : ∀ z : ℂ, z.re < c' → upsInv γ (c : ℂ) e z * U (z + (c : ℂ)) = U z := by
    let s : Set ℂ := {z | z.re < c'}
    have hf : DifferentiableOn ℂ (fun z => upsInv γ (c : ℂ) e z * U (z + (c : ℂ))) s :=
      fun z (hz : z.re < c') => by
        have hlt1 : c * z.re < 1 := by simpa [hcc'] using mul_lt_mul_of_pos_left hz hc
        have hRe : 0 < (1 - (c : ℂ) * z).re := by rw [Complex.sub_re, Complex.one_re, hcre]; linarith
        have hG1 : DifferentiableAt ℂ (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-e w)) z :=
          DifferentiableAt.const_cpow (he z).neg (Or.inl hb0)
        have hG2 := DifferentiableAt.fun_comp' z
          (Complex.differentiableAt_Gamma _ fun n hn =>
            (Complex.Gamma_ne_zero_of_re_pos hRe) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n))
          (by fun_prop : DifferentiableAt ℂ (fun w => 1 - (c : ℂ) * w) z)
        have hG3 := DifferentiableAt.fun_comp' z Complex.differentiable_one_div_Gamma.differentiableAt
          (by fun_prop : DifferentiableAt ℂ (fun w => (c : ℂ) * w) z)
        exact (((hG1.mul hG2).mul hG3).mul
          (DifferentiableAt.fun_comp' z (hU.1 _) (by fun_prop))).differentiableWithinAt
    have hg : DifferentiableOn ℂ U s := fun z _ => (hU.1 z).differentiableWithinAt
    have heq : EqOn (fun z => upsInv γ (c : ℂ) e z * U (z + (c : ℂ))) U o := fun z hz => by
      have hlt1 : c * z.re < 1 := by simpa [hcc'] using mul_lt_mul_of_pos_left hz.2 hc
      have hΓ :=
        Complex.Gamma_ne_zero_of_re_pos (by rw [hcre]; exact mul_pos hc hz.1)
      have hΓ1 : Complex.Gamma (1 - (c : ℂ) * z) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.sub_re, Complex.one_re, hcre]; linarith)
      dsimp only
      rw [hright z hz.1, ← mul_assoc, ups_cancel (c : ℂ) e hΓ hΓ1, one_mul]
    intro z hz
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hf.analyticOnNhd (Complex.isOpen_re_lt c')) (hg.analyticOnNhd (Complex.isOpen_re_lt c'))
      (convex_halfSpace_re_lt c').isPreconnected hz₀.2
      (Filter.mem_of_superset (hoOpen.mem_nhds hz₀) heq) hz
  refine ⟨hleft, fun z hz => ?_⟩
  by_cases hzRe : 0 < z.re
  · simpa [upsFwd, lFun, div_eq_mul_inv, mul_assoc] using hright z hzRe
  · have hzRe' : z.re ≤ 0 := le_of_not_gt hzRe
    have hrec := hleft z (lt_of_le_of_lt hzRe' hc')
    have hΓ1 : Complex.Gamma (1 - (c : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.sub_re, Complex.one_re, hcre]; nlinarith)
    have hcan := ups_cancel (c : ℂ) e (Complex.Gamma_ne_zero hz) hΓ1
    calc U (z + (c : ℂ)) = upsFwd γ (c : ℂ) e z * (upsInv γ (c : ℂ) e z * U (z + (c : ℂ))) := by
          rw [← mul_assoc, mul_comm (upsFwd _ _ _ _), hcan, one_mul]
      _ = upsFwd γ (c : ℂ) e z * U z := by rw [hrec]
      _ = _ := by simp [upsFwd, lFun, div_eq_mul_inv, mul_assoc]

section
variable (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) (z : ℂ)
include hγ hγ2 hU z

/-- Reciprocal form of the first shift. The reciprocal Gamma is entire and its
totalized zeros encode the zeros created by continuation to the left. -/
theorem IsUpsilon.shift_b_reciprocal (hz : z.re < 2 / γ) :
    ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * z)) *
      Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
      (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹ * U (z + (γ / 2 : ℂ)) = U z := by
  have hc : ((γ / 2 : ℝ) : ℂ) = (γ / 2 : ℂ) := by push_cast; rfl
  have h := (ups_shift_core hγ hU (γ / 2) (2 / γ) (by positivity) (by positivity)
    (by field_simp [hγ.ne']) (by unfold Q; ring)
    (fun w => 1 - (γ : ℂ) * w) (by fun_prop)
    (fun w hw0 hwQ => by simpa [hc] using exp_upsilonLog_shift_b hγ hγ2 hw0 hwQ)).1 z hz
  simpa [upsInv, hc] using h

/-- First shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(γz/2)`. -/
theorem IsUpsilon.shift_b (hz : ∀ n : ℕ, (γ / 2 : ℂ) * z ≠ -(n : ℂ)) :
    U (z + γ / 2) = lFun (γ / 2 * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - γ * z) * U z := by
  have hc : ((γ / 2 : ℝ) : ℂ) = (γ / 2 : ℂ) := by push_cast; rfl
  simpa [hc] using (ups_shift_core hγ hU (γ / 2) (2 / γ) (by positivity) (by positivity)
    (by field_simp [hγ.ne']) (by unfold Q; ring)
    (fun w => 1 - (γ : ℂ) * w) (by fun_prop)
    (fun w hw0 hwQ => by simpa [hc] using exp_upsilonLog_shift_b hγ hγ2 hw0 hwQ)).2 z
      (by simpa [hc] using hz)

/-- Second shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(2z/γ)`. -/
theorem IsUpsilon.shift_binv (hz : ∀ n : ℕ, (2 / γ : ℂ) * z ≠ -(n : ℂ)) :
    U (z + 2 / γ) = lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) * U z := by
  have hc : ((2 / γ : ℝ) : ℂ) = (2 / γ : ℂ) := by push_cast; rfl
  simpa [hc] using (ups_shift_core hγ hU (2 / γ) (γ / 2) (by positivity) (by positivity)
    (by field_simp [hγ.ne']) (by unfold Q; ring)
    (fun w => 4 / (γ : ℂ) * w - 1) (by fun_prop)
    (fun w hw0 hwQ => by simpa [hc] using exp_upsilonLog_shift_binv hγ hγ2 hw0 hwQ)).2 z
      (by simpa [hc] using hz)


end
end DOZZ.Proofs
