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

Cross-multiplication by reciprocal Gamma makes the two sides entire, so the strip
identities extend by the analytic identity theorem.
-/

@[expose] public section
open Complex Set Filter Topology
namespace DOZZ.Proofs

variable {γ : ℝ} {U : ℂ → ℂ}

private theorem entire_shift (hU : IsUpsilon γ U) {c d a : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (ha : 0 < a) (hQ : Q γ = a + d)
    {b : ℂ} (hb : b ≠ 0) {e : ℂ → ℂ} (he : Differentiable ℂ e)
    (hshift : ∀ z : ℂ, 0 < z.re → z.re < a →
      exp (upsilonLog γ (z + d)) = lFun (c * z) * b ^ (e z) * exp (upsilonLog γ z))
    (z : ℂ) :
    (Gamma (c * z))⁻¹ * U (z + d) = (Gamma (1 - c * z))⁻¹ * b ^ (e z) * U z := by
  have hΓ : Differentiable ℂ (fun w => (Gamma w)⁻¹) := differentiable_one_div_Gamma
  have hp : Differentiable ℂ (fun w => b ^ (e w)) := fun w => (he w).const_cpow (Or.inl hb)
  have hU' := hU.1
  have hf' : Differentiable ℂ (fun w : ℂ => (Gamma ((c : ℂ) * w))⁻¹) :=
    hΓ.comp (by fun_prop : Differentiable ℂ (fun w : ℂ => (c : ℂ) * w))
  have hg' : Differentiable ℂ (fun w : ℂ => (Gamma (1 - (c : ℂ) * w))⁻¹) :=
    hΓ.comp (by fun_prop : Differentiable ℂ (fun w : ℂ => 1 - (c : ℂ) * w))
  have hf := hf'.mul (hU'.comp (by fun_prop : Differentiable ℂ (fun w : ℂ => w + d)))
  have hg := (hg'.mul hp).mul hU'
  refine congrFun ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (↑(a / 2) : ℂ)) ?_) z
  have ho : {(w : ℂ) | 0 < w.re ∧ w.re < a} ∈ 𝓝 (↑(a / 2) : ℂ) :=
    ((Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt a)).mem_nhds
      (by exact show 0 < a / 2 ∧ a / 2 < a by constructor <;> linarith)
  filter_upwards [ho] with w hw
  simp only [Pi.mul_apply, Function.comp_apply]
  have hpos : 0 < (c * w).re := by simpa using mul_pos hc hw.1
  have hΓw := Gamma_ne_zero_of_re_pos hpos
  rw [hU.2 w hw.1 (by linarith [hw.2]), hU.2 (w + d) (by simp; linarith [hw.1])
    (by simp; linarith [hw.2]), hshift w hw.1 hw.2]
  simp [lFun, div_eq_mul_inv, ← mul_assoc, hΓw]

private theorem shift_eq_of_entire_shift {z d c p : ℂ}
    (hz : ∀ n : ℕ, c * z ≠ -(n : ℂ))
    (h : (Gamma (c * z))⁻¹ * U (z + d) = (Gamma (1 - c * z))⁻¹ * p * U z) :
    U (z + d) = lFun (c * z) * p * U z := by
  have hΓ := Gamma_ne_zero hz
  apply mul_left_cancel₀ (inv_ne_zero hΓ)
  rw [h]
  simp [lFun, div_eq_mul_inv, ← mul_assoc, hΓ]

private theorem upsilonB_entire_shift (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) (z : ℂ) :
    (Gamma ((γ / 2 : ℂ) * z))⁻¹ * U (z + γ / 2) =
      (Gamma (1 - (γ / 2 : ℂ) * z))⁻¹ * ((γ / 2 : ℝ) : ℂ) ^ (1 - γ * z) * U z := by
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    entire_shift hU (c := γ / 2) (d := γ / 2) (a := 2 / γ)
      (by positivity) (by positivity) (by positivity) rfl
      (b := ((γ / 2 : ℝ) : ℂ)) (Complex.ofReal_ne_zero.mpr (by positivity))
      (e := fun w => 1 - γ * w) (by fun_prop)
      (fun w hw₀ hw => by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
        exp_upsilonLog_shift_b hγ hγ2 hw₀ hw) z

section
variable {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) (z : ℂ)
include hγ hγ2 hU

/-- Reciprocal form of the first shift. The reciprocal Gamma is entire and its
totalized zeros encode the zeros created by continuation to the left. -/
theorem IsUpsilon.shift_b_reciprocal (hz : z.re < 2 / γ) :
    ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * z)) *
      Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
      (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹ * U (z + (γ / 2 : ℂ)) = U z := by
  have hΓ : Gamma (1 - (γ / 2 : ℂ) * z) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp
    have h := mul_lt_mul_of_pos_right hz (half_pos hγ)
    have hcancel : 2 / γ * (γ / 2) = 1 := by field_simp
    linarith)
  have hp : ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  rw [Complex.cpow_neg, mul_assoc, mul_assoc, upsilonB_entire_shift hγ hγ2 hU]
  simp only [mul_assoc, mul_inv_cancel_left₀ hΓ, inv_mul_cancel_left₀ hp]

/-- First shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(γz/2)`. -/
theorem IsUpsilon.shift_b (hz : ∀ n : ℕ, (γ / 2 : ℂ) * z ≠ -(n : ℂ)) :
    U (z + γ / 2) = lFun (γ / 2 * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - γ * z) * U z :=
  shift_eq_of_entire_shift hz (upsilonB_entire_shift hγ hγ2 hU z)

/-- Second shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(2z/γ)`. -/
theorem IsUpsilon.shift_binv (hz : ∀ n : ℕ, (2 / γ : ℂ) * z ≠ -(n : ℂ)) :
    U (z + 2 / γ) = lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) * U z := by
  refine shift_eq_of_entire_shift hz ?_
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    entire_shift hU (c := 2 / γ) (d := 2 / γ) (a := γ / 2)
      (by positivity) (by positivity) (by positivity) (by unfold Q; ring)
      (b := ((γ / 2 : ℝ) : ℂ)) (Complex.ofReal_ne_zero.mpr (by positivity))
      (e := fun w => 4 / γ * w - 1) (by fun_prop)
      (fun w hw₀ hw => by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
        exp_upsilonLog_shift_binv hγ hγ2 hw₀ hw) z

end

end DOZZ.Proofs
