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

The overlap shift identities extend to half-planes by the analytic identity theorem.
Reciprocal Gamma gives the holomorphic multiplier on the opposite half-plane; the exact
exclusions in the statements of `DOZZ.IsUpsilon.shift_b` and `DOZZ.IsUpsilon.shift_binv`
then permit pointwise inversion there.
-/

@[expose] public section

open Complex Set Filter Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

private noncomputable def upsilonBForwardMultiplier (γ : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma ((γ / 2 : ℂ) * z) *
    (Complex.Gamma (1 - (γ / 2 : ℂ) * z))⁻¹ *
    ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z)

private noncomputable def upsilonBInverseMultiplier (γ : ℝ) (z : ℂ) : ℂ :=
  ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * z)) *
    Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
    (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹

private noncomputable def upsilonBinvForwardMultiplier (γ : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma ((2 / γ : ℂ) * z) *
    (Complex.Gamma (1 - (2 / γ : ℂ) * z))⁻¹ *
    ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1)

private noncomputable def upsilonBinvInverseMultiplier (γ : ℝ) (z : ℂ) : ℂ :=
  ((γ / 2 : ℝ) : ℂ) ^ (-(4 / (γ : ℂ) * z - 1)) *
    Complex.Gamma (1 - (2 / γ : ℂ) * z) *
    (Complex.Gamma ((2 / γ : ℂ) * z))⁻¹
section
variable (γ : ℝ)

private theorem complex_half_re : ((γ / 2 : ℂ)).re = γ / 2 := by
  simp

private theorem complex_half_cast :
    ((γ / 2 : ℝ) : ℂ) = (γ / 2 : ℂ) := Complex.ofReal_div γ 2

private theorem complex_dual_re : ((2 / γ : ℂ)).re = 2 / γ := by
  simp

end

private theorem differentiableOn_eqOn_of_open
    {s o : Set ℂ} {f g : ℂ → ℂ}
    (hsOpen : IsOpen s) (hsConn : IsPreconnected s)
    (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (hoOpen : IsOpen o) (hoSub : o ⊆ s) (z₀ : ℂ) (hz₀ : z₀ ∈ o)
    (heq : EqOn f g o) : EqOn f g s := by
  have heq' : f =ᶠ[𝓝 z₀] g := by
    filter_upwards [hoOpen.mem_nhds hz₀] with z hz
    tauto
  intro z hz
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hf.analyticOnNhd hsOpen) (hg.analyticOnNhd hsOpen) hsConn
    (hoSub hz₀) heq') hz
section
variable (hγ : 0 < γ) {z : ℂ}
include hγ

private theorem differentiableAt_upsilonBForwardMultiplier
    (hz : 0 < z.re) :
    DifferentiableAt ℂ (upsilonBForwardMultiplier γ) z := by
  let b := (γ / 2 : ℂ)
  have hbR : 0 < γ / 2 := by positivity
  have hbzre : (b * z).re = (γ / 2) * z.re := by
    aesop
  have hArgRe : 0 < (b * z).re := by simp_all
  have hbDiff : DifferentiableAt ℂ (fun w => b * w) z := by fun_prop
  have hOneMinusDiff : DifferentiableAt ℂ (fun w => 1 - b * w) z := by fun_prop
  have hGamma : DifferentiableAt ℂ Complex.Gamma (b * z) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hzero : Complex.Gamma (b * z) = 0 := by
        grind
      exact (Complex.Gamma_ne_zero_of_re_pos hArgRe) hzero)
  have hGammaComp : DifferentiableAt ℂ (fun w => Complex.Gamma (b * w)) z :=
    by fun_prop
  have hInvGammaComp : DifferentiableAt ℂ
      (fun w => (Complex.Gamma (1 - b * w))⁻¹) z := by
    exact DifferentiableAt.fun_comp' z
      (g := fun v : ℂ => (Complex.Gamma v)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt hOneMinusDiff
  have hPow : DifferentiableAt ℂ
      (fun w => ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * w)) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (by
        apply Complex.ofReal_ne_zero.mpr
        exact div_ne_zero hγ.ne' (by norm_num))
  change DifferentiableAt ℂ
    (fun w => Complex.Gamma _ * (Complex.Gamma _)⁻¹ *
      ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * w)) z
  exact (hGammaComp.mul hInvGammaComp).mul hPow

private theorem differentiableAt_upsilonBInverseMultiplier
    (hz : z.re < 2 / γ) :
    DifferentiableAt ℂ (upsilonBInverseMultiplier γ) z := by
  let b := (γ / 2 : ℂ)
  have hbR : 0 < γ / 2 := by positivity
  have hbzre : (b * z).re = (γ / 2) * z.re := by
    aesop
  have hscale : (γ / 2) * z.re < 1 := by
    have hmul := mul_lt_mul_of_pos_left hz hbR
    grind
  have hArgRe : 0 < (1 - b * z).re := by
    simp_all
  have hbDiff : DifferentiableAt ℂ (fun w => b * w) z := by fun_prop
  have hOneMinusDiff : DifferentiableAt ℂ (fun w => 1 - b * w) z := by fun_prop
  have hGamma : DifferentiableAt ℂ Complex.Gamma (1 - b * z) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hzero : Complex.Gamma (1 - b * z) = 0 := by
        grind
      exact (Complex.Gamma_ne_zero_of_re_pos hArgRe) hzero)
  have hGammaComp : DifferentiableAt ℂ
      (fun w => Complex.Gamma (1 - b * w)) z :=
    by fun_prop
  have hInvGammaComp : DifferentiableAt ℂ
      (fun w => (Complex.Gamma (b * w))⁻¹) z := by
    exact DifferentiableAt.fun_comp' z
      (g := fun v : ℂ => (Complex.Gamma v)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt hbDiff
  have hPow : DifferentiableAt ℂ
      (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * w))) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (by
        apply Complex.ofReal_ne_zero.mpr
        exact div_ne_zero hγ.ne' (by norm_num))
  change DifferentiableAt ℂ
    (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * w)) *
      Complex.Gamma _ * (Complex.Gamma _)⁻¹) z
  exact (hPow.mul hGammaComp).mul hInvGammaComp

private theorem differentiableAt_upsilonBinvForwardMultiplier
    (hz : 0 < z.re) :
    DifferentiableAt ℂ (upsilonBinvForwardMultiplier γ) z := by
  let c := (2 / γ : ℂ)
  have hcR : 0 < 2 / γ := by positivity
  have hczre : (c * z).re = (2 / γ) * z.re := by
    aesop
  have hArgRe : 0 < (c * z).re := by simp_all
  have hcDiff : DifferentiableAt ℂ (fun w => c * w) z := by fun_prop
  have hOneMinusDiff : DifferentiableAt ℂ (fun w => 1 - c * w) z := by fun_prop
  have hGamma : DifferentiableAt ℂ Complex.Gamma (c * z) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hzero : Complex.Gamma (c * z) = 0 := by
        grind
      exact (Complex.Gamma_ne_zero_of_re_pos hArgRe) hzero)
  have hGammaComp : DifferentiableAt ℂ (fun w => Complex.Gamma (c * w)) z :=
    by fun_prop
  have hInvGammaComp : DifferentiableAt ℂ
      (fun w => (Complex.Gamma (1 - c * w))⁻¹) z := by
    exact DifferentiableAt.fun_comp' z
      (g := fun v : ℂ => (Complex.Gamma v)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt hOneMinusDiff
  have hPow : DifferentiableAt ℂ
      (fun w => ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * w - 1)) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (by
        apply Complex.ofReal_ne_zero.mpr
        exact div_ne_zero hγ.ne' (by norm_num))
  change DifferentiableAt ℂ
    (fun w => Complex.Gamma _ * (Complex.Gamma _)⁻¹ *
      ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * w - 1)) z
  exact (hGammaComp.mul hInvGammaComp).mul hPow

private theorem differentiableAt_upsilonBinvInverseMultiplier
    (hz : z.re < γ / 2) :
    DifferentiableAt ℂ (upsilonBinvInverseMultiplier γ) z := by
  let c := (2 / γ : ℂ)
  have hcR : 0 < 2 / γ := by positivity
  have hczre : (c * z).re = (2 / γ) * z.re := by
    aesop
  have hscale : (2 / γ) * z.re < 1 := by
    have hmul := mul_lt_mul_of_pos_left hz hcR
    grind
  have hArgRe : 0 < (1 - c * z).re := by
    simp_all
  have hcDiff : DifferentiableAt ℂ (fun w => c * w) z := by fun_prop
  have hOneMinusDiff : DifferentiableAt ℂ (fun w => 1 - c * w) z := by fun_prop
  have hGamma : DifferentiableAt ℂ Complex.Gamma (1 - c * z) :=
    Complex.differentiableAt_Gamma _ (by
      intro n hn
      have hzero : Complex.Gamma (1 - c * z) = 0 := by
        grind
      exact (Complex.Gamma_ne_zero_of_re_pos hArgRe) hzero)
  have hGammaComp : DifferentiableAt ℂ
      (fun w => Complex.Gamma (1 - c * w)) z :=
    by fun_prop
  have hInvGammaComp : DifferentiableAt ℂ
      (fun w => (Complex.Gamma (c * w))⁻¹) z := by
    exact DifferentiableAt.fun_comp' z
      (g := fun v : ℂ => (Complex.Gamma v)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt hcDiff
  have hPow : DifferentiableAt ℂ
      (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(4 / (γ : ℂ) * w - 1))) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (by
        apply Complex.ofReal_ne_zero.mpr
        exact div_ne_zero hγ.ne' (by norm_num))
  change DifferentiableAt ℂ
    (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(4 / (γ : ℂ) * w - 1)) *
      Complex.Gamma _ * (Complex.Gamma _)⁻¹) z
  exact (hPow.mul hGammaComp).mul hInvGammaComp

private theorem upsilonBMultipliers_cancel_of_nonzero
    (hΓ : Complex.Gamma ((γ / 2 : ℂ) * z) ≠ 0)
    (hΓ1 : Complex.Gamma (1 - (γ / 2 : ℂ) * z) ≠ 0) :
    upsilonBInverseMultiplier γ z * upsilonBForwardMultiplier γ z = 1 := by
  have hb : ((γ / 2 : ℝ) : ℂ) ≠ 0 := by
    aesop
  have hpow : ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) ≠ 0 :=
    by simp_all
  have hpowC : ((γ / 2 : ℂ) ^ (1 - (γ : ℂ) * z)) ≠ 0 := by
    simp_all
  change
    (((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * z)) *
      Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
      (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹) *
    (Complex.Gamma ((γ / 2 : ℂ) * z) *
      (Complex.Gamma (1 - (γ / 2 : ℂ) * z))⁻¹ *
      ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z)) = 1
  rw [Complex.cpow_neg]
  grind

private theorem upsilonBinvMultipliers_cancel_of_nonzero
    (hΓ : Complex.Gamma ((2 / γ : ℂ) * z) ≠ 0)
    (hΓ1 : Complex.Gamma (1 - (2 / γ : ℂ) * z) ≠ 0) :
    upsilonBinvInverseMultiplier γ z * upsilonBinvForwardMultiplier γ z = 1 := by
  have hb : ((γ / 2 : ℝ) : ℂ) ≠ 0 := by
    aesop
  have hpow : ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1) ≠ 0 :=
    by simp_all
  have hpowC : ((γ / 2 : ℂ) ^ (4 / (γ : ℂ) * z - 1)) ≠ 0 := by
    simp_all
  change
    (((γ / 2 : ℝ) : ℂ) ^ (-(4 / (γ : ℂ) * z - 1)) *
      Complex.Gamma (1 - (2 / γ : ℂ) * z) *
      (Complex.Gamma ((2 / γ : ℂ) * z))⁻¹) *
    (Complex.Gamma ((2 / γ : ℂ) * z) *
      (Complex.Gamma (1 - (2 / γ : ℂ) * z))⁻¹ *
      ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1)) = 1
  rw [Complex.cpow_neg]
  grind

end
section
variable (hγ : 0 < γ) (hγ2 : γ < 2) {U : ℂ → ℂ} (hU : IsUpsilon γ U)
include hγ hγ2 hU

private theorem upsilonB_shift_on_right
    :
    ∀ z : ℂ, 0 < z.re →
      U (z + (γ / 2 : ℂ)) = upsilonBForwardMultiplier γ z * U z := by
  let s : Set ℂ := {z | 0 < z.re}
  let o : Set ℂ := {z | 0 < z.re ∧ z.re < 2 / γ}
  let f : ℂ → ℂ := fun z => U (z + (γ / 2))
  let g : ℂ → ℂ := fun z => upsilonBForwardMultiplier γ z * U z
  have hsOpen : IsOpen s := Complex.isOpen_re_gt 0
  have hsConn : IsPreconnected s := (convex_halfSpace_re_gt 0).isPreconnected
  have hoOpen : IsOpen o := by
    change IsOpen ((Complex.re ⁻¹' Set.Ioi 0) ∩
      (Complex.re ⁻¹' Set.Iio _))
    exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))
  have hoSub : o ⊆ s := by
    aesop
  have hf : DifferentiableOn ℂ f s := by
    intro z hz
    dsimp [f]
    exact (DifferentiableAt.fun_comp' z (f := fun w : ℂ => w + (γ / 2))
      (g := U) (hU.1 _) (by fun_prop)).differentiableWithinAt
  have hg : DifferentiableOn ℂ g s := by
    intro z hz
    dsimp [g]
    exact (differentiableAt_upsilonBForwardMultiplier hγ hz).differentiableWithinAt.mul
      (hU.1 z).differentiableWithinAt
  have hz₀ : 1 ∈ o := by
    dsimp [o]
    bound
  have heq : EqOn f g o := by
    intro z hz
    dsimp [f, g, o] at hz ⊢
    have hzQ : z.re < Q γ := by
      unfold Q
      have hpos : 0 < γ / 2 := by positivity
      linarith
    have hzbQ : (z + (γ / 2)).re < Q γ := by
      rw [Complex.add_re, complex_half_re]
      unfold Q
      linarith
    have hzb0 : 0 < (z + (γ / 2)).re := by
      rw [Complex.add_re, complex_half_re]
      exact add_pos hz.1 (by positivity)
    calc
      U _ = Complex.exp _ :=
        hU.2 _ hzb0 hzbQ
      _ = lFun _ * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
          Complex.exp _ :=
        exp_upsilonLog_shift_b hγ hγ2 hz.1 hz.2
      _ = upsilonBForwardMultiplier γ z * U z := by
        rw [hU.2 z hz.1 hzQ]
        simp [upsilonBForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc]
  intro z hz
  exact (differentiableOn_eqOn_of_open hsOpen hsConn hf hg hoOpen hoSub 1 hz₀ heq) hz

private theorem upsilonB_shift_reciprocal_on_left
    :
    ∀ z : ℂ, z.re < 2 / γ →
      upsilonBInverseMultiplier γ z * U (z + (γ / 2 : ℂ)) = U z := by
  let s : Set ℂ := {z | z.re < 2 / γ}
  let o : Set ℂ := {z | 0 < z.re ∧ z.re < 2 / γ}
  let f : ℂ → ℂ := fun z => upsilonBInverseMultiplier γ z *
    U (z + (γ / 2))
  let g := U
  have hsConn : IsPreconnected s := (convex_halfSpace_re_lt _).isPreconnected
  have hoOpen : IsOpen o := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))
  have hoSub : o ⊆ s := by aesop
  have hf : DifferentiableOn ℂ f s := by
    intro z hz
    exact (differentiableAt_upsilonBInverseMultiplier hγ hz).differentiableWithinAt.mul <|
      (DifferentiableAt.fun_comp' z
        (hU.1 _) (by fun_prop)).differentiableWithinAt
  have hg : DifferentiableOn ℂ g s := by
    intro z hz
    exact (hU.1 z).differentiableWithinAt
  have hz₀ : 1 ∈ o := by
    dsimp [o]
    bound
  have heq : EqOn f g o := by
    intro z hz
    dsimp [f, g, o] at hz ⊢
    have hΓ : Complex.Gamma ((γ / 2 : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        simp_all)
    have hΓ1 : Complex.Gamma (1 - (γ / 2 : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        have hb : 0 < γ / 2 := by positivity
        have hlt := mul_lt_mul_of_pos_left hz.2 hb
        have hcancel : (γ / 2) * (2 / γ) = 1 := by field_simp
        have hbzre : ((γ / 2 : ℂ) * z).re = (γ / 2) * z.re := by simp
        rw [Complex.sub_re, Complex.one_re, hbzre]
        linarith)
    have hcancel := upsilonBMultipliers_cancel_of_nonzero hγ hΓ hΓ1
    have hforward := upsilonB_shift_on_right hγ hγ2 hU z hz.1
    calc
      _ = upsilonBInverseMultiplier γ z *
          (upsilonBForwardMultiplier γ z * U z) := by simp_all
      _ = U z := by grind
  intro z hz
  exact (differentiableOn_eqOn_of_open (Complex.isOpen_re_lt (2 / γ)) hsConn hf hg hoOpen hoSub 1 hz₀ heq) hz

private theorem upsilonBinv_shift_on_right
    :
    ∀ z : ℂ, 0 < z.re →
      U (z + (2 / γ : ℂ)) = upsilonBinvForwardMultiplier γ z * U z := by
  let s : Set ℂ := {z | 0 < z.re}
  let o : Set ℂ := {z | 0 < z.re ∧ z.re < γ / 2}
  let f : ℂ → ℂ := fun z => U (z + (2 / γ))
  let g : ℂ → ℂ := fun z => upsilonBinvForwardMultiplier γ z * U z
  have hoOpen : IsOpen o := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (γ / 2))
  have hoSub : o ⊆ s := by aesop
  have hf : DifferentiableOn ℂ f s := by
    intro z hz
    dsimp [f]
    exact (DifferentiableAt.fun_comp' z (f := fun w : ℂ => w + (2 / γ))
      (g := U) (hU.1 _) (by fun_prop)).differentiableWithinAt
  have hg : DifferentiableOn ℂ g s := by
    intro z hz
    dsimp [g]
    exact (differentiableAt_upsilonBinvForwardMultiplier hγ hz).differentiableWithinAt.mul
      (hU.1 z).differentiableWithinAt
  let z₀ : ℂ := (γ / 4 : ℝ)
  have hz₀ : z₀ ∈ o := by
    dsimp [z₀, o]
    grind
  have heq : EqOn f g o := by
    intro z hz
    dsimp [f, g, o] at hz ⊢
    have hzQ : z.re < Q γ := by
      unfold Q
      have hpos : 0 < 2 / γ := by positivity
      linarith
    have hzbQ : (z + (2 / γ)).re < Q γ := by
      rw [Complex.add_re, complex_dual_re]
      unfold Q
      linarith
    have hzb0 : 0 < (z + (2 / γ)).re := by
      rw [Complex.add_re, complex_dual_re]
      exact add_pos hz.1 (by positivity)
    calc
      U _ = Complex.exp _ :=
        hU.2 _ hzb0 hzbQ
      _ = lFun _ * ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1) *
          Complex.exp _ :=
        exp_upsilonLog_shift_binv hγ hγ2 hz.1 hz.2
      _ = upsilonBinvForwardMultiplier γ z * U z := by
        rw [hU.2 z hz.1 hzQ]
        simp [upsilonBinvForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc]
  have hEq := differentiableOn_eqOn_of_open (Complex.isOpen_re_gt 0) ((convex_halfSpace_re_gt 0).isPreconnected) hf hg hoOpen hoSub z₀ hz₀ heq
  intro z hz
  exact hEq hz

private theorem upsilonBinv_shift_reciprocal_on_left
    :
    ∀ z : ℂ, z.re < γ / 2 →
      upsilonBinvInverseMultiplier γ z * U (z + (2 / γ : ℂ)) = U z := by
  let s : Set ℂ := {z | z.re < γ / 2}
  let o : Set ℂ := {z | 0 < z.re ∧ z.re < γ / 2}
  let f : ℂ → ℂ := fun z => upsilonBinvInverseMultiplier γ z *
    U (z + (2 / γ))
  let g := U
  have hoOpen : IsOpen o := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (γ / 2))
  have hoSub : o ⊆ s := by aesop
  have hf : DifferentiableOn ℂ f s := by
    intro z hz
    exact (differentiableAt_upsilonBinvInverseMultiplier hγ hz).differentiableWithinAt.mul <|
      (DifferentiableAt.fun_comp' z
        (hU.1 _) (by fun_prop)).differentiableWithinAt
  have hg : DifferentiableOn ℂ g s := by
    intro z hz
    exact (hU.1 z).differentiableWithinAt
  let z₀ : ℂ := (γ / 4 : ℝ)
  have hz₀ : z₀ ∈ o := by
    dsimp [z₀, o]
    grind
  have heq : EqOn f g o := by
    intro z hz
    dsimp [f, g, o] at hz ⊢
    have hzQ : z.re < Q γ := by
      unfold Q
      have hpos : 0 < 2 / γ := by positivity
      linarith
    have hzbQ : (z + (2 / γ)).re < Q γ := by
      rw [Complex.add_re, complex_dual_re]
      unfold Q
      linarith
    have hΓ : Complex.Gamma ((2 / γ : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        have hcre : ((2 / γ : ℂ) * z).re = (2 / γ) * z.re := by simp
        rw [hcre]
        exact mul_pos (by positivity) hz.1)
    have hΓ1 : Complex.Gamma (1 - (2 / γ : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        have hc : 0 < 2 / γ := by positivity
        have hlt := mul_lt_mul_of_pos_left hz.2 hc
        have hcancel : (2 / γ) * (γ / 2) = 1 := by field_simp
        rw [hcancel] at hlt
        have hcre : ((2 / γ : ℂ) * z).re = (2 / γ) * z.re := by simp
        rw [Complex.sub_re, Complex.one_re, hcre]
        linarith)
    have hcancel := upsilonBinvMultipliers_cancel_of_nonzero hγ hΓ hΓ1
    have hforward := upsilonBinv_shift_on_right hγ hγ2 hU z hz.1
    calc
      _ = upsilonBinvInverseMultiplier γ z *
          (upsilonBinvForwardMultiplier γ z * U z) := by simp_all
      _ = U z := by grind
  have hEq := differentiableOn_eqOn_of_open (Complex.isOpen_re_lt (γ / 2)) ((convex_halfSpace_re_lt (γ / 2)).isPreconnected) hf hg hoOpen hoSub z₀ hz₀ heq
  intro z hz
  exact hEq hz

end
section
variable {U : ℂ → ℂ}
section
variable (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) (z : ℂ)
include hγ hγ2 hU

/-- Reciprocal form of the first shift. The reciprocal Gamma is entire and its
totalized zeros encode the zeros created by continuation to the left. -/
theorem IsUpsilon.shift_b_reciprocal (hz : z.re < 2 / γ) :
    ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * z)) *
      Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
      (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹ * U (z + (γ / 2 : ℂ)) = U z := by
  simpa [upsilonBInverseMultiplier] using
    upsilonB_shift_reciprocal_on_left hγ hγ2 hU z hz

/-- First shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(γz/2)`. -/
theorem IsUpsilon.shift_b (hz : ∀ n : ℕ, (γ / 2 : ℂ) * z ≠ -(n : ℂ)) :
    U (z + γ / 2) = lFun (γ / 2 * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - γ * z) * U z := by
  by_cases hzRe : 0 < z.re
  · have h := upsilonB_shift_on_right hγ hγ2 hU z hzRe
    assumption
  · have hzRe' : z.re ≤ 0 := le_of_not_gt hzRe
    have hrecip := upsilonB_shift_reciprocal_on_left hγ hγ2 hU z (by
      have hbound : 0 < 2 / γ := by positivity
      linarith)
    have hΓ1 : Complex.Gamma (1 - (γ / 2 : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        have hbzre : ((γ / 2 : ℂ) * z).re = (γ / 2) * z.re := by simp
        rw [Complex.sub_re, Complex.one_re, hbzre]
        nlinarith)
    have hcancel := upsilonBMultipliers_cancel_of_nonzero hγ (Complex.Gamma_ne_zero hz) hΓ1
    have hmulNe : upsilonBInverseMultiplier γ z ≠ 0 := by
      grind
    have hinv : (upsilonBInverseMultiplier γ z)⁻¹ = upsilonBForwardMultiplier γ z := by
      grind
    calc
      U _ = (upsilonBInverseMultiplier γ z)⁻¹ * U z := by
        grind
      _ = upsilonBForwardMultiplier γ z * U z := by simp_all
      _ = _ := by rfl

/-- Second shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(2z/γ)`. -/
theorem IsUpsilon.shift_binv (hz : ∀ n : ℕ, (2 / γ : ℂ) * z ≠ -(n : ℂ)) :
    U (z + 2 / γ) = lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) * U z := by
  by_cases hzRe : 0 < z.re
  · have h := upsilonBinv_shift_on_right hγ hγ2 hU z hzRe
    assumption
  · have hzRe' : z.re ≤ 0 := le_of_not_gt hzRe
    have hrecip := upsilonBinv_shift_reciprocal_on_left hγ hγ2 hU z (by
      linarith)
    have hΓ1 : Complex.Gamma (1 - (2 / γ : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        have hczre : ((2 / γ : ℂ) * z).re = (2 / γ) * z.re := by simp
        rw [Complex.sub_re, Complex.one_re, hczre]
        have hc : 0 < 2 / γ := by positivity
        nlinarith)
    have hcancel := upsilonBinvMultipliers_cancel_of_nonzero hγ (Complex.Gamma_ne_zero hz) hΓ1
    have hmulNe : upsilonBinvInverseMultiplier γ z ≠ 0 := by
      grind
    have hinv : (upsilonBinvInverseMultiplier γ z)⁻¹ =
        upsilonBinvForwardMultiplier γ z := by
      grind
    calc
      U _ = (upsilonBinvInverseMultiplier γ z)⁻¹ * U z := by
        grind
      _ = upsilonBinvForwardMultiplier γ z * U z := by simp_all
      _ = _ := by rfl

end

end

end DOZZ.Proofs
