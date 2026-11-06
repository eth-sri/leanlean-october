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


private theorem complex_half_cast (γ : ℝ) :
    ((γ / 2 : ℝ) : ℂ) = (γ / 2 : ℂ) := by
  exact Complex.ofReal_div γ 2


private theorem differentiableOn_eqOn_of_open
    {s o} {f g : ℂ → ℂ}
    (hsOpen : IsOpen s) (hsConn : IsPreconnected s)
    (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (hoOpen : IsOpen o) (hoSub : o ⊆ s) z₀ (hz₀ : z₀ ∈ o)
    (heq : EqOn f g o) : EqOn f g s := by
  intro z hz
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hf.analyticOnNhd hsOpen) (hg.analyticOnNhd hsOpen) hsConn
    (hoSub hz₀) (by filter_upwards [hoOpen.mem_nhds hz₀] with z hz; exact heq hz)) hz





private theorem upsilonBMultipliers_cancel_of_nonzero
    (hγ : 0 < γ) {z}
    (hΓ : Complex.Gamma ((γ / 2 : ℂ) * z) ≠ 0)
    (hΓ1 : Complex.Gamma (1 - (γ / 2 : ℂ) * z) ≠ 0) :
    upsilonBInverseMultiplier γ z * upsilonBForwardMultiplier γ z = 1 := by
  change
    (((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * z)) *
      Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
      (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹) *
    (Complex.Gamma ((γ / 2 : ℂ) * z) *
      (Complex.Gamma (1 - (γ / 2 : ℂ) * z))⁻¹ *
      ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z)) = 1
  rw [Complex.cpow_neg]
  calc
    _ = ((((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z)) *
          (((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z))⁻¹) *
        (Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
          (Complex.Gamma (1 - (γ / 2 : ℂ) * z))⁻¹) *
        (Complex.Gamma ((γ / 2 : ℂ) * z) *
          (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹) := by ring_nf
    _ = 1 := by simp [(show ((γ / 2 : ℂ) ^ (1 - (γ : ℂ) * z)) ≠ 0 by rw [← complex_half_cast]; exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (show ((γ / 2 : ℝ) : ℂ) ≠ 0 by apply Complex.ofReal_ne_zero.mpr; exact div_ne_zero hγ.ne' (by norm_num))))), hΓ, hΓ1]


private theorem upsilonB_shift_on_right
    (hγ : 0 < γ) (hγ2 : γ < 2) {U} (hU : IsUpsilon γ U) :
    ∀ z : ℂ, 0 < z.re →
      U (z + (γ / 2 : ℂ)) = upsilonBForwardMultiplier γ z * U z := by
  have complex_half_re (γ : ℝ) : ((γ / 2 : ℂ)).re = γ / 2 := by
    rw [Complex.div_ofNat_re, Complex.ofReal_re]
  have differentiableAt_upsilonBForwardMultiplier {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (upsilonBForwardMultiplier γ) z := by
    let b := (γ / 2 : ℂ)
    have hGamma := Complex.differentiableAt_Gamma (b * z) (by
        intro n hn
        exact (Complex.Gamma_ne_zero_of_re_pos (show 0 < (b * z).re by rw [(show (b * z).re = (γ / 2) * z.re by simp [b, Complex.mul_re])]; exact mul_pos (show 0 < γ / 2 by positivity) hz)) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n))
    have hPow : DifferentiableAt ℂ
        (fun w => ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * w)) z := by
      apply DifferentiableAt.const_cpow
      · fun_prop
      · exact Or.inl (by
          apply Complex.ofReal_ne_zero.mpr
          exact div_ne_zero hγ.ne' (by norm_num))
    change DifferentiableAt ℂ
      (fun w => Complex.Gamma (b * w) * (Complex.Gamma (1 - b * w))⁻¹ *
        ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * w)) z
    exact ((DifferentiableAt.fun_comp' z (f := fun w => b * w) (g := Complex.Gamma) hGamma (by fun_prop)).mul (DifferentiableAt.fun_comp' z (f := fun w => 1 - b * w) (g := fun v => (Complex.Gamma v)⁻¹) Complex.differentiable_one_div_Gamma.differentiableAt (by fun_prop))).mul hPow
  let o : Set ℂ := {z | 0 < z.re ∧ z.re < 2 / γ}
  let f : ℂ → ℂ := fun z => U (z + (γ / 2 : ℂ))
  let g : ℂ → ℂ := fun z => upsilonBForwardMultiplier γ z * U z
  have hz₀ : (1 : ℂ) ∈ o := by
    dsimp [o]
    constructor
    · norm_num
    · rw [one_lt_div hγ]
      exact hγ2
  have heq : EqOn f g o := by
    intro z hz
    dsimp [f, g, o] at hz ⊢
    calc
      U (z + (γ / 2 : ℂ)) = Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) :=
        hU.2 _ (show 0 < (z + (γ / 2 : ℂ)).re by rw [Complex.add_re, complex_half_re]; exact add_pos hz.1 (by positivity)) (by rw [Complex.add_re, complex_half_re]; unfold Q; linarith)
      _ = lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
          Complex.exp (upsilonLog γ z) :=
        exp_upsilonLog_shift_b hγ hγ2 hz.1 hz.2
      _ = upsilonBForwardMultiplier γ z * U z := by
        rw [hU.2 z hz.1 (show z.re < Q γ by unfold Q; linarith)]
        simp [upsilonBForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc]
  intro z hz
  exact (differentiableOn_eqOn_of_open (Complex.isOpen_re_gt 0) ((convex_halfSpace_re_gt 0).isPreconnected) (by intro z hz; dsimp [f]; exact (DifferentiableAt.fun_comp' z (f := fun w => w + (γ / 2 : ℂ)) (g := U) (hU.1 (z + (γ / 2 : ℂ))) (by fun_prop)).differentiableWithinAt) (by intro z hz; dsimp [g]; exact (differentiableAt_upsilonBForwardMultiplier hz).differentiableWithinAt.mul (hU.1 z).differentiableWithinAt) (by change IsOpen ((Complex.re ⁻¹' Set.Ioi (0 : ℝ)) ∩ (Complex.re ⁻¹' Set.Iio (2 / γ))); exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))) (by intro z hz; exact hz.1) 1 hz₀ heq) hz

private theorem upsilonB_shift_reciprocal_on_left
    (hγ : 0 < γ) (hγ2 : γ < 2) {U} (hU : IsUpsilon γ U) :
    ∀ z : ℂ, z.re < 2 / γ →
      upsilonBInverseMultiplier γ z * U (z + (γ / 2 : ℂ)) = U z := by
  have differentiableAt_upsilonBInverseMultiplier {z : ℂ} (hz : z.re < 2 / γ) : DifferentiableAt ℂ (upsilonBInverseMultiplier γ) z := by
    let b : ℂ := (γ / 2 : ℂ)
    have : (γ / 2) * z.re < 1 := by
      have hmul := mul_lt_mul_of_pos_left hz (show 0 < γ / 2 by positivity)
      rw [(show (γ / 2) * (2 / γ) = 1 by field_simp [hγ.ne'])] at hmul
      exact hmul
    have hGamma := Complex.differentiableAt_Gamma (1 - b * z) (by
        intro n hn
        exact (Complex.Gamma_ne_zero_of_re_pos (show 0 < (1 - b * z).re by rw [Complex.sub_re, Complex.one_re, (show (b * z).re = (γ / 2) * z.re by simp [b, Complex.mul_re])]; linarith)) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n))
    have hPow : DifferentiableAt ℂ
        (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * w))) z := by
      apply DifferentiableAt.const_cpow
      · fun_prop
      · exact Or.inl (by
          apply Complex.ofReal_ne_zero.mpr
          exact div_ne_zero hγ.ne' (by norm_num))
    change DifferentiableAt ℂ
      (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * w)) *
        Complex.Gamma (1 - b * w) * (Complex.Gamma (b * w))⁻¹) z
    exact (hPow.mul (DifferentiableAt.fun_comp' z (f := fun w => 1 - b * w) (g := Complex.Gamma) hGamma (by fun_prop))).mul (DifferentiableAt.fun_comp' z (f := fun w => b * w) (g := fun v => (Complex.Gamma v)⁻¹) Complex.differentiable_one_div_Gamma.differentiableAt (by fun_prop))
  let s : Set ℂ := {z | z.re < 2 / γ}
  let o : Set ℂ := {z | 0 < z.re ∧ z.re < 2 / γ}
  let f : ℂ → ℂ := fun z => upsilonBInverseMultiplier γ z *
    U (z + (γ / 2 : ℂ))
  let g := U
  have hsOpen := Complex.isOpen_re_lt (2 / γ)
  have hsConn := (convex_halfSpace_re_lt (2 / γ)).isPreconnected
  have hoOpen := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))
  have hoSub : o ⊆ s := fun _ hz => hz.2
  have hf : DifferentiableOn ℂ f s := by
    intro z hz
    dsimp [f]
    exact (differentiableAt_upsilonBInverseMultiplier hz).differentiableWithinAt.mul <|
      (DifferentiableAt.fun_comp' z (f := fun w => w + (γ / 2 : ℂ))
        (g := U) (hU.1 (z + (γ / 2 : ℂ))) (by fun_prop)).differentiableWithinAt
  have hg : DifferentiableOn ℂ g s := by
    intro z hz
    exact (hU.1 z).differentiableWithinAt
  have hz₀ : (1 : ℂ) ∈ o := by
    dsimp [o]
    constructor
    · norm_num
    · rw [one_lt_div hγ]
      exact hγ2
  have heq : EqOn f g o := by
    intro z hz
    dsimp [f, g, o] at hz ⊢
    have hΓ : Complex.Gamma ((γ / 2 : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        rw [(show ((γ / 2 : ℂ) * z).re = (γ / 2) * z.re by simp)]
        exact mul_pos (by positivity) hz.1)
    have hΓ1 : Complex.Gamma (1 - (γ / 2 : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        have hb : 0 < γ / 2 := by positivity
        have hlt := mul_lt_mul_of_pos_left hz.2 hb
        have hcancel : (γ / 2) * (2 / γ) = 1 := by field_simp [hγ.ne']
        rw [hcancel] at hlt
        rw [Complex.sub_re, Complex.one_re, (show ((γ / 2 : ℂ) * z).re = (γ / 2) * z.re by simp)]
        linarith)
    calc
      _ = upsilonBInverseMultiplier γ z *
          (upsilonBForwardMultiplier γ z * U z) := by rw [(upsilonB_shift_on_right hγ hγ2 hU z hz.1)]
      _ = U z := by rw [← mul_assoc, (upsilonBMultipliers_cancel_of_nonzero hγ hΓ hΓ1), one_mul]
  intro z hz
  exact (differentiableOn_eqOn_of_open hsOpen hsConn hf hg hoOpen hoSub 1 hz₀ heq) hz



/-- Reciprocal form of the first shift. The reciprocal Gamma is entire and its
totalized zeros encode the zeros created by continuation to the left. -/
theorem IsUpsilon.shift_b_reciprocal {U} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) (hz : z.re < 2 / γ) :
    ((γ / 2 : ℝ) : ℂ) ^ (-(1 - (γ : ℂ) * z)) *
      Complex.Gamma (1 - (γ / 2 : ℂ) * z) *
      (Complex.Gamma ((γ / 2 : ℂ) * z))⁻¹ * U (z + (γ / 2 : ℂ)) = U z := by
  simpa [upsilonBInverseMultiplier] using
    upsilonB_shift_reciprocal_on_left hγ hγ2 hU z hz

/-- First shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(γz/2)`. -/
theorem IsUpsilon.shift_b {U} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    z (hz : ∀ n : ℕ, (γ / 2 : ℂ) * z ≠ -(n : ℂ)) :
    U (z + γ / 2) = lFun (γ / 2 * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - γ * z) * U z := by
  by_cases hzRe : 0 < z.re
  · have h := upsilonB_shift_on_right hγ hγ2 hU z hzRe
    simpa [upsilonBForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc] using h
  · have hzRe' : z.re ≤ 0 := le_of_not_gt hzRe
    have hrecip := upsilonB_shift_reciprocal_on_left hγ hγ2 hU z (by
      have : 0 < 2 / γ := by positivity
      linarith)
    have hΓ1 : Complex.Gamma (1 - (γ / 2 : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        rw [Complex.sub_re, Complex.one_re, (show ((γ / 2 : ℂ) * z).re = (γ / 2) * z.re by simp)]
        nlinarith)
    have hcancel := upsilonBMultipliers_cancel_of_nonzero hγ (Complex.Gamma_ne_zero hz) hΓ1
    have hmulNe : upsilonBInverseMultiplier γ z ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hcancel
      norm_num at hcancel
    have hinv : (upsilonBInverseMultiplier γ z)⁻¹ = upsilonBForwardMultiplier γ z := by
      calc
        _ = (upsilonBInverseMultiplier γ z)⁻¹ *
            (upsilonBInverseMultiplier γ z * upsilonBForwardMultiplier γ z) := by rw [hcancel, mul_one]
        _ = upsilonBForwardMultiplier γ z := by
          rw [← mul_assoc, inv_mul_cancel₀ hmulNe, one_mul]
    calc
      U (z + γ / 2) = (upsilonBInverseMultiplier γ z)⁻¹ * U z := by
        calc
          U (z + γ / 2) =
              ((upsilonBInverseMultiplier γ z)⁻¹ * upsilonBInverseMultiplier γ z) *
                U (z + γ / 2) := by
                  rw [inv_mul_cancel₀ hmulNe, one_mul]
          _ = (upsilonBInverseMultiplier γ z)⁻¹ *
              (upsilonBInverseMultiplier γ z * U (z + γ / 2)) := by rw [mul_assoc]
          _ = _ := by rw [hrecip]
      _ = upsilonBForwardMultiplier γ z * U z := by rw [hinv]
      _ = _ := by simp [upsilonBForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc]

/-- Second shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(2z/γ)`. -/
theorem IsUpsilon.shift_binv {U} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    z (hz : ∀ n : ℕ, (2 / γ : ℂ) * z ≠ -(n : ℂ)) :
    U (z + 2 / γ) = lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) * U z := by
  have upsilonBinv_shift_on_right : ∀ z : ℂ, 0 < z.re → U (z + (2 / γ : ℂ)) = upsilonBinvForwardMultiplier γ z * U z := by
    have complex_dual_re (γ : ℝ) : ((2 / γ : ℂ)).re = 2 / γ := by
      by_cases hγ : γ = 0
      · simp [hγ]
      · rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
        field_simp [hγ]
        norm_num
        ring_nf
    have differentiableAt_upsilonBinvForwardMultiplier {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (upsilonBinvForwardMultiplier γ) z := by
      let c := (2 / γ : ℂ)
      have hGamma := Complex.differentiableAt_Gamma (c * z) (by
          intro n hn
          exact (Complex.Gamma_ne_zero_of_re_pos (show 0 < (c * z).re by rw [(show (c * z).re = (2 / γ) * z.re by simp [c, Complex.mul_re])]; exact mul_pos (show 0 < 2 / γ by positivity) hz)) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n))
      have hPow : DifferentiableAt ℂ
          (fun w => ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * w - 1)) z := by
        apply DifferentiableAt.const_cpow
        · fun_prop
        · exact Or.inl (by
            apply Complex.ofReal_ne_zero.mpr
            exact div_ne_zero hγ.ne' (by norm_num))
      change DifferentiableAt ℂ
        (fun w => Complex.Gamma (c * w) * (Complex.Gamma (1 - c * w))⁻¹ *
          ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * w - 1)) z
      exact ((DifferentiableAt.fun_comp' z (f := fun w => c * w) (g := Complex.Gamma) hGamma (by fun_prop)).mul (DifferentiableAt.fun_comp' z (f := fun w => 1 - c * w) (g := fun v => (Complex.Gamma v)⁻¹) Complex.differentiable_one_div_Gamma.differentiableAt (by fun_prop))).mul hPow
    let o : Set ℂ := {z | 0 < z.re ∧ z.re < γ / 2}
    let f : ℂ → ℂ := fun z => U (z + (2 / γ : ℂ))
    let g : ℂ → ℂ := fun z => upsilonBinvForwardMultiplier γ z * U z
    let z₀ : ℂ := (γ / 4 : ℝ)
    have hz₀ : z₀ ∈ o := by
      dsimp [z₀, o]
      constructor
      · positivity
      · linarith
    have heq : EqOn f g o := by
      intro z hz
      dsimp [f, g, o] at hz ⊢
      have hzQ : z.re < Q γ := by
        unfold Q
        have : 0 < 2 / γ := by positivity
        linarith
      calc
        U (z + (2 / γ : ℂ)) = Complex.exp (upsilonLog γ (z + (2 / γ : ℂ))) :=
          hU.2 _ (show 0 < (z + (2 / γ : ℂ)).re by rw [Complex.add_re, complex_dual_re]; exact add_pos hz.1 (by positivity)) (by rw [Complex.add_re, complex_dual_re]; unfold Q; linarith)
        _ = lFun ((2 / γ : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1) *
            Complex.exp (upsilonLog γ z) :=
          exp_upsilonLog_shift_binv hγ hγ2 hz.1 hz.2
        _ = upsilonBinvForwardMultiplier γ z * U z := by
          rw [hU.2 z hz.1 hzQ]
          simp [upsilonBinvForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc]
    intro z hz
    exact (differentiableOn_eqOn_of_open (Complex.isOpen_re_gt 0) ((convex_halfSpace_re_gt 0).isPreconnected) (by intro z hz; dsimp [f]; exact (DifferentiableAt.fun_comp' z (f := fun w => w + (2 / γ : ℂ)) (g := U) (hU.1 (z + (2 / γ : ℂ))) (by fun_prop)).differentiableWithinAt) (by intro z hz; dsimp [g]; exact (differentiableAt_upsilonBinvForwardMultiplier hz).differentiableWithinAt.mul (hU.1 z).differentiableWithinAt) ((Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (γ / 2))) (fun _ hz => hz.1) z₀ hz₀ heq) hz
  have upsilonBinvMultipliers_cancel_of_nonzero {z} (hΓ : Complex.Gamma ((2 / γ : ℂ) * z) ≠ 0) (hΓ1 : Complex.Gamma (1 - (2 / γ : ℂ) * z) ≠ 0) : upsilonBinvInverseMultiplier γ z * upsilonBinvForwardMultiplier γ z = 1 := by
    change
      (((γ / 2 : ℝ) : ℂ) ^ (-(4 / (γ : ℂ) * z - 1)) *
        Complex.Gamma (1 - (2 / γ : ℂ) * z) *
        (Complex.Gamma ((2 / γ : ℂ) * z))⁻¹) *
      (Complex.Gamma ((2 / γ : ℂ) * z) *
        (Complex.Gamma (1 - (2 / γ : ℂ) * z))⁻¹ *
        ((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1)) = 1
    rw [Complex.cpow_neg]
    calc
      _ = ((((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1)) *
            (((γ / 2 : ℝ) : ℂ) ^ (4 / (γ : ℂ) * z - 1))⁻¹) *
          (Complex.Gamma (1 - (2 / γ : ℂ) * z) *
            (Complex.Gamma (1 - (2 / γ : ℂ) * z))⁻¹) *
          (Complex.Gamma ((2 / γ : ℂ) * z) *
            (Complex.Gamma ((2 / γ : ℂ) * z))⁻¹) := by ring_nf
      _ = 1 := by simp [(show ((γ / 2 : ℂ) ^ (4 / (γ : ℂ) * z - 1)) ≠ 0 by rw [← complex_half_cast]; exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (show ((γ / 2 : ℝ) : ℂ) ≠ 0 by apply Complex.ofReal_ne_zero.mpr; exact div_ne_zero hγ.ne' (by norm_num))))), hΓ, hΓ1]
  have upsilonBinv_shift_reciprocal_on_left : ∀ z : ℂ, z.re < γ / 2 → upsilonBinvInverseMultiplier γ z * U (z + (2 / γ : ℂ)) = U z := by
    have differentiableAt_upsilonBinvInverseMultiplier {z : ℂ} (hz : z.re < γ / 2) : DifferentiableAt ℂ (upsilonBinvInverseMultiplier γ) z := by
      let c : ℂ := (2 / γ : ℂ)
      have : (2 / γ) * z.re < 1 := by
        have hmul := mul_lt_mul_of_pos_left hz (show 0 < 2 / γ by positivity)
        rw [(show (2 / γ) * (γ / 2) = 1 by field_simp [hγ.ne'])] at hmul
        exact hmul
      have hGamma := Complex.differentiableAt_Gamma (1 - c * z) (by
          intro n hn
          exact (Complex.Gamma_ne_zero_of_re_pos (show 0 < (1 - c * z).re by rw [Complex.sub_re, Complex.one_re, (show (c * z).re = (2 / γ) * z.re by simp [c, Complex.mul_re])]; linarith)) (by rw [hn]; exact Complex.Gamma_neg_nat_eq_zero n))
      have hPow : DifferentiableAt ℂ
          (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(4 / (γ : ℂ) * w - 1))) z := by
        apply DifferentiableAt.const_cpow
        · fun_prop
        · exact Or.inl (by
            apply Complex.ofReal_ne_zero.mpr
            exact div_ne_zero hγ.ne' (by norm_num))
      change DifferentiableAt ℂ
        (fun w => ((γ / 2 : ℝ) : ℂ) ^ (-(4 / (γ : ℂ) * w - 1)) *
          Complex.Gamma (1 - c * w) * (Complex.Gamma (c * w))⁻¹) z
      exact (hPow.mul (DifferentiableAt.fun_comp' z (f := fun w => 1 - c * w) (g := Complex.Gamma) hGamma (by fun_prop))).mul (DifferentiableAt.fun_comp' z (f := fun w => c * w) (g := fun v => (Complex.Gamma v)⁻¹) Complex.differentiable_one_div_Gamma.differentiableAt (by fun_prop))
    let s : Set ℂ := {z | z.re < γ / 2}
    let o : Set ℂ := {z | 0 < z.re ∧ z.re < γ / 2}
    let f : ℂ → ℂ := fun z => upsilonBinvInverseMultiplier γ z *
      U (z + (2 / γ : ℂ))
    let g : ℂ → ℂ := U
    have hsOpen := Complex.isOpen_re_lt (γ / 2)
    have hsConn := (convex_halfSpace_re_lt (γ / 2)).isPreconnected
    have hoOpen := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (γ / 2))
    have hoSub : o ⊆ s := fun _ hz => hz.2
    have hf : DifferentiableOn ℂ f s := by
      intro z hz
      dsimp [f]
      exact (differentiableAt_upsilonBinvInverseMultiplier hz).differentiableWithinAt.mul <|
        (DifferentiableAt.fun_comp' z (f := fun w => w + (2 / γ : ℂ))
          (g := U) (hU.1 (z + (2 / γ : ℂ))) (by fun_prop)).differentiableWithinAt
    have hg : DifferentiableOn ℂ g s := by
      intro z hz
      exact (hU.1 z).differentiableWithinAt
    let z₀ : ℂ := (γ / 4 : ℝ)
    have hz₀ : z₀ ∈ o := by
      dsimp [z₀, o]
      constructor
      · positivity
      · linarith
    have heq : EqOn f g o := by
      intro z hz
      dsimp [f, g, o] at hz ⊢
      have hΓ : Complex.Gamma ((2 / γ : ℂ) * z) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (by
          rw [(show ((2 / γ : ℂ) * z).re = (2 / γ) * z.re by simp)]
          exact mul_pos (by positivity) hz.1)
      have hΓ1 : Complex.Gamma (1 - (2 / γ : ℂ) * z) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (by
          have hc : 0 < 2 / γ := by positivity
          have hlt := mul_lt_mul_of_pos_left hz.2 hc
          have hcancel : (2 / γ) * (γ / 2) = 1 := by field_simp [hγ.ne']
          rw [hcancel] at hlt
          rw [Complex.sub_re, Complex.one_re, (show ((2 / γ : ℂ) * z).re = (2 / γ) * z.re by simp)]
          linarith)
      calc
        _ = upsilonBinvInverseMultiplier γ z *
            (upsilonBinvForwardMultiplier γ z * U z) := by rw [(upsilonBinv_shift_on_right z hz.1)]
        _ = U z := by rw [← mul_assoc, (upsilonBinvMultipliers_cancel_of_nonzero hΓ hΓ1), one_mul]
    intro z hz
    exact (differentiableOn_eqOn_of_open hsOpen hsConn hf hg hoOpen hoSub z₀ hz₀ heq) hz
  by_cases hzRe : 0 < z.re
  · have h := upsilonBinv_shift_on_right z hzRe
    simpa [upsilonBinvForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc] using h
  · have hzRe' : z.re ≤ 0 := le_of_not_gt hzRe
    have hrecip := upsilonBinv_shift_reciprocal_on_left z (by
      linarith)
    have hΓ1 : Complex.Gamma (1 - (2 / γ : ℂ) * z) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by
        rw [Complex.sub_re, Complex.one_re, (show ((2 / γ : ℂ) * z).re = (2 / γ) * z.re by simp)]
        have : 0 < 2 / γ := by positivity
        nlinarith)
    have hcancel := upsilonBinvMultipliers_cancel_of_nonzero (Complex.Gamma_ne_zero hz) hΓ1
    have hmulNe : upsilonBinvInverseMultiplier γ z ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hcancel
      norm_num at hcancel
    have hinv : (upsilonBinvInverseMultiplier γ z)⁻¹ =
        upsilonBinvForwardMultiplier γ z := by
      calc
        _ = (upsilonBinvInverseMultiplier γ z)⁻¹ *
            (upsilonBinvInverseMultiplier γ z * upsilonBinvForwardMultiplier γ z) := by
              rw [hcancel, mul_one]
        _ = upsilonBinvForwardMultiplier γ z := by
          rw [← mul_assoc, inv_mul_cancel₀ hmulNe, one_mul]
    calc
      U (z + 2 / γ) = (upsilonBinvInverseMultiplier γ z)⁻¹ * U z := by
        calc
          U (z + 2 / γ) =
              ((upsilonBinvInverseMultiplier γ z)⁻¹ * upsilonBinvInverseMultiplier γ z) *
                U (z + 2 / γ) := by
                  rw [inv_mul_cancel₀ hmulNe, one_mul]
          _ = (upsilonBinvInverseMultiplier γ z)⁻¹ *
              (upsilonBinvInverseMultiplier γ z * U (z + 2 / γ)) := by rw [mul_assoc]
          _ = _ := by rw [hrecip]
      _ = upsilonBinvForwardMultiplier γ z * U z := by rw [hinv]
      _ = _ := by simp [upsilonBinvForwardMultiplier, lFun, div_eq_mul_inv, mul_assoc]

end DOZZ.Proofs
