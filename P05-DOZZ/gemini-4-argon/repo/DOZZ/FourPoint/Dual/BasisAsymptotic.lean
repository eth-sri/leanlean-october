/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Reflected.Remainder
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! # Gauss endpoint estimates for dual coefficient identification

The regular basis has squared norm 1+O(|z|). Since κ<1 on the dual
window, that error vanishes after division by |z|^κ.
-/

public section

open Filter Topology Set

namespace DOZZ.Proofs



/-- The actual first Gauss basis has its required sublinear squared-norm remainder. -/
theorem dual_gauss_norm_sq_littleO {H}
    (hH : IsGaussHypergeometricFamily H) a b c
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (κ : ℝ) (hκ : κ < 1) :
    Tendsto (fun z : ℂ => (‖gaussFMinus H a b c z‖ ^ 2 - 1) / ‖z‖ ^ κ)
      (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
  have dual_gauss_regular_origin : DifferentiableAt ℂ (H a b c) 0 ∧ H a b c 0 = 1 := by
    have hchar := hH a b c hc
    refine ⟨hchar.1.differentiableAt (by apply mem_of_superset ((isOpen_lt Complex.continuous_re continuous_const : IsOpen {z : ℂ | z.re < 1}).mem_nhds (by simp)); intro z hz; exact Or.inr hz), ?_⟩
    simpa only [ordinaryHypergeometric_zero] using hchar.2 0 (by norm_num)
  have dual_normalized_norm_sq_littleO (F : ℂ → ℂ) (hF : DifferentiableAt ℂ F 0) (hzero : F 0 = 1) (κ : ℝ) (hκ : κ < 1) : Tendsto (fun z : ℂ => (‖F z‖ ^ 2 - 1) / ‖z‖ ^ κ) (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
    obtain ⟨C, hC⟩ := ((hF.restrictScalars ℝ).norm_sq ℂ).isBigO_sub.bound
    exact (isComplexLittleOAtZero_ofReal_iff κ (fun z => ‖F z‖ ^ 2 - 1)).mp
      (isComplexLittleOAtZero_of_norm_le_power hκ (by simpa only [hzero, norm_one, one_pow, sub_zero, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one] using (hC.filter_mono (nhdsWithin_le_nhds (s := {z : ℂ | z ≠ 0})))))
  obtain ⟨hd, hz⟩ := dual_gauss_regular_origin
  exact dual_normalized_norm_sq_littleO (H a b c) hd hz κ hκ

/-- The second Gauss basis has normalized squared norm tending to one on the positive ray. -/
theorem dual_gauss_plus_norm_sq_ratio {H}
    (hH : IsGaussHypergeometricFamily H) a b (c : ℝ)
    (hc : ∀ n : ℕ, (2 - (c : ℂ)) ≠ -(n : ℂ)) :
    Tendsto (fun t : ℝ => ‖gaussFPlus H a b (c : ℂ) (t : ℂ)‖ ^ 2 /
      t ^ (2 * (1 - c))) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  apply (show Tendsto (fun t : ℝ => ‖H (a - c + 1) (b - c + 1) (2 - c) (t : ℂ)‖ ^ 2) (nhdsWithin 0 (Ioi 0)) (nhds 1) by simpa only [Function.comp_def, norm_one, one_pow] using (((gaussFamily_tendsto_one_at_zero hH (a - c + 1) (b - c + 1) (2 - c) hc).comp (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_id.mono_left nhdsWithin_le_nhds) : Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 (Ioi 0)) (nhds 0))).norm.pow 2)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht0
  unfold gaussFPlus
  rw [norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  have he : (t ^ (1 - c)) ^ (2 : ℕ) = t ^ (2 * (1 - c)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul ht0.le]
    congr 1
    ring
  rw [he]
  have : t ^ (2 * (1 - c)) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  field_simp

end DOZZ.Proofs
