/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.Malmsten
import DOZZ.Upsilon.IntegralBounds
import DOZZ.Upsilon.IntegralHolomorphy
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# DOZZ Upsilon shifts on the defining strip

The strip overlap equations are proved from the defining integral, before using
its entire continuation.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ.Proofs

private noncomputable def upsilonRealIntegrand (γ z t : ℝ) : ℝ :=
  ((Q γ / 2 - z) ^ 2 * Real.exp (-t) -
      Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
        (Real.sinh (t * γ / 4) * Real.sinh (t / γ))) / t

private lemma upsilonLogIntegrand_real (γ z t : ℝ) :
    upsilonLogIntegrand γ (z : ℂ) t = (upsilonRealIntegrand γ z t : ℂ) := by
  simp [upsilonLogIntegrand, upsilonRealIntegrand]


private lemma Q_eq_b_add_inv_b {γ : ℝ} (hγ : 0 < γ) :
    Q γ = γ / 2 + (γ / 2)⁻¹ := by
  unfold Q
  field_simp [(ne_of_gt hγ)]
  ring


private noncomputable def realKernel (γ z t : ℝ) : ℝ :=
  (Real.exp (-z * t) + Real.exp (-(Q γ - z) * t) -
      2 * Real.exp (-(Q γ / 2) * t)) /
    ((1 - Real.exp (-(γ / 2) * t)) * (1 - Real.exp (-t / (γ / 2))))



private lemma upsilonRealIntegrand_eq_kernel {γ z t}
    (hγ : 0 < γ) (ht : 0 < t) :
    upsilonRealIntegrand γ z t =
      ((Q γ / 2 - z) ^ 2 * Real.exp (-t) - realKernel γ z t) / t := by
  have real_sinh_quotient_eq_realKernel {z} : Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 / (Real.sinh (t * γ / 4) * Real.sinh (t / γ)) = realKernel γ z t := by
    have real_sinh_quotient_normalized {z} : Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 / (Real.sinh (t * γ / 4) * Real.sinh (t / γ)) = (Real.exp (-z * t) + Real.exp (-(Q γ - z) * t) - 2 * Real.exp (-(Q γ / 2) * t)) / ((1 - Real.exp (-(γ / 2) * t)) * (1 - Real.exp (-t / (γ / 2)))) := by
      let b := γ / 2
      have hb : 0 < b := by dsimp [b]; positivity
      have hbne := ne_of_gt hb
      have hP₁ : 1 - Real.exp (-b * t) ≠ 0 := by
        apply ne_of_gt
        apply sub_pos.mpr
        apply Real.exp_lt_one_iff.mpr
        simpa only [neg_mul] using neg_lt_zero.mpr (mul_pos hb ht)
      have hP₂ : 1 - Real.exp (-t / b) ≠ 0 := by
        apply ne_of_gt
        apply sub_pos.mpr
        apply Real.exp_lt_one_iff.mpr
        simpa only [neg_div] using neg_lt_zero.mpr (div_pos ht hb)
      have hSinh1 : Real.sinh (b * t / 2) =
          Real.exp (b * t / 2) * (1 - Real.exp (-b * t)) / 2 := by
        rw [Real.sinh_eq]
        have he : Real.exp (-(b * t / 2)) = Real.exp (b * t / 2) * Real.exp (-b * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he]
        ring
      have hSinh2 : Real.sinh (t / (2 * b)) =
          Real.exp (t / (2 * b)) * (1 - Real.exp (-t / b)) / 2 := by
        rw [Real.sinh_eq]
        have he : Real.exp (-(t / (2 * b))) = Real.exp (t / (2 * b)) * Real.exp (-t / b) := by
          rw [← Real.exp_add]
          congr 1
          field_simp [hbne]
          ring
        rw [he]
        ring
      have hSinhNum : Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 =
          (Real.exp ((Q γ / 2 - z) * t) - 2 +
            Real.exp (-((Q γ / 2 - z) * t))) / 4 := by
        rw [Real.sinh_eq]
        have hmul : Real.exp ((Q γ / 2 - z) * (t / 2)) *
            Real.exp ((Q γ / 2 - z) * (t / 2)) =
            Real.exp ((Q γ / 2 - z) * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hmul' : Real.exp (-((Q γ / 2 - z) * (t / 2))) *
            Real.exp (-((Q γ / 2 - z) * (t / 2))) =
            Real.exp (-((Q γ / 2 - z) * t)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have : Real.exp ((Q γ / 2 - z) * (t / 2)) *
            Real.exp (-((Q γ / 2 - z) * (t / 2))) = 1 := by
          rw [← Real.exp_add]
          simp
        calc
          ((Real.exp ((Q γ / 2 - z) * (t / 2)) -
              Real.exp (-((Q γ / 2 - z) * (t / 2)))) / 2) ^ 2 =
            (Real.exp ((Q γ / 2 - z) * (t / 2)) -
              Real.exp (-((Q γ / 2 - z) * (t / 2)))) ^ 2 / 4 := by ring
          _ = (Real.exp ((Q γ / 2 - z) * (t / 2)) ^ 2 -
              2 * Real.exp ((Q γ / 2 - z) * (t / 2)) *
                Real.exp (-((Q γ / 2 - z) * (t / 2))) +
              Real.exp (-((Q γ / 2 - z) * (t / 2))) ^ 2) / 4 := by ring
          _ = (Real.exp ((Q γ / 2 - z) * t) - 2 +
              Real.exp (-((Q γ / 2 - z) * t))) / 4 := by
            rw [show Real.exp ((Q γ / 2 - z) * (t / 2)) ^ 2 =
              Real.exp ((Q γ / 2 - z) * (t / 2)) *
                Real.exp ((Q γ / 2 - z) * (t / 2)) by ring,
              show Real.exp (-((Q γ / 2 - z) * (t / 2))) ^ 2 =
              Real.exp (-((Q γ / 2 - z) * (t / 2))) *
                Real.exp (-((Q γ / 2 - z) * (t / 2))) by ring,
              hmul, hmul']
            rw [(show 2 * Real.exp ((Q γ / 2 - z) * (t / 2)) * Real.exp (-((Q γ / 2 - z) * (t / 2))) = 2 by nlinarith)]
      have hscale : Real.exp (b * t / 2) * Real.exp (t / (2 * b)) =
          Real.exp ((b + b⁻¹) * t / 2) := by
        rw [← Real.exp_add]
        congr 1
        field_simp [hbne]
      have he₂ : Real.exp ((b + b⁻¹) * t / 2) *
          Real.exp (-z * t) =
            Real.exp (((b + b⁻¹) / 2 - z) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      have he₃ : Real.exp ((b + b⁻¹) * t / 2) *
          Real.exp (-(b + b⁻¹ - z) * t) =
            Real.exp (-(((b + b⁻¹) / 2 - z) * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      have hnum :
          Real.exp (((b + b⁻¹) / 2 - z) * t) - 2 +
            Real.exp (-(((b + b⁻¹) / 2 - z) * t)) =
          Real.exp ((b + b⁻¹) * t / 2) *
            (Real.exp (-z * t) + Real.exp (-(b + b⁻¹ - z) * t) -
              2 * Real.exp (-((b + b⁻¹) / 2 * t))) := by
        calc
          _ = Real.exp ((b + b⁻¹) * t / 2) * Real.exp (-z * t) +
              Real.exp ((b + b⁻¹) * t / 2) * Real.exp (-(b + b⁻¹ - z) * t) -
              2 * (Real.exp ((b + b⁻¹) * t / 2) *
                Real.exp (-((b + b⁻¹) / 2 * t))) := by
                rw [he₂, he₃, (show Real.exp ((b + b⁻¹) * t / 2) * Real.exp (-((b + b⁻¹) / 2 * t)) = 1 by rw [← Real.exp_add]; rw [show (b + b⁻¹) * t / 2 + -((b + b⁻¹) / 2 * t) = 0 by ring, Real.exp_zero])]
                simp
                ring
          _ = _ := by ring
      have hdenom :
          Real.exp (b * t / 2) * (1 - Real.exp (-b * t)) / 2 *
            (Real.exp (t / (2 * b)) * (1 - Real.exp (-t / b)) / 2) =
          Real.exp ((b + b⁻¹) * t / 2) *
            ((1 - Real.exp (-b * t)) * (1 - Real.exp (-t / b))) / 4 := by
        calc
          _ = (Real.exp (b * t / 2) * Real.exp (t / (2 * b))) *
              ((1 - Real.exp (-b * t)) * (1 - Real.exp (-t / b))) / 4 := by ring
          _ = _ := by rw [hscale]
      rw [show γ / 2 = b by rfl,
        show t * γ / 4 = b * t / 2 by dsimp [b]; ring,
        show t / γ = t / (2 * b) by dsimp [b]; field_simp [hbne],
        hSinh1, hSinh2, hSinhNum, (show Q γ = b + b⁻¹ by dsimp [b]; exact Q_eq_b_add_inv_b hγ)]
      rw [hdenom, hnum]
      field_simp [hP₁, hP₂, Real.exp_ne_zero]
    exact real_sinh_quotient_normalized
  rw [upsilonRealIntegrand, real_sinh_quotient_eq_realKernel]


private lemma upsilonRealIntegrand_integrableOn_of_complex {γ x : ℝ}
    (hComplex : IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ (x : ℂ) t)
      (Ioi 0)) : IntegrableOn (upsilonRealIntegrand γ x) (Ioi 0) := by
  exact (IntegrableOn.iff_ofReal).2 (by apply hComplex.congr; filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact upsilonLogIntegrand_real γ x t)

private lemma upsilonLog_real_integral (γ x : ℝ) :
    upsilonLog γ (x : ℂ) =
      ((∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ x t ∂volume : ℝ) : ℂ) := by
  change ∫ t in Ioi (0 : ℝ), upsilonLogIntegrand γ (x : ℂ) t ∂volume = _
  calc
    _ = ∫ t in Ioi (0 : ℝ), (upsilonRealIntegrand γ x t : ℂ) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact upsilonLogIntegrand_real γ x t
    _ = (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ x t ∂volume : ℝ) :=
      integral_ofReal

private noncomputable def upsilonScaledShiftKernel (b z u : ℝ) : ℝ :=
  ((2 * b * z - 1) * Real.exp (-b * u) +
    (Real.exp (-(b * z) * u) - Real.exp (-(1 - b * z) * u)) /
      (1 - Real.exp (-u))) / u


private lemma exp_frullani_integrableOn {b} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))
      (Ioi 0) := by
  have hsub : IntegrableOn
      (fun u => malmstenRealIntegrand (b + 1) u - malmstenRealIntegrand b u)
      (Ioi 0) := by
    change IntegrableOn (malmstenRealIntegrand (b + 1) - malmstenRealIntegrand b)
      (Ioi 0)
    exact (malmstenRealIntegrand_integrableOn (add_pos hb one_pos)).sub (malmstenRealIntegrand_integrableOn hb)
  apply hsub.neg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change -(malmstenRealIntegrand (b + 1) u - malmstenRealIntegrand b u) = _
  rw [malmstenRealIntegrand_add_one_sub hu]
  ring

private lemma exp_frullani_integral {b} (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)) ∂volume =
      -Real.log b := by
  have hfr := Frullani.integral_Ioi_eq (by exact (show Continuous (fun u => Real.exp (-u)) by fun_prop).continuousOn.locallyIntegrableOn measurableSet_Ioi) hb one_pos (by simpa using (show ContinuousAt (fun u => Real.exp (-u)) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds) Real.tendsto_exp_neg_atTop_nhds_zero (by simpa [smul_eq_mul, one_mul] using exp_frullani_integrableOn hb)
  rw [(show ∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)) ∂volume = Real.log (1 / b) by simpa [smul_eq_mul, one_mul] using hfr), Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hb.ne', Real.log_one]
  ring




private noncomputable def upsilonBForwardFactor (γ : ℝ) (z : ℂ) : ℂ :=
  lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z)


/-- Forward strip shift from the defining integral, assuming the source integral and its
derivative are available on the full strip. This form also applies to the dual parameter. -/
theorem exp_upsilonLog_shift_b_of_integrable {γ : ℝ} (hγ : 0 < γ)
    (hDiff : DifferentiableOn ℂ (fun z => upsilonLog γ z)
      {z | 0 < z.re ∧ z.re < Q γ})
    (hInt : ∀ x : ℝ, 0 < x → x < Q γ →
      IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ (x : ℂ) t) (Ioi 0))
    {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
    Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) =
      lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
        Complex.exp (upsilonLog γ z) := by
  have upsilonBForwardFactor_differentiableAt {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (upsilonBForwardFactor γ) z := by
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
  have exp_upsilonLog_shift_b_real {z : ℝ} (hz0 : 0 < z) (hzQ : z < 2 / γ) (hI₀ : IntegrableOn (upsilonRealIntegrand γ z) (Ioi 0)) (hI₁ : IntegrableOn (upsilonRealIntegrand γ (z + γ / 2)) (Ioi 0)) : Complex.exp (upsilonLog γ ((z + γ / 2 : ℝ) : ℂ)) = lFun ((γ / 2 : ℂ) * (z : ℂ)) * ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) * Complex.exp (upsilonLog γ (z : ℂ)) := by
    have upsilonRealIntegral_shift_b : (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + γ / 2) t ∂volume) - ∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ z t ∂volume = malmstenRealH ((γ / 2) * z) - malmstenRealH (1 - (γ / 2) * z) + (1 - 2 * (γ / 2) * z) * Real.log (γ / 2) := by
      have upsilonScaledShiftKernel_eq_malmsten {b} {z} {u} (hu : 0 < u) : upsilonScaledShiftKernel b z u = malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u + (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) := by
        unfold upsilonScaledShiftKernel malmstenRealIntegrand
        field_simp [ne_of_gt hu, (show 1 - Real.exp (-u) ≠ 0 by apply ne_of_gt; exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))]
        ring_nf
      have upsilonRealIntegrand_shift_b_scaled {γ} {z} {u} (hγ : 0 < γ) (hu : 0 < u) : (γ / 2) * (upsilonRealIntegrand γ (z + γ / 2) ((γ / 2) * u) - upsilonRealIntegrand γ z ((γ / 2) * u)) = upsilonScaledShiftKernel (γ / 2) z u := by
        have upsilonRealIntegrand_shift_b_pointwise {z} {t} (ht : 0 < t) : upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t = ((2 * (γ / 2) * z - 1) * Real.exp (-t) + (Real.exp (-z * t) - Real.exp (-((γ / 2)⁻¹ - z) * t)) / (1 - Real.exp (-t / (γ / 2)))) / t := by
          have realKernel_shift_b {z} : realKernel γ (z + γ / 2) t - realKernel γ z t = (Real.exp (-((γ / 2)⁻¹ - z) * t) - Real.exp (-z * t)) / (1 - Real.exp (-t / (γ / 2))) := by
            let b := γ / 2
            have hb : 0 < b := by dsimp [b]; positivity
            have hQ : Q γ = b + b⁻¹ := by
              dsimp [b]
              exact Q_eq_b_add_inv_b hγ
            have hP₁ : 1 - Real.exp (-b * t) ≠ 0 := by
              apply ne_of_gt
              apply sub_pos.mpr
              apply Real.exp_lt_one_iff.mpr
              simpa only [neg_mul] using neg_lt_zero.mpr (mul_pos hb ht)
            have hB : Real.exp (-(Q γ - (z + b)) * t) =
                Real.exp (-(b⁻¹ - z) * t) := by
              rw [hQ]
              congr 1
              ring
            unfold realKernel
            rw [show γ / 2 = b by rfl, (show Real.exp (-(z + b) * t) = Real.exp (-z * t) * Real.exp (-b * t) by rw [show -(z + b) * t = (-z * t) + (-b * t) by ring, Real.exp_add]), hB, (show Real.exp (-(Q γ - z) * t) = Real.exp (-(b⁻¹ - z) * t) * Real.exp (-b * t) by rw [hQ, show -(b + b⁻¹ - z) * t = (-(b⁻¹ - z) * t) + (-b * t) by ring, Real.exp_add]), hQ]
            rw [div_sub_div_same, (show (Real.exp (-z * t) * Real.exp (-b * t) + Real.exp (-(b⁻¹ - z) * t) - 2 * Real.exp (-((b + b⁻¹) / 2) * t)) - (Real.exp (-z * t) + Real.exp (-(b⁻¹ - z) * t) * Real.exp (-b * t) - 2 * Real.exp (-((b + b⁻¹) / 2) * t)) = (1 - Real.exp (-b * t)) * (Real.exp (-(b⁻¹ - z) * t) - Real.exp (-z * t)) by ring), (show -(b⁻¹ - z) * t = -(t * (1 - b * z) / b) by field_simp [(ne_of_gt hb)]), mul_div_mul_left _ _ hP₁]
          have hQ :
              (Q γ / 2 - (z + γ / 2)) ^ 2 - (Q γ / 2 - z) ^ 2 =
                2 * (γ / 2) * z - 1 := by
            rw [Q_eq_b_add_inv_b hγ]
            field_simp [((show γ / 2 ≠ 0 by positivity))]
            ring
          rw [upsilonRealIntegrand_eq_kernel (γ := γ) (z := z + γ / 2) (t := t) hγ ht,
            upsilonRealIntegrand_eq_kernel (γ := γ) (z := z) (t := t) hγ ht]
          rw [(show ((Q γ / 2 - (z + γ / 2)) ^ 2 * Real.exp (-t) - realKernel γ (z + γ / 2) t) / t - ((Q γ / 2 - z) ^ 2 * Real.exp (-t) - realKernel γ z t) / t = (((Q γ / 2 - (z + γ / 2)) ^ 2 - (Q γ / 2 - z) ^ 2) * Real.exp (-t) - (realKernel γ (z + γ / 2) t - realKernel γ z t)) / t by field_simp [ne_of_gt ht]; ring), hQ, realKernel_shift_b]
          have hden : 1 - Real.exp (-t / (γ / 2)) ≠ 0 := by
            apply ne_of_gt
            apply sub_pos.mpr
            apply Real.exp_lt_one_iff.mpr
            simpa only [neg_div] using neg_lt_zero.mpr (div_pos ht (by positivity))
          field_simp [ne_of_gt ht, hden]
          ring
        let b := γ / 2
        have hb : 0 < b := by dsimp [b]; positivity
        have hbne := ne_of_gt hb
        have hden : 1 - Real.exp (-u) ≠ 0 := by
          apply ne_of_gt
          apply sub_pos.mpr
          exact Real.exp_lt_one_iff.mpr (by linarith)
        rw [upsilonRealIntegrand_shift_b_pointwise (mul_pos hb hu)]
        simp_rw [show γ / 2 = b by rfl]
        rw [(show Real.exp (-z * (b * u)) = Real.exp (-(b * z) * u) by congr 1; ring), (show Real.exp (-(b⁻¹ - z) * (b * u)) = Real.exp (-(1 - b * z) * u) by congr 1; field_simp [hbne]), (show 1 - Real.exp (-(b * u) / b) = 1 - Real.exp (-u) by congr 1; field_simp [hbne])]
        unfold upsilonScaledShiftKernel
        field_simp [ne_of_gt hu, hden]
      let b := γ / 2
      have hb : 0 < b := by dsimp [b]; positivity
      have hx1 : 0 < 1 - b * z := by
        have hmul := mul_lt_mul_of_pos_left (by rw [(show 2 / γ = b⁻¹ by dsimp [b]; field_simp [hγ.ne'])] at hzQ; exact hzQ) hb
        rw [(mul_inv_cancel₀ (ne_of_gt hb))] at hmul
        linarith
      have hscaled :
          (∫ t in Ioi (0 : ℝ),
              upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t ∂volume) =
            ∫ u in Ioi (0 : ℝ), upsilonScaledShiftKernel b z u ∂volume := by
        calc
          _ = b * ∫ u in Ioi (0 : ℝ),
              (upsilonRealIntegrand γ (z + γ / 2) (b * u) -
                upsilonRealIntegrand γ z (b * u)) ∂volume := by
            simpa [b, smul_eq_mul] using (integral_comp_mul_left_Ioi' (fun t => upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t) 0 hb).symm
          _ = ∫ u in Ioi (0 : ℝ),
              b * (upsilonRealIntegrand γ (z + γ / 2) (b * u) -
                upsilonRealIntegrand γ z (b * u)) ∂volume := by
            rw [integral_const_mul]
          _ = ∫ u in Ioi (0 : ℝ), upsilonScaledShiftKernel b z u ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            simpa [b] using
              (upsilonRealIntegrand_shift_b_scaled (γ := γ) (z := z) (u := u) hγ hu)
      have hxI := malmstenRealIntegrand_integrableOn (mul_pos hb hz0)
      have hyI := malmstenRealIntegrand_integrableOn hx1
      have hkernel :
          (∫ u in Ioi (0 : ℝ), upsilonScaledShiftKernel b z u ∂volume) =
            malmstenRealH (b * z) - malmstenRealH (1 - b * z) +
              (2 * b * z - 1) *
                (∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)) ∂volume) := by
        calc
          _ = ∫ u in Ioi (0 : ℝ),
              (malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u +
                (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            exact upsilonScaledShiftKernel_eq_malmsten hu
          _ = _ := by
            change (∫ u in Ioi (0 : ℝ),
                ((malmstenRealIntegrand (b * z) -
                  malmstenRealIntegrand (1 - b * z)) u +
                  (2 * b * z - 1) *
                    (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))) ∂volume) = _
            rw [integral_add (hxI.sub hyI) ((exp_frullani_integrableOn hb).const_mul (2 * b * z - 1))]
            change (∫ u in Ioi (0 : ℝ),
                malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u) +
              ∫ u in Ioi (0 : ℝ),
                (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) = _
            rw [integral_sub hxI hyI, integral_const_mul, exp_frullani_integral hb]
            simp [malmstenRealH]
      rw [← (show (∫ t in Ioi (0 : ℝ), (upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t) ∂volume) = (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + γ / 2) t ∂volume) - ∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ z t ∂volume by rw [integral_sub hI₁ hI₀]), hscaled, hkernel, exp_frullani_integral hb]
      ring
    let b := γ / 2
    let x := b * z
    have hb : 0 < b := by dsimp [b]; positivity
    have hx1 : 0 < 1 - x := by
      dsimp [x, b]
      have hmul := mul_lt_mul_of_pos_left hzQ (by positivity : 0 < γ / 2)
      have hcancel : (γ / 2) * (2 / γ) = 1 := by field_simp [hγ.ne']
      rw [hcancel] at hmul
      linarith
    have hlogDiff :
        upsilonLog γ ((z + γ / 2 : ℝ) : ℂ) - upsilonLog γ (z : ℂ) =
          ((malmstenRealH x - malmstenRealH (1 - x) +
            (1 - 2 * x) * Real.log b : ℝ) : ℂ) := by
      rw [upsilonLog_real_integral, upsilonLog_real_integral]
      exact_mod_cast (by convert (upsilonRealIntegral_shift_b) using 1; ring)
    have harg₁ : (γ / 2 : ℂ) * (z : ℂ) = (x : ℂ) := by
      dsimp [x, b]
      push_cast
      ring
    calc
      Complex.exp (upsilonLog γ ((z + γ / 2 : ℝ) : ℂ)) =
          Complex.exp (((malmstenRealH x - malmstenRealH (1 - x) +
            (1 - 2 * x) * Real.log b : ℝ) : ℂ) + upsilonLog γ (z : ℂ)) := by
              congr 1
              linear_combination hlogDiff
      _ = Complex.exp ((malmstenRealH x - malmstenRealH (1 - x) +
            (1 - 2 * x) * Real.log b : ℝ) : ℂ) *
            Complex.exp (upsilonLog γ (z : ℂ)) := by rw [Complex.exp_add]
      _ = _ := by rw [← Complex.ofReal_exp, (show lFun ((γ / 2 : ℂ) * (z : ℂ)) * ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) = ((Real.exp (malmstenRealH x - malmstenRealH (1 - x) + (1 - 2 * x) * Real.log b) : ℝ) : ℂ) by rw [(show lFun ((γ / 2 : ℂ) * (z : ℂ)) = ((Real.Gamma x / Real.Gamma (1 - x) : ℝ) : ℂ) by unfold lFun; rw [harg₁, (show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring), Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.ofReal_div]), (show ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) = ((b ^ (1 - 2 * x) : ℝ) : ℂ) by rw [show (γ / 2 : ℝ) = b by rfl, show (1 - γ * z : ℝ) = 1 - 2 * x by dsimp [x, b]; ring]; exact (Complex.ofReal_cpow (le_of_lt hb) (1 - 2 * x)).symm), ← Complex.ofReal_mul]; exact (congrArg Complex.ofReal (by rw [Real.exp_add, Real.exp_sub, (malmstenRealH_exp_eq_Gamma (show 0 < x by dsimp [x]; exact mul_pos hb hz0)), (malmstenRealH_exp_eq_Gamma hx1), (show Real.exp ((1 - 2 * x) * Real.log b) = b ^ (1 - 2 * x) by rw [mul_comm (1 - 2 * x) (Real.log b), ← Real.rpow_def_of_pos hb])])).symm)]
  let O : Set ℂ := {w | 0 < w.re ∧ w.re < 2 / γ}
  let T : Set ℂ := {w | 0 < w.re ∧ w.re < Q γ}
  let bC := (γ / 2 : ℂ)
  let f : ℂ → ℂ := fun w => Complex.exp (upsilonLog γ (w + bC))
  let g : ℂ → ℂ := fun w => upsilonBForwardFactor γ w *
    Complex.exp (upsilonLog γ w)
  have hrecip : 2 / γ = (γ / 2)⁻¹ := by field_simp [hγ.ne']
  have hQ := Q_eq_b_add_inv_b hγ
  have hupper : 2 / γ < Q γ := by
    rw [hQ, hrecip]
    linarith
  have hOOpen : IsOpen O := by
    change IsOpen ((Complex.re ⁻¹' Ioi (0 : ℝ)) ∩
      (Complex.re ⁻¹' Iio (2 / γ)))
    exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))
  have hOConvex : Convex ℝ O := by
    change Convex ℝ ((Complex.re ⁻¹' Ioi (0 : ℝ)) ∩
      (Complex.re ⁻¹' Iio (2 / γ)))
    exact (convex_halfSpace_re_gt 0).inter
      (convex_halfSpace_re_lt (2 / γ))
  have hOsubT : O ⊆ T := by
    intro w hw
    exact ⟨hw.1, lt_trans hw.2 hupper⟩
  have hshiftT : ∀ w : ℂ, w ∈ O → w + bC ∈ T := by
    intro w hw
    change 0 < w.re ∧ w.re < 2 / γ at hw
    have hre : (w + bC).re = w.re + γ / 2 := by simp [bC]
    change 0 < (w + bC).re ∧ (w + bC).re < Q γ
    rw [hre]
    constructor
    · linarith
    · rw [hQ]
      linarith
  have hf : DifferentiableOn ℂ f O := by
    intro w hw
    change DifferentiableWithinAt ℂ
      (fun v => Complex.exp (upsilonLog γ (v + bC))) O w
    exact differentiable_exp.differentiableAt.comp_differentiableWithinAt w
      ((hDiff.fun_comp (by intro w hw; fun_prop) hshiftT) w hw)
  have hg : DifferentiableOn ℂ g O := by
    intro w hw
    change DifferentiableWithinAt ℂ
      (fun v => upsilonBForwardFactor γ v * Complex.exp (upsilonLog γ v)) O w
    exact (upsilonBForwardFactor_differentiableAt hw.1).differentiableWithinAt.mul (differentiable_exp.differentiableAt.comp_differentiableWithinAt w ((hDiff w (hOsubT hw)).mono hOsubT))
  let x₀ := 1 / γ
  let w₀ := (x₀ : ℂ)
  have hrealEq : ∀ r : ℝ, 0 < r → r < 2 / γ → f (r : ℂ) = g (r : ℂ) := by
    intro r hr0 hrUpper
    have hI₁ := upsilonRealIntegrand_integrableOn_of_complex
      (hInt (r + γ / 2) (by positivity) (show r + γ / 2 < Q γ by rw [hQ]; linarith))
    simpa [f, g, upsilonBForwardFactor, bC] using (exp_upsilonLog_shift_b_real hr0 hrUpper (upsilonRealIntegrand_integrableOn_of_complex (hInt r hr0 (lt_trans hrUpper hupper))) hI₁)
  have hclosure : w₀ ∈ closure ({w | f w = g w} \ {w₀}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let d : ℝ := min (ε / 2) (1 / (2 * γ))
    let r := x₀ + d
    have hd : 0 < d := lt_min (by linarith) (by positivity)
    have hrUpper : r < 2 / γ := by
      have hdle : d ≤ 1 / (2 * γ) := min_le_right _ _
      dsimp [r, x₀]
      have hhalf : 1 / (2 * γ) = (1 / 2) * (1 / γ) := by
        field_simp [hγ.ne']
      calc
        1 / γ + d ≤ 1 / γ + 1 / (2 * γ) := by
          simpa [add_comm] using add_le_add_right hdle (1 / γ)
        _ = 1 / γ + (1 / 2) * (1 / γ) := by rw [hhalf]
        _ = (3 / 2) / γ := by field_simp [hγ.ne']; ring
        _ < 2 / γ := div_lt_div_of_pos_right (by norm_num) hγ
    have hrne : (r : ℂ) ≠ w₀ := by
      intro heq
      have hreal : r = x₀ := Complex.ofReal_inj.mp (by simpa [w₀] using heq)
      exact (ne_of_gt hd) (by dsimp [r] at hreal; linarith)
    have hdist : dist (r : ℂ) w₀ = d := by
      rw [dist_eq_norm, ← Complex.ofReal_sub]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [show r - x₀ = d by dsimp [r]; ring, abs_of_pos hd]
    refine ⟨(r : ℂ), ⟨hrealEq r (by dsimp [r]; positivity) hrUpper, hrne⟩, ?_⟩
    rw [dist_comm, hdist]
    have : d ≤ ε / 2 := min_le_left _ _
    linarith
  simpa [f, g, upsilonBForwardFactor, bC] using (AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure (hf.analyticOnNhd hOOpen) (hg.analyticOnNhd hOOpen) hOConvex.isPreconnected (by change 0 < w₀.re ∧ w₀.re < 2 / γ; simp only [w₀, Complex.ofReal_re]; exact ⟨(by dsimp [x₀]; positivity), (by dsimp [x₀]; exact div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) hγ)⟩) hclosure) ⟨hz0, hzQ⟩

/-- Forward strip shift, using the convergence and holomorphy results for `upsilonLog` on the
defining strip. -/
theorem exp_upsilonLog_shift_b {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
    Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) =
      lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
        Complex.exp (upsilonLog γ z) := by
  exact exp_upsilonLog_shift_b_of_integrable hγ (upsilonLog_differentiableOn hγ hγ2) (by intro x hx0 hxQ; exact upsilonLogIntegrand_integrableOn hγ hγ2 (x : ℂ) (by simpa using hx0) (by simpa using hxQ)) hz0 hzQ

end DOZZ.Proofs

end
