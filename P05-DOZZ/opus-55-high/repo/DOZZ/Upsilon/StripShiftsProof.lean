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
section
variable {γ : ℝ}
section
variable (hγ : 0 < γ)
include hγ

private lemma b_nonzero : γ / 2 ≠ 0 := by
  positivity

private lemma Q_eq_b_add_inv_b :
    Q γ = γ / 2 + (γ / 2)⁻¹ := by
  have hg := ne_of_gt hγ
  unfold Q
  ring

end

end

private lemma real_sinh_quotient_normalized {γ z t : ℝ} (hγ : 0 < γ) (ht : 0 < t) :
    Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
        (Real.sinh (t * γ / 4) * Real.sinh (t / γ)) =
      (Real.exp (-z * t) + Real.exp (-(Q γ - z) * t) -
          2 * Real.exp (-(Q γ / 2) * t)) /
        ((1 - Real.exp (-(γ / 2) * t)) *
          (1 - Real.exp (-t / (γ / 2)))) := by
  let b := γ / 2
  have hb : 0 < b := by positivity
  have hbne := ne_of_gt hb
  have hQ : Q γ = b + b⁻¹ := by
    dsimp [b]
    exact Q_eq_b_add_inv_b hγ
  have hden₁ : Real.sinh (t * γ / 4) ≠ 0 := by
    positivity
  have hden₂ : Real.sinh (t / γ) ≠ 0 := by positivity
  have hP₁ : 1 - Real.exp (-b * t) ≠ 0 := by
    apply ne_of_gt
    simp_all
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
    have hcross₁ : Real.exp ((Q γ / 2 - z) * (t / 2)) *
        Real.exp (-((Q γ / 2 - z) * (t / 2))) = 1 := by
      rw [← Real.exp_add]
      simp
    have hcross₂ : Real.exp (-((Q γ / 2 - z) * (t / 2))) *
        Real.exp ((Q γ / 2 - z) * (t / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      ((Real.exp _ -
          Real.exp _) / 2) ^ 2 =
        (Real.exp _ -
          Real.exp (-((Q γ / 2 - z) * (t / 2)))) ^ 2 / 4 := by ring
      _ = (Real.exp _ ^ 2 -
          2 * Real.exp ((Q γ / 2 - z) * (t / 2)) *
            Real.exp (-((Q γ / 2 - z) * (t / 2))) +
          Real.exp (-((Q γ / 2 - z) * (t / 2))) ^ 2) / 4 := by ring
      _ = (Real.exp ((Q γ / 2 - z) * t) - 2 +
          Real.exp (-((Q γ / 2 - z) * t))) / 4 := by
        rw [show Real.exp ((Q γ / 2 - z) * (t / 2)) ^ 2 =
          Real.exp _ *
            Real.exp _ by ring,
          show Real.exp (-((Q γ / 2 - z) * (t / 2))) ^ 2 =
          Real.exp _ *
            Real.exp _ by ring,
          hmul, hmul']
        have hab := hcross₁
        have hmul₂ : 2 * Real.exp ((Q γ / 2 - z) * (t / 2)) *
            Real.exp (-((Q γ / 2 - z) * (t / 2))) = 2 := by nlinarith
        rw [hmul₂]
  have hscale : Real.exp (b * t / 2) * Real.exp (t / (2 * b)) =
      Real.exp ((b + b⁻¹) * t / 2) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hbne]
  have he₁ : Real.exp ((b + b⁻¹) * t / 2) *
      Real.exp (-((b + b⁻¹) / 2 * t)) = 1 := by
    rw [← Real.exp_add]
    rw [show (b + b⁻¹) * t / 2 + -((b + b⁻¹) / 2 * t) = 0 by ring,
      Real.exp_zero]
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
      _ = Real.exp _ * Real.exp _ +
          Real.exp ((b + b⁻¹) * t / 2) * Real.exp (-(b + b⁻¹ - z) * t) -
          2 * (Real.exp ((b + b⁻¹) * t / 2) *
            Real.exp (-((b + b⁻¹) / 2 * t))) := by
            rw [he₂, he₃, he₁]
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
      _ = _ := by simp_all
  rw [show γ / 2 = b by rfl,
    show t * γ / 4 = b * t / 2 by ring,
    show t / γ = t / (2 * b) by ring,
    hSinh1, hSinh2, hSinhNum, hQ]
  rw [hdenom, hnum]
  field_simp [hP₁, hP₂, Real.exp_ne_zero]

private noncomputable def realKernel (γ z t : ℝ) : ℝ :=
  (Real.exp (-z * t) + Real.exp (-(Q γ - z) * t) -
      2 * Real.exp (-(Q γ / 2) * t)) /
    ((1 - Real.exp (-(γ / 2) * t)) * (1 - Real.exp (-t / (γ / 2))))
section
variable {γ z t : ℝ}
section
variable (hγ : 0 < γ) (ht : 0 < t)
include hγ ht

private lemma real_sinh_quotient_eq_realKernel :
    Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
        (Real.sinh (t * γ / 4) * Real.sinh (t / γ)) = realKernel γ z t := real_sinh_quotient_normalized hγ ht

private lemma realKernel_shift_b :
    realKernel γ (z + γ / 2) t - realKernel γ z t =
      (Real.exp (-((γ / 2)⁻¹ - z) * t) - Real.exp (-z * t)) /
        (1 - Real.exp (-t / (γ / 2))) := by
  let b := γ / 2
  have hb : 0 < b := by positivity
  have hQ : Q γ = b + b⁻¹ := by
    dsimp [b]
    exact Q_eq_b_add_inv_b hγ
  have hP₁ : 1 - Real.exp (-b * t) ≠ 0 := by
    apply ne_of_gt
    simp_all
  have hP₂ : 1 - Real.exp (-t / b) ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    simpa only [neg_div] using neg_lt_zero.mpr (div_pos ht hb)
  have hP :=
    mul_ne_zero hP₁ hP₂
  have hA : Real.exp (-(z + b) * t) = Real.exp (-z * t) * Real.exp (-b * t) := by
    rw [show -(z + b) * t = (-z * t) + (-b * t) by ring, Real.exp_add]
  have hB : Real.exp (-(Q γ - (z + b)) * t) =
      Real.exp (-(b⁻¹ - z) * t) := by
    grind
  have hC : Real.exp (-(Q γ - z) * t) =
      Real.exp (-(b⁻¹ - z) * t) * Real.exp (-b * t) := by
    rw [hQ, show -(b + b⁻¹ - z) * t = (-(b⁻¹ - z) * t) + (-b * t) by ring,
      Real.exp_add]
  unfold realKernel
  rw [show γ / 2 = b by rfl, hA, hB, hC, hQ]
  have hnum :
      (Real.exp (-z * t) * Real.exp (-b * t) +
          Real.exp (-(b⁻¹ - z) * t) -
          2 * Real.exp (-((b + b⁻¹) / 2) * t)) -
        (Real.exp (-z * t) +
          Real.exp (-(b⁻¹ - z) * t) * Real.exp (-b * t) -
          2 * Real.exp (-((b + b⁻¹) / 2) * t)) =
      (1 - Real.exp (-b * t)) *
        (Real.exp (-(b⁻¹ - z) * t) - Real.exp (-z * t)) := by ring
  have hExp : -(b⁻¹ - z) * t = -(t * (1 - b * z) / b) := by
    field_simp [(ne_of_gt hb)]
  rw [div_sub_div_same, hnum, hExp, mul_div_mul_left _ _ hP₁]

private lemma upsilonRealIntegrand_eq_kernel :
    upsilonRealIntegrand γ z t =
      ((Q γ / 2 - z) ^ 2 * Real.exp (-t) - realKernel γ z t) / t := by
  rw [upsilonRealIntegrand, real_sinh_quotient_eq_realKernel hγ ht]

private lemma upsilonRealIntegrand_shift_b_pointwise :
    upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t =
      ((2 * (γ / 2) * z - 1) * Real.exp (-t) +
        (Real.exp (-z * t) - Real.exp (-((γ / 2)⁻¹ - z) * t)) /
          (1 - Real.exp (-t / (γ / 2)))) / t := by
  have hb := b_nonzero hγ
  have hQ :
      (Q γ / 2 - (z + γ / 2)) ^ 2 - (Q γ / 2 - z) ^ 2 =
        2 * (γ / 2) * z - 1 := by
    rw [Q_eq_b_add_inv_b hγ]
    grind
  rw [upsilonRealIntegrand_eq_kernel (γ := γ) (z := z + γ / 2) (t := t) hγ ht,
    upsilonRealIntegrand_eq_kernel (γ := γ) (z := z) (t := t) hγ ht]
  have hsource :
      ((Q γ / 2 - (z + γ / 2)) ^ 2 * Real.exp (-t) - realKernel γ (z + γ / 2) t) / t -
        ((Q γ / 2 - z) ^ 2 * Real.exp (-t) - realKernel γ z t) / t =
      (((Q γ / 2 - (z + γ / 2)) ^ 2 - (Q γ / 2 - z) ^ 2) * Real.exp (-t) -
        (realKernel γ (z + γ / 2) t - realKernel γ z t)) / t := by
    ring
  rw [hsource, hQ, realKernel_shift_b hγ ht]
  ring

end

end

private lemma upsilonRealIntegrand_integrableOn_of_complex {γ x : ℝ}
    (hComplex : IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ (x : ℂ) t)
      (Ioi 0)) : IntegrableOn (upsilonRealIntegrand γ x) (Ioi 0) := by
  have hCast : IntegrableOn (fun t => (upsilonRealIntegrand γ x t : ℂ))
      (Ioi 0) := by
    apply hComplex.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact upsilonLogIntegrand_real γ x t
  exact (IntegrableOn.iff_ofReal).2 hCast

private lemma upsilonLog_real_integral (γ x : ℝ) :
    upsilonLog γ (x : ℂ) =
      ((∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ x t ∂volume : ℝ) : ℂ) := by
  calc
    _ = ∫ t in Ioi 0, (upsilonRealIntegrand γ x t : ℂ) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact upsilonLogIntegrand_real γ x t
    _ = (∫ t in Ioi 0, upsilonRealIntegrand γ x t ∂volume : ℝ) :=
      integral_ofReal

private noncomputable def upsilonScaledShiftKernel (b z u : ℝ) : ℝ :=
  ((2 * b * z - 1) * Real.exp (-b * u) +
    (Real.exp (-(b * z) * u) - Real.exp (-(1 - b * z) * u)) /
      (1 - Real.exp (-u))) / u

private lemma upsilonRealIntegrand_shift_b_scaled {γ z u : ℝ}
    (hγ : 0 < γ) (hu : 0 < u) :
    (γ / 2) * (upsilonRealIntegrand γ (z + γ / 2) ((γ / 2) * u) -
      upsilonRealIntegrand γ z ((γ / 2) * u)) =
      upsilonScaledShiftKernel (γ / 2) z u := by
  let b := γ / 2
  have hb : 0 < b := by positivity
  have hbne := ne_of_gt hb
  have hden : 1 - Real.exp (-u) ≠ 0 := by
    apply ne_of_gt
    simp_all
  have he₁ : Real.exp (-z * (b * u)) = Real.exp (-(b * z) * u) := by
    ring
  have he₂ : Real.exp (-(b⁻¹ - z) * (b * u)) =
      Real.exp (-(1 - b * z) * u) := by
    field_simp
  have hdenom : 1 - Real.exp (-(b * u) / b) = 1 - Real.exp (-u) := by
    field_simp
  rw [upsilonRealIntegrand_shift_b_pointwise hγ (mul_pos hb hu)]
  simp_rw [show γ / 2 = b by rfl]
  rw [he₁, he₂, hdenom]
  unfold upsilonScaledShiftKernel
  field_simp
section
variable {b : ℝ}
section
variable (hb : 0 < b)
include hb

private lemma exp_frullani_integrableOn :
    IntegrableOn (fun u : ℝ => u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))
      (Ioi 0) := by
  have hsub : IntegrableOn
      (fun u : ℝ => malmstenRealIntegrand (b + 1) u - malmstenRealIntegrand b u)
      (Ioi 0) := by
    change IntegrableOn (malmstenRealIntegrand (b + 1) - malmstenRealIntegrand b)
      (Ioi 0)
    exact (malmstenRealIntegrand_integrableOn (add_pos hb one_pos)).sub (malmstenRealIntegrand_integrableOn hb)
  apply hsub.neg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change -(malmstenRealIntegrand _ u - malmstenRealIntegrand b u) = _
  rw [malmstenRealIntegrand_add_one_sub hu]
  ring

private lemma exp_frullani_integral :
    ∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)) ∂volume =
      -Real.log b := by
  have hloc : LocallyIntegrableOn (fun u => Real.exp (-u)) (Ioi 0) := by
    have hcont : Continuous (fun u => Real.exp (-u)) := by fun_prop
    exact hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : Tendsto (fun u => Real.exp (-u)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun u => Real.exp (-u)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hinf :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hint : IntegrableOn
      (fun u => u⁻¹ • (Real.exp (-(b * u)) - Real.exp (-(1 * u)))) (Ioi 0) := by
    simpa [smul_eq_mul, one_mul] using exp_frullani_integrableOn hb
  have hfr := Frullani.integral_Ioi_eq hloc hb one_pos hzero hinf hint
  simp_all

end

end

private lemma upsilonScaledShiftKernel_eq_malmsten {b z u : ℝ} (hu : 0 < u) :
    upsilonScaledShiftKernel b z u =
      malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u +
        (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) := by
  have hden : 1 - Real.exp (-u) ≠ 0 := by
    apply ne_of_gt
    simp_all
  unfold upsilonScaledShiftKernel malmstenRealIntegrand
  ring

private lemma upsilonRealIntegral_shift_b {γ z : ℝ}
    (hγ : 0 < γ) (hz0 : 0 < z) (hzQ : z < 2 / γ)
    (hI₀ : IntegrableOn (upsilonRealIntegrand γ z) (Ioi 0))
    (hI₁ : IntegrableOn (upsilonRealIntegrand γ (z + γ / 2)) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + γ / 2) t ∂volume) -
        ∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ z t ∂volume =
      malmstenRealH ((γ / 2) * z) - malmstenRealH (1 - (γ / 2) * z) +
        (1 - 2 * (γ / 2) * z) * Real.log (γ / 2) := by
  let b := γ / 2
  have hb : 0 < b := by positivity
  have hQ : Q γ = b + b⁻¹ := by
    dsimp [b]
    exact Q_eq_b_add_inv_b hγ
  have hzQb : z < b⁻¹ := by
    aesop
  have hzQstrip : z < Q γ := by linarith
  have hzShift0 : 0 < z + b := by positivity
  have hzShiftQ : z + b < Q γ := by
    linarith
  have hx1 : 0 < 1 - b * z := by
    have hmul := mul_lt_mul_of_pos_left hzQb hb
    grind
  have hscaled :
      (∫ t in Ioi 0,
          upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t ∂volume) =
        ∫ u in Ioi 0, upsilonScaledShiftKernel b z u ∂volume := by
    calc
      _ = b * ∫ u in Ioi 0,
          (upsilonRealIntegrand γ (z + γ / 2) (b * u) -
            upsilonRealIntegrand γ z (b * u)) ∂volume := by
        have hchange := integral_comp_mul_left_Ioi'
          (fun t : ℝ => upsilonRealIntegrand γ (z + γ / 2) t -
            upsilonRealIntegrand γ z t) 0 hb
        simp_all
      _ = ∫ u in Ioi 0,
          b * (upsilonRealIntegrand γ (z + γ / 2) (b * u) -
            upsilonRealIntegrand γ z (b * u)) ∂volume := by
        rw [integral_const_mul]
      _ = ∫ u in Ioi 0, upsilonScaledShiftKernel b z u ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        simpa [b] using
          (upsilonRealIntegrand_shift_b_scaled (γ := γ) (z := z) (u := u) hγ hu)
  have hsub :
      (∫ t in Ioi 0,
          (upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t) ∂volume) =
        (∫ t in Ioi 0, upsilonRealIntegrand γ (z + γ / 2) t ∂volume) -
          ∫ t in Ioi 0, upsilonRealIntegrand γ z t ∂volume := by
    rw [integral_sub hI₁ hI₀]
  have hxI := malmstenRealIntegrand_integrableOn (mul_pos hb hz0)
  have hyI := malmstenRealIntegrand_integrableOn hx1
  have hkernel :
      (∫ u in Ioi 0, upsilonScaledShiftKernel b z u ∂volume) =
        malmstenRealH (b * z) - malmstenRealH (1 - b * z) +
          (2 * b * z - 1) *
            (∫ u in Ioi 0, u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)) ∂volume) := by
    calc
      _ = ∫ u in Ioi 0,
          (malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u +
            (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))) ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        exact upsilonScaledShiftKernel_eq_malmsten hu
      _ = _ := by
        change (∫ u in Ioi 0,
            ((malmstenRealIntegrand (b * z) -
              malmstenRealIntegrand (1 - b * z)) u +
              (2 * b * z - 1) *
                (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))) ∂volume) = _
        rw [integral_add (hxI.sub hyI) ((exp_frullani_integrableOn hb).const_mul (2 * b * z - 1))]
        change (∫ u in Ioi 0,
            malmstenRealIntegrand _ u - malmstenRealIntegrand _ u) +
          ∫ u in Ioi 0,
            (2 * b * z - 1) * (u⁻¹ * (Real.exp _ - Real.exp (-u))) = _
        rw [integral_sub hxI hyI, integral_const_mul, exp_frullani_integral hb]
        simp [malmstenRealH]
  rw [← hsub, hscaled, hkernel, exp_frullani_integral hb]
  ring

private lemma exp_upsilonLog_shift_b_real {γ : ℝ} (hγ : 0 < γ)
    {z : ℝ} (hz0 : 0 < z) (hzQ : z < 2 / γ)
    (hI₀ : IntegrableOn (upsilonRealIntegrand γ z) (Ioi 0))
    (hI₁ : IntegrableOn (upsilonRealIntegrand γ (z + γ / 2)) (Ioi 0)) :
    Complex.exp (upsilonLog γ ((z + γ / 2 : ℝ) : ℂ)) =
      lFun ((γ / 2 : ℂ) * (z : ℂ)) *
        ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) *
        Complex.exp (upsilonLog γ (z : ℂ)) := by
  let b := γ / 2
  let x := b * z
  have hb : 0 < b := by positivity
  have hx0 : 0 < x := by positivity
  have hx1 : 0 < 1 - x := by
    dsimp [x, b]
    have hmul := mul_lt_mul_of_pos_left hzQ (by positivity : 0 < γ / 2)
    grind
  have hlogDiff :
      upsilonLog γ ((z + γ / 2 : ℝ) : ℂ) - upsilonLog γ (z : ℂ) =
        ((malmstenRealH x - malmstenRealH (1 - x) +
          (1 - 2 * x) * Real.log b : ℝ) : ℂ) := by
    rw [upsilonLog_real_integral, upsilonLog_real_integral]
    have hreal := upsilonRealIntegral_shift_b hγ hz0 hzQ hI₀ hI₁
    have hconvert :
        (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + γ / 2) t ∂volume) -
          ∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ z t ∂volume =
        malmstenRealH x - malmstenRealH (1 - x) + (1 - 2 * x) * Real.log b := by
      grind
    exact_mod_cast hconvert
  have hRealExp :
      Real.exp (malmstenRealH x - malmstenRealH (1 - x) +
          (1 - 2 * x) * Real.log b) =
        Real.Gamma x / Real.Gamma (1 - x) * b ^ (1 - 2 * x) := by
    have hpow : Real.exp ((1 - 2 * x) * Real.log b) = b ^ (1 - 2 * x) := by
      rw [mul_comm _ (Real.log b), ← Real.rpow_def_of_pos hb]
    have hgamma₁' : Real.exp (malmstenRealH x) = Real.Gamma x := (malmstenRealH_exp_eq_Gamma hx0)
    have hgamma₂' : Real.exp (malmstenRealH (1 - x)) = Real.Gamma (1 - x) := (malmstenRealH_exp_eq_Gamma hx1)
    rw [Real.exp_add, Real.exp_sub, hgamma₁', hgamma₂', hpow]
  have harg₁ : (γ / 2 : ℂ) * (z : ℂ) = (x : ℂ) := by
    dsimp [x, b]
    push_cast
    ring
  have harg₂ : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    push_cast
    ring
  have hLfun : lFun ((γ / 2 : ℂ) * (z : ℂ)) =
      ((Real.Gamma x / Real.Gamma (1 - x) : ℝ) : ℂ) := by
    unfold lFun
    rw [harg₁, harg₂, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      Complex.ofReal_div]
  have hpower :
      ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) =
        ((b ^ (1 - 2 * x) : ℝ) : ℂ) := by
    rw [show (γ / 2 : ℝ) = b by rfl,
      show (1 - γ * z : ℝ) = 1 - 2 * x by ring]
    exact (Complex.ofReal_cpow (le_of_lt hb) _).symm
  have hfactor :
    lFun ((γ / 2 : ℂ) * (z : ℂ)) *
        ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) =
      ((Real.exp (malmstenRealH x - malmstenRealH (1 - x) +
        (1 - 2 * x) * Real.log b) : ℝ) : ℂ) := by
    rw [hLfun, hpower]
    rw [← Complex.ofReal_mul]
    exact (congrArg Complex.ofReal hRealExp).symm
  calc
    Complex.exp (upsilonLog γ ((z + γ / 2 : ℝ) : ℂ)) =
        Complex.exp (((malmstenRealH x - malmstenRealH _ +
          (1 - 2 * x) * Real.log b : ℝ) : ℂ) + upsilonLog γ (z : ℂ)) := by
            congr 1
            linear_combination hlogDiff
    _ = Complex.exp ((malmstenRealH x - malmstenRealH _ +
          (1 - 2 * x) * Real.log b : ℝ) : ℂ) *
          Complex.exp (upsilonLog γ (z : ℂ)) := by rw [Complex.exp_add]
    _ = _ := by rw [← Complex.ofReal_exp, hfactor]

private noncomputable def upsilonBForwardFactor (γ : ℝ) (z : ℂ) : ℂ :=
  lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z)
section
variable {γ : ℝ}
section
variable (hγ : 0 < γ)
include hγ

private lemma upsilonBForwardFactor_differentiableAt {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (upsilonBForwardFactor γ) z := by
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
  have hGammaComp : DifferentiableAt ℂ
      (fun w => Complex.Gamma (b * w)) z := by
    fun_prop
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

/-- Forward strip shift from the defining integral, assuming the source integral and its
derivative are available on the full strip. This form also applies to the dual parameter. -/
theorem exp_upsilonLog_shift_b_of_integrable (hDiff : DifferentiableOn ℂ (fun z => upsilonLog γ z)
      {z | 0 < z.re ∧ z.re < Q γ})
    (hInt : ∀ x : ℝ, 0 < x → x < Q γ →
      IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ (x : ℂ) t) (Ioi 0))
    {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
    Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) =
      lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
        Complex.exp (upsilonLog γ z) := by
  let O : Set ℂ := {w | 0 < w.re ∧ w.re < 2 / γ}
  let T : Set ℂ := {w | 0 < w.re ∧ w.re < Q γ}
  let bC : ℂ := (γ / 2)
  let f : ℂ → ℂ := fun w => Complex.exp (upsilonLog γ (w + bC))
  let g : ℂ → ℂ := fun w => upsilonBForwardFactor γ w *
    Complex.exp (upsilonLog γ w)
  have hb : 0 < γ / 2 := by positivity
  have hrecip : 2 / γ = (γ / 2)⁻¹ := by simp
  have hQ := Q_eq_b_add_inv_b hγ
  have hupper : 2 / γ < Q γ := by
    linarith
  have hOOpen : IsOpen O := by
    change IsOpen ((Complex.re ⁻¹' Ioi 0) ∩
      (Complex.re ⁻¹' Iio _))
    exact (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))
  have hOConvex : Convex ℝ O := by
    change Convex ℝ ((Complex.re ⁻¹' Ioi 0) ∩
      (Complex.re ⁻¹' Iio _))
    exact (convex_halfSpace_re_gt 0).inter
      (convex_halfSpace_re_lt _)
  have hOsubT : O ⊆ T := by
    intro w hw
    exact ⟨hw.1, lt_trans hw.2 hupper⟩
  have hshiftT : ∀ w : ℂ, w ∈ O → w + bC ∈ T := by
    intro w hw
    change 0 < w.re ∧ w.re < 2 / γ at hw
    have hre : (w + bC).re = w.re + γ / 2 := by simp [bC]
    change 0 < (w + bC).re ∧ (w + bC).re < Q γ
    constructor <;> linarith
  have htrans : DifferentiableOn ℂ (fun w => w + bC) O := by
    intro w hw
    fun_prop
  have hshiftLog :=
    hDiff.fun_comp htrans hshiftT
  have hf : DifferentiableOn ℂ f O := by
    intro w hw
    change DifferentiableWithinAt ℂ
      (fun v => Complex.exp _) O w
    exact differentiable_exp.differentiableAt.comp_differentiableWithinAt w
      (hshiftLog w hw)
  have hg : DifferentiableOn ℂ g O := by
    intro w hw
    change DifferentiableWithinAt ℂ
      (fun v => upsilonBForwardFactor γ v * Complex.exp _) O w
    have hlog := (hDiff w (hOsubT hw)).mono hOsubT
    have hexp := differentiable_exp.differentiableAt.comp_differentiableWithinAt w hlog
    exact (upsilonBForwardFactor_differentiableAt hγ hw.1).differentiableWithinAt.mul hexp
  let x₀ : ℝ := 1 / γ
  let w₀ : ℂ := x₀
  have hx₀ : 0 < x₀ := by positivity
  have hx₀upper : x₀ < 2 / γ := by
    exact div_lt_div_of_pos_right (by norm_num) hγ
  have hw₀ : w₀ ∈ O := by
    change 0 < w₀.re ∧ w₀.re < 2 / γ
    exact ⟨hx₀, hx₀upper⟩
  have hrealEq : ∀ r : ℝ, 0 < r → r < 2 / γ → f r = g r := by
    intro r hr0 hrUpper
    have hrQ := lt_trans hrUpper hupper
    have hrShift0 : 0 < r + γ / 2 := by positivity
    have hrShiftQ : r + γ / 2 < Q γ := by
      have hrUpper' : r < (γ / 2)⁻¹ := by
        calc
          r < 2 / γ := hrUpper
          _ = (γ / 2)⁻¹ := hrecip
      linarith
    have hI₀ := upsilonRealIntegrand_integrableOn_of_complex (hInt r hr0 hrQ)
    have hI₁ := upsilonRealIntegrand_integrableOn_of_complex
      (hInt (r + γ / 2) hrShift0 hrShiftQ)
    simpa [f, g, upsilonBForwardFactor, bC] using (exp_upsilonLog_shift_b_real hγ hr0 hrUpper hI₀ hI₁)
  have hclosure : w₀ ∈ closure ({w | f w = g w} \ {w₀}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let d := min (ε / 2) (1 / (2 * γ))
    let r := x₀ + d
    have hd : 0 < d := lt_min (by linarith) (by positivity)
    have hr0 : 0 < r := by positivity
    have hrUpper : r < 2 / γ := by
      have hdle : d ≤ 1 / (2 * γ) := min_le_right ..
      have hγ0 : 0 < 1 / γ := by positivity
      have hhalf : 1 / (2 * γ) = (1 / 2) * (1 / γ) := by
        field_simp [hγ.ne']
      calc
        1 / γ + d ≤ 1 / γ + 1 / (2 * γ) := by
          simpa [add_comm] using add_le_add_right hdle (1 / γ)
        _ = 1 / γ + (1 / 2) * (1 / γ) := by linarith
        _ = (3 / 2) / γ := by ring
        _ < 2 / γ := div_lt_div_of_pos_right (by norm_num) hγ
    have hrne : r ≠ w₀ := by
      intro heq
      have hreal := Complex.ofReal_inj.mp (by simpa [w₀] using heq)
      exact (ne_of_gt hd) (by linarith)
    have hdist : dist (r : ℂ) w₀ = d := by
      rw [dist_eq_norm, ← Complex.ofReal_sub]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [show r - x₀ = d by linarith, abs_of_pos hd]
    refine ⟨(r : ℂ), ⟨hrealEq r hr0 hrUpper, hrne⟩, ?_⟩
    rw [dist_comm, hdist]
    have hdε : d ≤ ε / 2 := min_le_left ..
    linarith
  have hgA := hg.analyticOnNhd hOOpen
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
    (hf.analyticOnNhd hOOpen) hgA hOConvex.isPreconnected hw₀ hclosure
  have hz : z ∈ O := ⟨hz0, hzQ⟩
  simpa [f, g, upsilonBForwardFactor, bC] using hEqOn hz

/-- Forward strip shift, using the convergence and holomorphy results for `upsilonLog` on the
defining strip. -/
theorem exp_upsilonLog_shift_b (hγ2 : γ < 2)
    {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
    Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) =
      lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
        Complex.exp (upsilonLog γ z) := by
  have hInt : ∀ x : ℝ, 0 < x → x < Q γ →
      IntegrableOn (upsilonLogIntegrand γ x) (Ioi 0) := by
    intro x hx0 hxQ
    exact upsilonLogIntegrand_integrableOn hγ hγ2 x (by assumption)
      (by assumption)
  exact exp_upsilonLog_shift_b_of_integrable hγ (upsilonLog_differentiableOn hγ hγ2) hInt hz0 hzQ

end

end

end DOZZ.Proofs

end
