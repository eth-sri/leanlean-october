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
import Mathlib.Tactic

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

private lemma b_nonzero {γ : ℝ} (hγ : 0 < γ) : γ / 2 ≠ 0 := by
  positivity

private lemma Q_eq_b_add_inv_b {γ : ℝ} (hγ : 0 < γ) :
    Q γ = γ / 2 + (γ / 2)⁻¹ := by
  have hg  := ne_of_gt hγ
  unfold Q
  field_simp [hg]
  ring

variable {γ z t : ℝ} (hγ : 0 < γ) (ht : 0 < t)

include γ z t hγ ht
private lemma real_sinh_quotient_normalized  :
    Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
        (Real.sinh (t * γ / 4) * Real.sinh (t / γ)) =
      (Real.exp (-z * t) + Real.exp (-(Q γ - z) * t) -
          2 * Real.exp (-(Q γ / 2) * t)) /
        ((1 - Real.exp (-(γ / 2) * t)) *
          (1 - Real.exp (-t / (γ / 2)))) := by
  let b  := γ / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbne  := ne_of_gt hb
  have hQ : Q γ = b + b⁻¹ := Q_eq_b_add_inv_b hγ
  have hden₁ : Real.sinh (t * γ / 4) ≠ 0 := by
    continuity
  have hden₂  := (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
  have hP₁ : 1 - Real.exp (-b * t) ≠ 0 := by
    apply ne_of_gt
    simp_all
  have hP₂ : 1 - Real.exp (-t / b) ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    field_simp <;> nlinarith
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
    grind
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
  grind

private noncomputable def realKernel (γ z t : ℝ) : ℝ :=
  (Real.exp (-z * t) + Real.exp (-(Q γ - z) * t) -
      2 * Real.exp (-(Q γ / 2) * t)) /
    ((1 - Real.exp (-(γ / 2) * t)) * (1 - Real.exp (-t / (γ / 2))))


private lemma real_sinh_quotient_eq_realKernel  :
    Real.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
        (Real.sinh (t * γ / 4) * Real.sinh (t / γ)) = realKernel γ z t := real_sinh_quotient_normalized hγ ht


private lemma realKernel_shift_b  :
    realKernel γ (z + γ / 2) t - realKernel γ z t =
      (Real.exp (-((γ / 2)⁻¹ - z) * t) - Real.exp (-z * t)) /
        (1 - Real.exp (-t / (γ / 2))) := by
  let b  := γ / 2
  have hb : 0 < b := by dsimp [b]; positivity

  have hQ : Q γ = b + b⁻¹ := Q_eq_b_add_inv_b hγ
  have hP₁ : 1 - Real.exp (-b * t) ≠ 0 := by
    apply ne_of_gt
    simp_all
  have hP₂ : 1 - Real.exp (-t / b) ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    field_simp <;> nlinarith
  have hP  :=
    mul_ne_zero hP₁ hP₂
  have hA : Real.exp (-(z + b) * t) = Real.exp (-z * t) * Real.exp (-b * t) := by
    rw [show -(z + b) * t = (-z * t) + (-b * t) by ring, Real.exp_add]
  have hB : Real.exp (-(Q γ - (z + b)) * t) =
      Real.exp (-(b⁻¹ - z) * t) := by
    rw [hQ]
    congr 1
    ring
  have hC : Real.exp (-(Q γ - z) * t) =
      Real.exp (-(b⁻¹ - z) * t) * Real.exp (-b * t) := by
    rw [hQ, show -(b + b⁻¹ - z) * t = (-(b⁻¹ - z) * t) + (-b * t) by ring,
      Real.exp_add]
  unfold realKernel
  grind


private lemma upsilonRealIntegrand_eq_kernel  :
    upsilonRealIntegrand γ z t =
      ((Q γ / 2 - z) ^ 2 * Real.exp (-t) - realKernel γ z t) / t := by
  rw [upsilonRealIntegrand, real_sinh_quotient_eq_realKernel hγ ht]


private lemma upsilonRealIntegrand_shift_b_pointwise  :
    upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t =
      ((2 * (γ / 2) * z - 1) * Real.exp (-t) +
        (Real.exp (-z * t) - Real.exp (-((γ / 2)⁻¹ - z) * t)) /
          (1 - Real.exp (-t / (γ / 2)))) / t := by
  have hb  := b_nonzero hγ
  have hQ :
      (Q γ / 2 - (z + γ / 2)) ^ 2 - (Q γ / 2 - z) ^ 2 =
        2 * (γ / 2) * z - 1 := by
    rw [Q_eq_b_add_inv_b hγ]
    field_simp [hb]
    ring
  rw [upsilonRealIntegrand_eq_kernel (γ := γ) (z := z + γ / 2) (t := t) hγ ht,
    upsilonRealIntegrand_eq_kernel (γ := γ) (z := z) (t := t) hγ ht]
  have hsource :
      ((Q γ / 2 - (z + γ / 2)) ^ 2 * Real.exp (-t) - realKernel γ (z + γ / 2) t) / t -
        ((Q γ / 2 - z) ^ 2 * Real.exp (-t) - realKernel γ z t) / t =
      (((Q γ / 2 - (z + γ / 2)) ^ 2 - (Q γ / 2 - z) ^ 2) * Real.exp (-t) -
        (realKernel γ (z + γ / 2) t - realKernel γ z t)) / t := by
    field_simp [ne_of_gt ht]
    ring
  rw [hsource, hQ, realKernel_shift_b hγ ht]
  ring
omit γ z t hγ ht


private lemma upsilonRealIntegrand_integrableOn_of_complex {γ x : ℝ}
    (hComplex : IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ (x : ℂ) t)
      (Ioi 0)) : IntegrableOn (upsilonRealIntegrand γ x) (Ioi 0) := by
  have hCast : IntegrableOn (fun t : ℝ => (upsilonRealIntegrand γ x t : ℂ))
      (Ioi 0) := by
    apply hComplex.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact upsilonLogIntegrand_real γ x t
  exact (IntegrableOn.iff_ofReal).2 hCast

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

private lemma upsilonRealIntegrand_shift_b_scaled {γ z u : ℝ}
    (hγ : 0 < γ) (hu : 0 < u) :
    (γ / 2) * (upsilonRealIntegrand γ (z + γ / 2) ((γ / 2) * u) -
      upsilonRealIntegrand γ z ((γ / 2) * u)) =
      upsilonScaledShiftKernel (γ / 2) z u := by
  let b  := γ / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbne  := ne_of_gt hb
  have hden : 1 - Real.exp (-u) ≠ 0 := by
    apply ne_of_gt
    simp_all
  have he₁ : Real.exp (-z * (b * u)) = Real.exp (-(b * z) * u) := by
    congr 1
    ring
  have he₂ : Real.exp (-(b⁻¹ - z) * (b * u)) =
      Real.exp (-(1 - b * z) * u) := by
    congr 1
    field_simp [hbne]
  have hdenom : 1 - Real.exp (-(b * u) / b) = 1 - Real.exp (-u) := by
    congr 1
    field_simp [hbne]
  rw [upsilonRealIntegrand_shift_b_pointwise hγ (mul_pos hb hu)]
  simp_rw [show γ / 2 = b by rfl]
  rw [he₁, he₂, hdenom]
  unfold upsilonScaledShiftKernel
  field_simp [ne_of_gt hu, hden]

private lemma exp_frullani_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)))
      (Ioi 0) := by
  have hplus := malmstenRealIntegrand_integrableOn (add_pos hb one_pos)
  have hbase := malmstenRealIntegrand_integrableOn hb
  have hsub : IntegrableOn
      (fun u : ℝ => malmstenRealIntegrand (b + 1) u - malmstenRealIntegrand b u)
      (Ioi 0) := hplus.sub hbase
  have hneg := hsub.neg
  apply hneg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change -(malmstenRealIntegrand (b + 1) u - malmstenRealIntegrand b u) = _
  rw [malmstenRealIntegrand_add_one_sub hu]
  ring

private lemma exp_frullani_integral {b : ℝ} (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), u⁻¹ * (Real.exp (-b * u) - Real.exp (-u)) ∂volume =
      -Real.log b := by
  have hloc : LocallyIntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
    have hcont : Continuous (fun u : ℝ => Real.exp (-u)) := by fun_prop
    exact hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : Tendsto (fun u : ℝ => Real.exp (-u)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun u : ℝ => Real.exp (-u)) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hinf  :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hint : IntegrableOn
      (fun u : ℝ => u⁻¹ • (Real.exp (-(b * u)) - Real.exp (-(1 * u)))) (Ioi 0) := by
    simpa [smul_eq_mul, one_mul] using exp_frullani_integrableOn hb
  have hfr := Frullani.integral_Ioi_eq hloc hb one_pos hzero hinf hint
  simp_all

private lemma upsilonScaledShiftKernel_eq_malmsten {b z u : ℝ} (hu : 0 < u) :
    upsilonScaledShiftKernel b z u =
      malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u +
        (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) := by
  have hden : 1 - Real.exp (-u) ≠ 0 := by
    apply ne_of_gt
    simp_all
  unfold upsilonScaledShiftKernel malmstenRealIntegrand
  field_simp [ne_of_gt hu, hden]
  ring_nf

private lemma upsilonRealIntegral_shift_b {γ z : ℝ}
    (hγ : 0 < γ) (hz0 : 0 < z) (hzQ : z < 2 / γ)
    (hI₀ : IntegrableOn (upsilonRealIntegrand γ z) (Ioi 0))
    (hI₁ : IntegrableOn (upsilonRealIntegrand γ (z + γ / 2)) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + γ / 2) t ∂volume) -
        ∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ z t ∂volume =
      malmstenRealH ((γ / 2) * z) - malmstenRealH (1 - (γ / 2) * z) +
        (1 - 2 * (γ / 2) * z) * Real.log (γ / 2) := by
  let b  := γ / 2
  have hb : 0 < b := by dsimp [b]; positivity

  have hzQb : z < b⁻¹ := by
    continuity



  have hx0  := mul_pos hb hz0
  have hx1 : 0 < 1 - b * z := by
    have hmul := mul_lt_mul_of_pos_left hzQb hb
    grind
  have hscaled :
      (∫ t in Ioi (0 : ℝ),
          upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t ∂volume) =
        ∫ u in Ioi (0 : ℝ), upsilonScaledShiftKernel b z u ∂volume := by
    calc
      _ = b * ∫ u in Ioi (0 : ℝ),
          (upsilonRealIntegrand γ (z + γ / 2) (b * u) -
            upsilonRealIntegrand γ z (b * u)) ∂volume := by
        have hchange := integral_comp_mul_left_Ioi'
          (fun t : ℝ => upsilonRealIntegrand γ (z + γ / 2) t -
            upsilonRealIntegrand γ z t) 0 hb
        simpa [b, smul_eq_mul] using hchange.symm
      _ = ∫ u in Ioi (0 : ℝ),
          b * (upsilonRealIntegrand γ (z + γ / 2) (b * u) -
            upsilonRealIntegrand γ z (b * u)) ∂volume := by
        rw [integral_const_mul]
      _ = ∫ u in Ioi (0 : ℝ), upsilonScaledShiftKernel b z u ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        exact (upsilonRealIntegrand_shift_b_scaled (γ := γ) (z := z) (u := u) hγ hu)
  have hsub :
      (∫ t in Ioi (0 : ℝ),
          (upsilonRealIntegrand γ (z + γ / 2) t - upsilonRealIntegrand γ z t) ∂volume) =
        (∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ (z + γ / 2) t ∂volume) -
          ∫ t in Ioi (0 : ℝ), upsilonRealIntegrand γ z t ∂volume := by
    rw [integral_sub hI₁ hI₀]
  have hxI := malmstenRealIntegrand_integrableOn hx0
  have hyI := malmstenRealIntegrand_integrableOn hx1
  have hfrI := exp_frullani_integrableOn hb
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
        rw [integral_add (hxI.sub hyI) (hfrI.const_mul (2 * b * z - 1))]
        change (∫ u in Ioi (0 : ℝ),
            malmstenRealIntegrand (b * z) u - malmstenRealIntegrand (1 - b * z) u) +
          ∫ u in Ioi (0 : ℝ),
            (2 * b * z - 1) * (u⁻¹ * (Real.exp (-b * u) - Real.exp (-u))) = _
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
  let b  := γ / 2
  let x  := b * z
  have hb : 0 < b := by dsimp [b]; positivity
  have hx0 : 0 < x := mul_pos hb hz0
  have hx1 : 0 < 1 - x := by
    dsimp [x, b]
    field_simp at * <;> nlinarith
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
      convert hreal using 1; ring
    exact_mod_cast hconvert
  have hgamma₁ := malmstenRealH_exp_eq_Gamma hx0
  have hgamma₂ := malmstenRealH_exp_eq_Gamma hx1
  have hRealExp :
      Real.exp (malmstenRealH x - malmstenRealH (1 - x) +
          (1 - 2 * x) * Real.log b) =
        Real.Gamma x / Real.Gamma (1 - x) * b ^ (1 - 2 * x) := by
    have hpow : Real.exp ((1 - 2 * x) * Real.log b) = b ^ (1 - 2 * x) := by
      rw [mul_comm (1 - 2 * x) (Real.log b), ← Real.rpow_def_of_pos hb]
    have hgamma₁'  := hgamma₁
    have hgamma₂'  := hgamma₂
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
      show (1 - γ * z : ℝ) = 1 - 2 * x by dsimp [x, b]; ring]
    exact (Complex.ofReal_cpow (le_of_lt hb) (1 - 2 * x)).symm
  have hfactor :
    lFun ((γ / 2 : ℂ) * (z : ℂ)) *
        ((γ / 2 : ℝ) : ℂ) ^ ((1 - γ * z : ℝ) : ℂ) =
      ((Real.exp (malmstenRealH x - malmstenRealH (1 - x) +
        (1 - 2 * x) * Real.log b) : ℝ) : ℂ) := by
    simp_all
  calc
    Complex.exp (upsilonLog γ ((z + γ / 2 : ℝ) : ℂ)) =
        Complex.exp (((malmstenRealH x - malmstenRealH (1 - x) +
          (1 - 2 * x) * Real.log b : ℝ) : ℂ) + upsilonLog γ (z : ℂ)) := by
            grind
    _ = Complex.exp ((malmstenRealH x - malmstenRealH (1 - x) +
          (1 - 2 * x) * Real.log b : ℝ) : ℂ) *
          Complex.exp (upsilonLog γ (z : ℂ)) := by rw [Complex.exp_add]
    _ = _ := by rw [← Complex.ofReal_exp, hfactor]

private noncomputable def upsilonBForwardFactor (γ : ℝ) (z : ℂ) : ℂ :=
  lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z)

private lemma upsilonBForwardFactor_differentiableAt {γ : ℝ} (hγ : 0 < γ)
    {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (upsilonBForwardFactor γ) z := by
  let b  := (γ / 2 : ℂ)
  have hbR : 0 < γ / 2 := by positivity
  have hbzre : (b * z).re = (γ / 2) * z.re := by
    simp [b, Complex.mul_re]
  have hArgRe : 0 < (b * z).re := by rw [hbzre]; exact mul_pos hbR hz
  have hbDiff : DifferentiableAt ℂ (fun w : ℂ => b * w) z := by fun_prop
  have hOneMinusDiff : DifferentiableAt ℂ (fun w : ℂ => 1 - b * w) z := by fun_prop
  have hGamma  :=
    Complex.differentiableAt_Gamma (b * z) (by
      intro n hn
      have hzero : Complex.Gamma (b * z) = 0 := by
        rw [hn]
        exact Complex.Gamma_neg_nat_eq_zero n
      exact (Complex.Gamma_ne_zero_of_re_pos hArgRe) hzero)
  have hGammaComp  := DifferentiableAt.fun_comp' z (f := fun w : ℂ => b * w)
      (g := Complex.Gamma) hGamma hbDiff
  have hInvGammaComp  := DifferentiableAt.fun_comp' z (f := fun w : ℂ => 1 - b * w)
      (g := fun v : ℂ => (Complex.Gamma v)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt hOneMinusDiff
  have hPow : DifferentiableAt ℂ
      (fun w : ℂ => ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * w)) z := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (by
        apply Complex.ofReal_ne_zero.mpr
        exact div_ne_zero hγ.ne' (by norm_num))
  exact (hGammaComp.mul hInvGammaComp).mul hPow

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
  let O : Set ℂ := {w | 0 < w.re ∧ w.re < 2 / γ}
  let T : Set ℂ := {w | 0 < w.re ∧ w.re < Q γ}
  let bC  := (γ / 2 : ℂ)
  let f  := fun w => Complex.exp (upsilonLog γ (w + bC))
  let g  := fun w => upsilonBForwardFactor γ w *
    Complex.exp (upsilonLog γ w)

  have hrecip : 2 / γ = (γ / 2)⁻¹ := by field_simp [hγ.ne']
  have hQ  := Q_eq_b_add_inv_b hγ
  have hupper : 2 / γ < Q γ := by
    rw [hQ, hrecip]

    linarith
  have hOOpen : IsOpen O := (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt (2 / γ))
  have hOConvex : Convex ℝ O := (convex_halfSpace_re_gt 0).inter
      (convex_halfSpace_re_lt (2 / γ))
  have hOConn  := hOConvex.isPreconnected
  have hOsubT : O ⊆ T := by
    grind
  have hshiftT : ∀ w : ℂ, w ∈ O → w + bC ∈ T := by
    intro w hw
    change 0 < w.re ∧ w.re < 2 / γ at hw
    have hre : (w + bC).re = w.re + γ / 2 := by simp [bC]
    grind
  have htrans : DifferentiableOn ℂ (fun w : ℂ => w + bC) O := by
    intro w hw
    fun_prop
  have hshiftLog  :=
    hDiff.fun_comp htrans hshiftT
  have hf : DifferentiableOn ℂ f O := by
    fun_prop
  have hg : DifferentiableOn ℂ g O := by
    intro w hw
    change DifferentiableWithinAt ℂ
      (fun v => upsilonBForwardFactor γ v * Complex.exp (upsilonLog γ v)) O w
    have hmult := upsilonBForwardFactor_differentiableAt hγ hw.1
    have hlog := (hDiff w (hOsubT hw)).mono hOsubT
    have hexp := differentiable_exp.differentiableAt.comp_differentiableWithinAt w hlog
    exact hmult.differentiableWithinAt.mul hexp
  let x₀  := 1 / γ
  let w₀  := (x₀ : ℂ)
  have hx₀ : 0 < x₀ := by dsimp [x₀]; positivity
  have hx₀upper : x₀ < 2 / γ := by
    bound
  have hw₀ : w₀ ∈ O := ⟨hx₀, hx₀upper⟩
  have hrealEq : ∀ r : ℝ, 0 < r → r < 2 / γ → f (r : ℂ) = g (r : ℂ) := by
    intro r hr0 hrUpper
    have hrQ  := lt_trans hrUpper hupper
    have hrShift0 : 0 < r + γ / 2 := by positivity
    have hrShiftQ : r + γ / 2 < Q γ := by
      linarith
    have hI₀ := upsilonRealIntegrand_integrableOn_of_complex (hInt r hr0 hrQ)
    have hI₁ := upsilonRealIntegrand_integrableOn_of_complex
      (hInt (r + γ / 2) hrShift0 hrShiftQ)
    have h := exp_upsilonLog_shift_b_real hγ hr0 hrUpper hI₀ hI₁
    simpa [f, g, upsilonBForwardFactor, bC] using h
  have hclosure : w₀ ∈ closure ({w | f w = g w} \ {w₀}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let d  := min (ε / 2) (1 / (2 * γ))
    let r  := x₀ + d
    have hd : 0 < d := lt_min (by linarith) (by positivity)
    have hr0 : 0 < r := by dsimp [r]; positivity
    have hrUpper : r < 2 / γ := by
      have hdle : d ≤ 1 / (2 * γ) := min_le_right _ _
      dsimp [r, x₀]

      have hhalf : 1 / (2 * γ) = (1 / 2) * (1 / γ) := by
        field_simp [hγ.ne']
      grind
    have hrne : (r : ℂ) ≠ w₀ := by
      intro heq
      have hreal  := Complex.ofReal_inj.mp (heq)
      grind
    have hdist : dist (r : ℂ) w₀ = d := by
      rw [dist_eq_norm, ← Complex.ofReal_sub]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [show r - x₀ = d by dsimp [r]; ring, abs_of_pos hd]
    refine ⟨(r : ℂ), ⟨hrealEq r hr0 hrUpper, hrne⟩, ?_⟩
    rw [dist_comm, hdist]
    have hdε : d ≤ ε / 2 := min_le_left _ _
    linarith
  have hfA  := hf.analyticOnNhd hOOpen
  have hgA  := hg.analyticOnNhd hOOpen
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
    hfA hgA hOConn hw₀ hclosure
  have hz : z ∈ O := ⟨hz0, hzQ⟩
  exact hEqOn hz

/-- Forward strip shift, using the convergence and holomorphy results for `upsilonLog` on the
defining strip. -/
theorem exp_upsilonLog_shift_b {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {z : ℂ} (hz0 : 0 < z.re) (hzQ : z.re < 2 / γ) :
    Complex.exp (upsilonLog γ (z + (γ / 2 : ℂ))) =
      lFun ((γ / 2 : ℂ) * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - (γ : ℂ) * z) *
        Complex.exp (upsilonLog γ z) := by
  have hDiff := upsilonLog_differentiableOn hγ hγ2
  have hInt : ∀ x : ℝ, 0 < x → x < Q γ →
      IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ (x : ℂ) t) (Ioi 0) := fun x a a_1 => upsilonLogIntegrand_integrableOn hγ hγ2 (↑x) a a_1
  exact exp_upsilonLog_shift_b_of_integrable hγ hDiff hInt hz0 hzQ

end DOZZ.Proofs

end
