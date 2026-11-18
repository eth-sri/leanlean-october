/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Real-variable substitution lemmas for Euler's hypergeometric integral. -/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace DOZZ.Proofs

private lemma euler_int_Icc {a b c x : ℝ} (hb : 0 < b) (hcb : 0 < c - b) (hx1 : x < 1) :
    IntegrableOn (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) (Icc 0 1) := by
  refine (((integrableOn_Icc_iff_integrableOn_Ioc).2
    (realEulerBetaWeight_integrable b (c - b) hb hcb)).mul_continuousOn
    (ContinuousOn.rpow_const (by fun_prop) fun t ht => Or.inl ?_) isCompact_Icc)
  by_cases hx0 : 0 ≤ x
  · exact (by linarith [mul_le_of_le_one_right hx0 ht.2] : 0 < 1 - x * t).ne'
  · exact (by nlinarith [ht.1] : 0 < 1 - x * t).ne'

/-- Euler's transformation for the characterized Gauss family on the positive real interval. -/
theorem realGaussEulerTransform_family
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hca : 0 < c - a)
    (hcb : 0 < c - b) (hx : 0 < x) (hx1 : x < 1) :
    H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
      (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := by
  let k (p q s t : ℝ) : ℝ := t ^ (q - 1) * (1 - t) ^ (s - q - 1) * (1 - x * t) ^ (-p)
  let g : ℝ → ℝ := k (c - a) (c - b) c
  let φ (t : ℝ) : ℝ := (1 - t) / (1 - x * t)
  let d (t : ℝ) : ℝ := -(1 - x) / (1 - x * t) ^ 2
  have hden {t : ℝ} (ht1 : t ≤ 1) : 0 < 1 - x * t := by
    linarith [mul_le_of_le_one_right hx.le ht1]
  have hφ_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : φ t ∈ Icc 0 1 :=
    ⟨div_nonneg (by linarith [ht.2]) (hden ht.2).le,
      (div_le_one (hden ht.2)).2 (by linarith [mul_le_of_le_one_left ht.1 hx1.le])⟩
  have hφ_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : φ t ∈ Ioo 0 1 :=
    ⟨div_pos (by linarith [ht.2]) (hden ht.2.le),
      (div_lt_one (hden ht.2.le)).2 (by linarith [(mul_lt_mul_of_pos_right hx1 ht.1).trans_eq (one_mul t)])⟩
  have hkid {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
      g (φ t) * d t = -((1 - x) ^ (-(c - a - b))) * k a b c t := by
    dsimp only [g, k]
    set q := 1 - x * t; set r := 1 - x
    have hq : 0 < q := hden ht1.le
    have hr : 0 < r := by dsimp [r]; linarith
    have h1t : 0 < 1 - t := by linarith
    have hφq : φ t = (1 - t) / q := rfl
    have h1φ : 1 - φ t = t * r / q := by rw [hφq]; field_simp [hq.ne']; dsimp [q, r]; ring
    have hxφ : 1 - x * φ t = r / q := by rw [hφq]; field_simp [hq.ne']; dsimp [q, r]; ring
    have hd_eq : d t = -r * q ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hq.le, Real.rpow_two]; dsimp [d, q, r]; field_simp [hq.ne']
    rw [show c - (c - b) - 1 = b - 1 by ring, h1φ, hxφ, hd_eq, hφq,
      Real.div_rpow h1t.le hq.le, Real.div_rpow (mul_pos ht0 hr).le hq.le,
      Real.mul_rpow ht0.le hr.le, Real.div_rpow hr.le hq.le,
      div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ← Real.rpow_neg hq.le, ← Real.rpow_neg hq.le, ← Real.rpow_neg hq.le, neg_neg]
    have hqp : q ^ (-(c - b - 1)) * q ^ (-(b - 1)) * q ^ (c - a) * q ^ (-2 : ℝ) = q ^ (-a) := by
      rw [← Real.rpow_add hq, ← Real.rpow_add hq, ← Real.rpow_add hq]; congr 1; ring
    have hrp : r ^ (b - 1) * r ^ (-(c - a)) * r = r ^ (-(c - a - b)) := by
      calc r ^ (b - 1) * r ^ (-(c - a)) * r
          = r ^ (b - 1) * r ^ (-(c - a)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = r ^ (-(c - a - b)) := by rw [← Real.rpow_add hr, ← Real.rpow_add hr]; congr 1; ring
    calc (1 - t) ^ (c - b - 1) * q ^ (-(c - b - 1)) * (t ^ (b - 1) * r ^ (b - 1) * q ^ (-(b - 1))) *
            (r ^ (-(c - a)) * q ^ (c - a)) * (-r * q ^ (-2 : ℝ))
        = -(t ^ (b - 1) * (1 - t) ^ (c - b - 1)) * (r ^ (b - 1) * r ^ (-(c - a)) * r) *
            (q ^ (-(c - b - 1)) * q ^ (-(b - 1)) * q ^ (c - a) * q ^ (-2 : ℝ)) := by ring
      _ = -r ^ (-(c - a - b)) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * q ^ (-a)) := by
            rw [hrp, hqp]; ring
  have hbc : 0 < c - (c - b) := by linarith
  have htransIcc : IntegrableOn g (Icc 0 1) := euler_int_Icc hcb hbc hx1
  have hEq_ae : (fun t => (g ∘ φ) t * d t) =ᵐ[volume.restrict (Ioc 0 1)]
      fun t => -((1 - x) ^ (-(c - a - b))) * k a b c t := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 hm
    exact hkid hm.1 (lt_of_le_of_ne hm.2 ht1)
  have hcompIcc : IntegrableOn (fun t => (g ∘ φ) t * d t) (Icc 0 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2
      (((euler_int_Icc hb hcb hx1).mono_set Ioc_subset_Icc_self).const_mul _ |>.congr hEq_ae.symm)
  have hφderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivWithinAt φ (d t) (Ioi t) t := by
    have hq := (((hasDerivAt_id t).const_sub 1).div
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul x)) (hden ht.2.le).ne')
    refine (hq.congr_deriv ?_).hasDerivWithinAt
    dsimp [d]; field_simp [(hden ht.2.le).ne']; ring
  have hgcont : ContinuousOn g (Ioo 0 1) :=
    ((ContinuousOn.rpow_const continuousOn_id fun u hu => Or.inl hu.1.ne').mul
      (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
        fun u hu => Or.inl (sub_pos.mpr hu.2).ne')).mul
      (ContinuousOn.rpow_const (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
        fun u hu => Or.inl (hden hu.2.le).ne')
  have hφcont : ContinuousOn φ (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) fun _ ht => (hden ht.2).ne'
  have hu01 : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have himgIoo : φ '' Ioo 0 1 ⊆ Ioo 0 1 := by rintro _ ⟨t, ht, rfl⟩; exact hφ_Ioo ht
  have himgIcc : φ '' Icc 0 1 ⊆ Icc 0 1 := by rintro _ ⟨t, ht, rfl⟩; exact hφ_Icc ht
  have hsub := intervalIntegral.integral_comp_mul_deriv''' (f := φ) (f' := d) (g := g)
    (a := (0 : ℝ)) (b := 1) (hu01 ▸ hφcont) (by simpa using hφderiv)
    (by simpa using hgcont.mono himgIoo)
    (hu01 ▸ htransIcc.mono_set himgIcc)
    (hu01 ▸ hcompIcc)
  have hφ0 : φ 0 = 1 := by simp [φ]
  have hφ1 : φ 1 = 0 := by simp [φ]
  rw [hφ0, hφ1, intervalIntegral.integral_symm 0 1, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, integral_congr_ae hEq_ae, integral_const_mul] at hsub
  have hKerEq : realGaussEulerKernelIntegral (c - a) (c - b) c x =
      (1 - x) ^ (-(c - a - b)) * realGaussEulerKernelIntegral a b c x := by
    have h1 : ∫ u in Ioc 0 1, g u = realGaussEulerKernelIntegral (c - a) (c - b) c x := rfl
    have h2 : ∫ t in Ioc 0 1, k a b c t = realGaussEulerKernelIntegral a b c x := rfl
    rw [h1, h2, neg_mul] at hsub; linarith
  have hOrig := realGaussEulerIntegral_eq_family hH a b c x ha hb hcb hx hx1
  have hTrans := realGaussEulerIntegral_eq_family hH (c - a) (c - b) c x hca hcb hbc hx hx1
  unfold realGaussEulerKernelIntegral at hKerEq
  rw [← hOrig, ← hTrans, hKerEq, show c - (c - b) = b by ring, mul_comm (Real.Gamma (c - b)) (Real.Gamma b)]
  have hpow : (1 - x) ^ (c - a - b) * (1 - x) ^ (-(c - a - b)) = 1 := by
    rw [← Real.rpow_add (by linarith : 0 < 1 - x), add_neg_cancel, Real.rpow_zero]
  have hcast : (((1 - x) ^ (c - a - b) : ℝ) : ℂ) =
      (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) := by
    rw [Complex.ofReal_cpow (by linarith : 0 ≤ 1 - x)]; push_cast; rfl
  rw [← hcast, Complex.ofReal_mul ((1 - x) ^ (-(c - a - b))),
    show ∀ G K A B : ℂ, A * (G * (B * K)) = (A * B) * (G * K) by intros; ring,
    ← Complex.ofReal_mul ((1 - x) ^ (c - a - b)), hpow, Complex.ofReal_one, one_mul]

end DOZZ.Proofs
