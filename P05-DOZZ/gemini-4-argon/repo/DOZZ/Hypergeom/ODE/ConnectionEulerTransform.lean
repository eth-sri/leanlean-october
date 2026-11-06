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

open MeasureTheory Set

namespace DOZZ.Proofs

/-- The real Euler integrand for parameters `(a,b,c)` at a real argument `x`. -/
noncomputable def realGaussEulerKernel (a b c x t : ℝ) : ℝ :=
  t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)

/-- The integrand for the Euler-transformed parameters `(c-a,c-b,c)`. -/
noncomputable def realGaussEulerTransformedKernel (a b c x u : ℝ) : ℝ :=
  u ^ (c - b - 1) * (1 - u) ^ (b - 1) * (1 - x * u) ^ (-(c - a))

/-- The decreasing Mobius map used to exchange the two beta endpoints. -/
noncomputable def realGaussEulerMobius (x t : ℝ) : ℝ :=
  (1 - t) / (1 - x * t)

private theorem realGaussEulerKernel_integrableOn_Icc_aux a b c x
    (hb : 0 < b) (hcb : 0 < c - b) (hx : x < 1) :
    IntegrableOn (realGaussEulerKernel a b c x) (Icc 0 1) := by
  have hfactor : ContinuousOn (fun t => (1 - x * t) ^ (-a)) (Icc 0 1) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro t ht
    left
    by_cases hx0 : 0 ≤ x
    · have hxt : x * t ≤ x := mul_le_of_le_one_right hx0 ht.2
      exact ne_of_gt (by nlinarith [hx, hxt])
    · have hxneg : x < 0 := lt_of_not_ge hx0
      exact ne_of_gt (by nlinarith [(mul_nonpos_of_nonpos_of_nonneg hxneg.le ht.1)])
  change IntegrableOn (fun t : ℝ =>
    t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - x * t) ^ (-a)) (Icc 0 1)
  exact (((integrableOn_Icc_iff_integrableOn_Ioc).2 (realEulerBetaWeight_integrable b (c - b) hb hcb)).mul_continuousOn hfactor isCompact_Icc)

/-- The real Euler kernel is integrable on the closed beta interval whenever its two beta
parameters are positive and `x < 1`. -/
theorem realGaussEulerKernel_integrableOn_Icc a b c x
    (hb : 0 < b) (hcb : 0 < c - b) (hx : x < 1) :
    IntegrableOn (realGaussEulerKernel a b c x) (Icc 0 1) :=
  realGaussEulerKernel_integrableOn_Icc_aux a b c x hb hcb hx





/-- Euler's transformation for the characterized Gauss family on the positive real interval. The
real Euler integral represents both parameter triples, and the Mobius integral identity connects
them. -/
theorem realGaussEulerTransform_family
    {H} (hH : IsGaussHypergeometricFamily H)
    (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hca : 0 < c - a)
    (hcb : 0 < c - b) (hx : 0 < x) (hx1 : x < 1) :
    H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
      (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := by
  have realGaussEulerMobius_mem_Icc t (hx : 0 < x) (hx1 : x < 1) (ht : t ∈ Icc 0 1) : realGaussEulerMobius x t ∈ Icc 0 1 := by
    rcases ht with ⟨ht0, ht1⟩
    have hden : 0 < 1 - x * t := by
      have := mul_le_of_le_one_right hx.le ht1
      linarith
    have := mul_le_of_le_one_left ht0 hx1.le
    constructor
    · exact div_nonneg (by linarith) hden.le
    · rw [realGaussEulerMobius, div_le_one hden]
      linarith
  have realGaussEulerMobius_kernel_identity t (hx : 0 < x) (hx1 : x < 1) (ht : 0 < t) (ht1 : t < 1) : realGaussEulerTransformedKernel a b c x (realGaussEulerMobius x t) * (-(1 - x) / (1 - x * t) ^ 2) = -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernel a b c x t := by
    let q : ℝ := 1 - x * t
    let r : ℝ := 1 - x
    have hq : 0 < q := by dsimp [q]; nlinarith
    have hr : 0 < r := by dsimp [r]; linarith
    have hphi : realGaussEulerMobius x t = (1 - t) / q := by
      simp [realGaussEulerMobius, q]
    have h1phi : 1 - realGaussEulerMobius x t = t * r / q := by
      rw [hphi]
      field_simp [ne_of_gt hq]
      ring
    have hxphi : 1 - x * realGaussEulerMobius x t = r / q := by
      rw [hphi]
      field_simp [ne_of_gt hq]
      ring
    have hqpow2 : q ^ (2 : ℝ) = q ^ 2 := Real.rpow_natCast q 2
    have hderiv : (-(1 - x) / (1 - x * t) ^ 2) = -r * q ^ (-(2 : ℝ)) := by
      rw [(show q ^ (-(2 : ℝ)) = (q ^ 2)⁻¹ by rw [(Real.rpow_neg hq.le (2 : ℝ)), hqpow2])]
      dsimp [r, q]
      field_simp
    have hqpow : q ^ (-(c - b - 1)) * q ^ (-(b - 1)) * q ^ (c - a) *
        q ^ (-(2 : ℝ)) = q ^ (-a) := by
      calc
        q ^ (-(c - b - 1)) * q ^ (-(b - 1)) * q ^ (c - a) * q ^ (-(2 : ℝ)) =
            q ^ (-(c - b - 1) - (b - 1) + (c - a) - 2) := by
              rw [← Real.rpow_add hq, ← Real.rpow_add hq, ← Real.rpow_add hq, (show -(c - b - 1) + -(b - 1) + (c - a) + (-(2 : ℝ)) = -(c - b - 1) - (b - 1) + (c - a) - 2 by ring)]
        _ = q ^ (-a) := by
          rw [show -(c - b - 1) - (b - 1) + (c - a) - 2 = -a by ring]
    have hrpow : r ^ (b - 1) * r ^ (-(c - a)) * r = r ^ (-(c - a - b)) := by
      calc
        r ^ (b - 1) * r ^ (-(c - a)) * r = r ^ (b - 1 - (c - a) + 1) := by
          calc
            r ^ (b - 1) * r ^ (-(c - a)) * r =
                r ^ (b - 1) * r ^ (-(c - a)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = r ^ (b - 1 - (c - a)) * r ^ (1 : ℝ) := by
              rw [← Real.rpow_add hr, show b - 1 + -(c - a) = b - 1 - (c - a) by ring]
            _ = r ^ (b - 1 - (c - a) + 1) :=
              (Real.rpow_add hr (b - 1 - (c - a)) 1).symm
        _ = r ^ (-(c - a - b)) := by
          rw [show b - 1 - (c - a) + 1 = -(c - a - b) by ring]
    rw [realGaussEulerTransformedKernel, realGaussEulerKernel,
      (show realGaussEulerMobius x t ^ (c - b - 1) = (1 - t) ^ (c - b - 1) * q ^ (-(c - b - 1)) by rw [hphi, Real.div_rpow (le_of_lt (show 0 < 1 - t by linarith)) (le_of_lt hq), div_eq_mul_inv, ← Real.rpow_neg hq.le (c - b - 1)]), (show (1 - realGaussEulerMobius x t) ^ (b - 1) = t ^ (b - 1) * r ^ (b - 1) * q ^ (-(b - 1)) by rw [h1phi, Real.div_rpow (le_of_lt (mul_pos ht hr)) (le_of_lt hq), Real.mul_rpow ht.le hr.le, div_eq_mul_inv, ← Real.rpow_neg hq.le (b - 1)]), (show (1 - x * realGaussEulerMobius x t) ^ (-(c - a)) = r ^ (-(c - a)) * q ^ (c - a) by rw [hxphi, Real.div_rpow hr.le hq.le, div_eq_mul_inv, Real.rpow_neg hr.le, Real.rpow_neg hq.le, inv_inv]), hderiv]
    calc
      _ = -(r ^ (-(c - a - b))) *
          (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * q ^ (-a)) := by
        rw [mul_assoc, mul_assoc, ← hrpow, ← hqpow]
        ring
      _ = -((1 - x) ^ (-(c - a - b))) *
          realGaussEulerKernel a b c x t := by
        simp [realGaussEulerKernel, q, r]
  have realGaussEulerIntegral_eulerTransform : (Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))) * realGaussEulerKernelIntegral a b c x = (1 - x) ^ (c - a - b) * ((Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b)) * realGaussEulerKernelIntegral (c - a) (c - b) c x) := by
    have realGaussEulerMobius_mem_Ioo t (hx : 0 < x) (hx1 : x < 1) (ht : t ∈ Ioo 0 1) : realGaussEulerMobius x t ∈ Ioo 0 1 := by
      rcases ht with ⟨ht0, ht1⟩
      have hden : 0 < 1 - x * t := by
        have := mul_le_of_le_one_right hx.le ht1.le
        linarith
      have : x * t < t := by
        calc
          x * t < 1 * t := mul_lt_mul_of_pos_right hx1 ht0
          _ = t := one_mul _
      constructor
      · exact div_pos (by linarith) hden
      · rw [realGaussEulerMobius, div_lt_one hden]
        linarith
    let φ : ℝ → ℝ := realGaussEulerMobius x
    let g := realGaussEulerTransformedKernel a b c x
    let d : ℝ → ℝ := fun t => -(1 - x) / (1 - x * t) ^ 2
    have hden t (ht : t ∈ Icc 0 1) : 1 - x * t ≠ 0 := by
      have hxt : x * t ≤ x := by
        rcases ht with ⟨ht0, ht1⟩
        exact mul_le_of_le_one_right hx.le ht1
      exact ne_of_gt (by nlinarith [hx1, hxt])
    have hφcont : ContinuousOn φ (Icc 0 1) := by
      change ContinuousOn (fun t : ℝ => (1 - t) / (1 - x * t)) (Icc 0 1)
      refine (continuousOn_const.sub continuousOn_id).div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) ?_
      intro t ht
      exact hden t ht
    have hφderiv t (ht : t ∈ Ioo 0 1) : HasDerivWithinAt φ (d t) (Ioi t) t := by
      have hdenpos : 0 < 1 - x * t := by
        have := realGaussEulerMobius_mem_Icc t hx hx1 ⟨ht.1.le, ht.2.le⟩
        nlinarith [hx1, (mul_le_of_le_one_right hx.le ht.2.le)]
      have hquot' : HasDerivAt (fun u : ℝ => (1 - u) / (1 - x * u)) (d t) t := by
        convert ((show HasDerivAt (fun u : ℝ => 1 - u) (-1) t by simpa using (hasDerivAt_id t).const_sub (1 : ℝ)).div (by change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - (fun u => x * u)) (-x) t; simpa only [zero_sub] using (hasDerivAt_const t (1 : ℝ)).sub (by simpa using (hasDerivAt_id t).const_mul x)) (ne_of_gt hdenpos)) using 1
        dsimp [d]
        field_simp
        ring
      exact hquot'.hasDerivWithinAt
    have hgcont : ContinuousOn g (Ioo 0 1) := by
      change ContinuousOn (fun u : ℝ =>
        u ^ (c - b - 1) * (1 - u) ^ (b - 1) * (1 - x * u) ^ (-(c - a)))
        (Ioo 0 1)
      have hpow1 : ContinuousOn (fun u : ℝ => u ^ (c - b - 1)) (Ioo 0 1) := by
        apply ContinuousOn.rpow_const continuousOn_id
        intro u hu
        exact Or.inl (ne_of_gt hu.1)
      exact (hpow1.mul (by apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id); intro u hu; exact Or.inl (ne_of_gt (sub_pos.mpr hu.2)))).mul (by apply ContinuousOn.rpow_const (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)); intro u hu; exact Or.inl (ne_of_gt (show 0 < 1 - x * u by nlinarith [hx1, (mul_le_of_le_one_right hx.le hu.2.le)])))
    have htransIcc : IntegrableOn g (Icc 0 1) := by
      have h := realGaussEulerKernel_integrableOn_Icc (c - a) (c - b) c x hcb (by simpa only [show c - (c - b) = b by ring] using hb) hx1
      change IntegrableOn (realGaussEulerTransformedKernel a b c x) (Icc 0 1)
      change IntegrableOn (realGaussEulerKernel (c - a) (c - b) c x) (Icc 0 1) at h
      have hk : realGaussEulerKernel (c - a) (c - b) c x =
          realGaussEulerTransformedKernel a b c x := by
        funext u
        simp only [realGaussEulerKernel, realGaussEulerTransformedKernel]
        rw [show c - (c - b) - 1 = b - 1 by ring]
      exact hk ▸ h
    have htransImage : IntegrableOn g (φ '' Icc 0 1) :=
      htransIcc.mono_set (by
        rintro u ⟨t, ht, rfl⟩
        exact realGaussEulerMobius_mem_Icc t hx hx1 ht)
    have hgcontImage : ContinuousOn g (φ '' Ioo 0 1) :=
      hgcont.mono (by
        rintro u ⟨t, ht, rfl⟩
        exact realGaussEulerMobius_mem_Ioo t hx hx1 ht)
    have hcompIoc : IntegrableOn (fun t => g (φ t) * d t) (Ioc 0 1) := by
      have hEq : (fun t => g (φ t) * d t) =ᵐ[volume.restrict (Ioc 0 1)]
          (fun t => -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernel a b c x t) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 hmem
        exact realGaussEulerMobius_kernel_identity t hx hx1 hmem.1
          (lt_of_le_of_ne hmem.2 ht1)
      exact (((realGaussEulerKernel_integrableOn_Icc a b c x hb hcb hx1).mono_set Ioc_subset_Icc_self).const_mul (-((1 - x) ^ (-(c - a - b))))) |>.congr hEq.symm
    have hsub := intervalIntegral.integral_comp_mul_deriv''' (f := φ) (f' := d) (g := g)
      (a := (0 : ℝ)) (b := 1) (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hφcont) (by simpa using hφderiv) (by simpa using hgcontImage) (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using htransImage) (by simpa [Function.comp_def, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ((integrableOn_Icc_iff_integrableOn_Ioc).2 hcompIoc))
    have hkernelEq :
        (∫ t in (0 : ℝ)..1, g (φ t) * d t) =
          -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernelIntegral a b c x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      have hEq : (fun t => g (φ t) * d t) =ᵐ[volume.restrict (Ioc 0 1)]
          (fun t => -((1 - x) ^ (-(c - a - b))) * realGaussEulerKernel a b c x t) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1 hmem
        exact realGaussEulerMobius_kernel_identity t hx hx1 hmem.1
          (lt_of_le_of_ne hmem.2 ht1)
      rw [integral_congr_ae hEq, integral_const_mul]
      rfl
    have hraw :
        realGaussEulerKernelIntegral (c - a) (c - b) c x =
          (1 - x) ^ (-(c - a - b)) * realGaussEulerKernelIntegral a b c x := by
      rw [← (show (∫ u in (0 : ℝ)..1, g u) = realGaussEulerKernelIntegral (c - a) (c - b) c x by rw [intervalIntegral.integral_of_le (by norm_num)]; simp [realGaussEulerKernelIntegral, g, realGaussEulerTransformedKernel])]
      calc
        (∫ u in (0 : ℝ)..1, g u) = -(∫ t in (0 : ℝ)..1, g (φ t) * d t) := by
          rw [(show (∫ t in (0 : ℝ)..1, g (φ t) * d t) = -(∫ u in (0 : ℝ)..1, g u) by rw [(show φ 0 = 1 by simp [φ, realGaussEulerMobius]), (show φ 1 = 0 by simp [φ, realGaussEulerMobius])] at hsub; exact hsub.trans (by rw [intervalIntegral.integral_symm]))]
          ring
        _ = (1 - x) ^ (-(c - a - b)) * realGaussEulerKernelIntegral a b c x := by
          rw [hkernelEq]
          ring
    rw [(show Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) = Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) by ring), hraw]
    calc
      Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) *
          realGaussEulerKernelIntegral a b c x =
        ((1 - x) ^ (c - a - b) * (1 - x) ^ (-(c - a - b))) *
          (Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) *
            realGaussEulerKernelIntegral a b c x) := by rw [(show (1 - x) ^ (c - a - b) * (1 - x) ^ (-(c - a - b)) = 1 by rw [← Real.rpow_add (by linarith : 0 < 1 - x)]; simp)]; simp
      _ = (1 - x) ^ (c - a - b) *
          (Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b) *
            ((1 - x) ^ (-(c - a - b)) * realGaussEulerKernelIntegral a b c x)) := by ring
  let N := Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b))
  let N' := Real.Gamma c / (Real.Gamma (c - b) * Real.Gamma b)
  have hrawC := congrArg (fun y : ℝ => (y : ℂ)) (realGaussEulerIntegral_eulerTransform)
  rw [Complex.ofReal_mul, Complex.ofReal_mul] at hrawC
  have hpowCast : ((1 - x) ^ (c - a - b) : ℝ) =
      (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) := by
    rw [← (show ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) by push_cast; ring), show (1 : ℂ) - (x : ℝ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by linarith : 0 ≤ 1 - x)]
  calc
    H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) =
        (N : ℂ) * (realGaussEulerKernelIntegral a b c x : ℂ) := (show (N : ℂ) * (realGaussEulerKernelIntegral a b c x : ℂ) = H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ) by simpa [N, realGaussEulerKernelIntegral] using (realGaussEulerIntegral_eq_family hH a b c x ha hb hcb hx hx1)).symm
    _ = ((1 - x) ^ (c - a - b) : ℝ) *
        ((N' : ℂ) * (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ)) := by
      rw [hpowCast]
      exact (by simpa only [N, N', Complex.ofReal_mul, hpowCast] using hrawC)
    _ = (1 - (x : ℂ)) ^ ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) := by
          rw [hpowCast, (show (N' : ℂ) * (realGaussEulerKernelIntegral (c - a) (c - b) c x : ℂ) = H (c - a : ℝ) (c - b : ℝ) (c : ℝ) (x : ℝ) by simpa [N', realGaussEulerKernelIntegral, (show c - (c - b) = b by ring)] using (realGaussEulerIntegral_eq_family hH (c - a) (c - b) c x hca hcb (by simpa only [show c - (c - b) = b by ring] using hb) hx hx1))]

end DOZZ.Proofs
