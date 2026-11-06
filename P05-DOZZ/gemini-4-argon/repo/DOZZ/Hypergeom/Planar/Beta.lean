/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Support for the proof of the beta integral `DOZZ.beta_negative_power_integral`
([KRV, Lemma 12.6]). -/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace DOZZ.Proofs

/-- Mathlib's complex beta integral on real parameters is the cast of the corresponding real
interval integral. -/
theorem betaIntegral_ofReal (x y : ℝ) :
    Complex.betaIntegral (x : ℂ) (y : ℂ) =
      (↑(∫ t : ℝ in Ioc (0 : ℝ) 1, t ^ (x - 1) * (1 - t) ^ (y - 1)) : ℂ) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ t : ℝ in Ioc (0 : ℝ) 1,
          ((t ^ (x - 1) * (1 - t) ^ (y - 1) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, show (y : ℂ) - 1 = ((y - 1 : ℝ) : ℂ) by push_cast; ring, show (1 : ℂ) - (t : ℝ) = ((1 - t : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (le_of_lt ht.1), ← Complex.ofReal_cpow (show 0 ≤ 1 - t by linarith [ht.2])]
      exact (Complex.ofReal_mul _ _).symm
    _ = _ := integral_ofReal







/-- The signed negative-power integral from the one-dimensional identity of [KRV, Lemma 12.6]. -/
theorem beta_negative_power_integral (p a : ℝ) (hp : 0 < p) (ha : 1 < a)
    (ha₂ : a < 2) :
    IntegrableOn (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) (Ioi 0) ∧
      (∫ v : ℝ in Ioi 0, ((1 + v) ^ (-p) - 1) * v ^ (-a)) =
        Real.Gamma (1 - a) * Real.Gamma (p + a - 1) / Real.Gamma p := by
  have beta_primitive_abs (x : ℝ) (ha : 1 < a) (hx : 0 < x) : |x ^ (1 - a) / (1 - a)| = (1 / (a - 1)) * x ^ (1 - a) := by
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hx _),
      abs_of_neg (by linarith : 1 - a < 0)]
    rw [show -(1 - a) = a - 1 by ring]
    ring
  have one_sub_rpow_abs_le {v} (hv : v ∈ Ioc (0 : ℝ) 1) : |(1 + v) ^ (-p) - 1| ≤ p * v := by
    have hderiv : ∀ x ∈ Icc (0 : ℝ) 1,
        ‖deriv (fun y => (1 + y) ^ (-p)) x‖ ≤ p := by
      intro x hx
      rw [(show deriv (fun y => (1 + y) ^ (-p)) x = (-p) * (1 + x) ^ (-p - 1) by simpa [Function.comp_def] using ((Real.hasDerivAt_rpow_const (x := 1 + x) (p := -p) (Or.inl (by linarith [hx.1]))).comp x ((hasDerivAt_id x).const_add 1)).deriv)]
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hp,
        abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)]
      exact (mul_le_of_le_one_right (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by linarith)))
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (by intro x hx; exact (Real.hasDerivAt_rpow_const (x := 1 + x) (p := -p) (Or.inl (by linarith [hx.1]))).differentiableAt.comp x ((hasDerivAt_id x).const_add 1).differentiableAt) hderiv (convex_Icc (0 : ℝ) 1) (left_mem_Icc.mpr (by norm_num))
      (by exact ⟨le_of_lt hv.1, hv.2⟩)
    simpa [Real.norm_eq_abs, abs_of_pos hv.1] using hmv
  have beta_product_tends_zero : Tendsto (fun x : ℝ => ((1 + x) ^ (-p) - 1) * (x ^ (1 - a) / (1 - a))) (𝓝[>] 0) (𝓝 0) ∧ Tendsto (fun x : ℝ => ((1 + x) ^ (-p) - 1) * (x ^ (1 - a) / (1 - a))) atTop (𝓝 0) := by
    let g : ℝ → ℝ := fun x => (1 + x) ^ (-p) - 1
    let G : ℝ → ℝ := fun x => x ^ (1 - a) / (1 - a)
    let c := p / (a - 1)
    let d : ℝ := 1 / (a - 1)
    have : 0 < c := div_pos hp (by linarith)
    have hd : 0 < d := by positivity
    have hnearBound : ∀ᶠ x in 𝓝[>] (0 : ℝ), ‖g x * G x‖ ≤ c * x ^ (2 - a) := by
      filter_upwards [eventually_mem_nhdsWithin, ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds)] with x hx hx1
      have hpowmul : x * x ^ (1 - a) = x ^ (2 - a) := by
        calc
          x * x ^ (1 - a) = x ^ (1 : ℝ) * x ^ (1 - a) := by rw [Real.rpow_one]
          _ = x ^ (1 + (1 - a)) := by rw [← Real.rpow_add hx]
          _ = x ^ (2 - a) := by congr 1; ring
      rw [(show ‖g x * G x‖ = |g x| * |G x| by simp [Real.norm_eq_abs]), (show |G x| = d * x ^ (1 - a) by simpa [G, d] using beta_primitive_abs x ha hx)]
      calc
        |g x| * (d * x ^ (1 - a)) ≤ (p * x) * (d * x ^ (1 - a)) :=
          mul_le_mul_of_nonneg_right (by simpa [g] using one_sub_rpow_abs_le ⟨hx, le_of_lt hx1⟩)
            (mul_nonneg hd.le (Real.rpow_nonneg hx.le _))
        _ = c * x ^ (2 - a) := by
          dsimp [c, d]
          field_simp
          rw [hpowmul]
    have hnearSqueeze :
        Tendsto (fun x : ℝ => g x * G x) (𝓝[>] 0) (𝓝 0) := by
      have htop : Tendsto (fun x : ℝ => c * x ^ (2 - a)) (𝓝[>] 0) (𝓝 0) := by
        simpa [mul_comm] using (show Tendsto (fun x : ℝ => x ^ (2 - a)) (𝓝[>] 0) (𝓝 0) by simpa [Real.zero_rpow, ne_of_gt (show 0 < 2 - a by linarith)] using (Real.continuousAt_rpow_const 0 (2 - a) (Or.inr (by linarith))).mono_left nhdsWithin_le_nhds).const_mul c
      have hbounds : ∀ᶠ x in 𝓝[>] (0 : ℝ),
          -(c * x ^ (2 - a)) ≤ g x * G x ∧ g x * G x ≤ c * x ^ (2 - a) := by
        filter_upwards [hnearBound] with x hx
        exact abs_le.mp (by simpa [Real.norm_eq_abs] using hx)
      exact Filter.Tendsto.squeeze' (by simpa using htop.neg) htop
        (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
    have htailBound : ∀ᶠ x in atTop, ‖g x * G x‖ ≤ d * x ^ (1 - a) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have := hx
      have : 0 ≤ (1 + x) ^ (-p) := Real.rpow_nonneg (by linarith) _
      rw [Real.norm_eq_abs, abs_mul, (show |G x| = d * x ^ (1 - a) by simpa [G, d] using beta_primitive_abs x ha (lt_trans zero_lt_one hx))]
      simpa [d] using mul_le_mul_of_nonneg_right (show |g x| ≤ 1 by rw [show g x = (1 + x) ^ (-p) - 1 by rfl, abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)))]; linarith)
        (mul_nonneg hd.le (Real.rpow_nonneg (by linarith) _))
    have htailSqueeze :
        Tendsto (fun x : ℝ => g x * G x) atTop (𝓝 0) := by
      have htop : Tendsto (fun x : ℝ => d * x ^ (1 - a)) atTop (𝓝 0) := by
        simpa [mul_comm] using (show Tendsto (fun x : ℝ => x ^ (1 - a)) atTop (𝓝 0) by simpa [sub_eq_add_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < a - 1)).const_mul d
      have hbounds : ∀ᶠ x in atTop,
          -(d * x ^ (1 - a)) ≤ g x * G x ∧ g x * G x ≤ d * x ^ (1 - a) := by
        filter_upwards [htailBound] with x hx
        exact abs_le.mp (by simpa [Real.norm_eq_abs] using hx)
      exact Filter.Tendsto.squeeze' (by simpa using htop.neg) htop
        (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
    constructor
    · simpa [g, G] using hnearSqueeze
    · simpa [g, G] using htailSqueeze
  have beta_ibp_derivative_integrable : IntegrableOn (fun v : ℝ => (-p) * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (1 - a))) (Ioi 0) := by
    let c := p / (a - 1)
    have hnearDom : IntegrableOn (fun v : ℝ => c * v ^ (1 - a)) (Ioc 0 1) := by
      change Integrable (fun v : ℝ => c * v ^ (1 - a)) (volume.restrict (Ioc 0 1))
      exact (show IntegrableOn (fun v : ℝ => v ^ (1 - a)) (Ioc 0 1) by rw [integrableOn_congr_set_ae Ioo_ae_eq_Ioc.symm]; exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)).integrable.const_mul c
    have hnear : IntegrableOn
        (fun v : ℝ => (-p) * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (1 - a)))
        (Ioc 0 1) := by
      apply hnearDom.integrable.mono' (Measurable.aestronglyMeasurable
        (show Measurable (fun v : ℝ => (-p) * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (1 - a))) from
          (measurable_const.mul ((measurable_const.add measurable_id).pow_const (-p - 1))).mul
            ((measurable_id.pow_const (1 - a)).div_const (1 - a))))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hv' := hv
      have hpow : 0 < v ^ (1 - a) := Real.rpow_pos_of_pos hv'.1 _
      have hfactor : 0 < (1 + v) ^ (-p - 1) ∧ (1 + v) ^ (-p - 1) ≤ 1 := by
        constructor
        · exact Real.rpow_pos_of_pos (by linarith [hv'.1]) _
        · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hv'.1]) (by linarith)
      have hnorm :
          ‖(-p) * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (1 - a))‖ =
            p * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (a - 1)) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos hp,
          abs_of_pos hfactor.1, abs_div, abs_of_pos hpow,
          abs_of_neg (by linarith : 1 - a < 0)]
        congr 2
        field_simp
        ring
      rw [hnorm]
      have hdiv := (div_le_div_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor.2 hp.le) hpow.le) (by linarith : 0 ≤ a - 1))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv.trans_eq (by dsimp [c]; ring)
    have htailDom : IntegrableOn (fun v : ℝ => c * v ^ (-p - a)) (Ioi 1) := by
      change Integrable (fun v : ℝ => c * v ^ (-p - a)) (volume.restrict (Ioi 1))
      exact (show IntegrableOn (fun v : ℝ => v ^ (-p - a)) (Ioi 1) by apply integrableOn_Ioi_rpow_of_lt (c := 1) _ zero_lt_one; linarith).integrable.const_mul c
    have htail : IntegrableOn
        (fun v : ℝ => (-p) * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (1 - a)))
        (Ioi 1) := by
      apply htailDom.integrable.mono' (Measurable.aestronglyMeasurable
        (show Measurable (fun v : ℝ => (-p) * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (1 - a))) from
          (measurable_const.mul ((measurable_const.add measurable_id).pow_const (-p - 1))).mul
            ((measurable_id.pow_const (1 - a)).div_const (1 - a))))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hvpos := lt_trans zero_lt_one hv
      have hq : 0 < v ^ (1 - a) := Real.rpow_pos_of_pos hvpos _
      have hpow :
          0 < (1 + v) ^ (-p - 1) ∧ (1 + v) ^ (-p - 1) ≤ v ^ (-p - 1) := by
        constructor
        · exact Real.rpow_pos_of_pos (by linarith [hv]) _
        · exact Real.rpow_le_rpow_of_nonpos hvpos (by linarith [hv]) (by linarith)
      have hnorm :
          ‖(-p) * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (1 - a))‖ =
            p * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (a - 1)) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos hp,
          abs_of_pos hpow.1, abs_div, abs_of_pos hq,
          abs_of_neg (by linarith : 1 - a < 0)]
        congr 2
        field_simp
        ring
      have hpowmul : v ^ (-p - 1) * v ^ (1 - a) = v ^ (-p - a) := by
        rw [← Real.rpow_add hvpos]
        congr 1
        ring
      rw [hnorm]
      have hdiv := (div_le_div_of_nonneg_right (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow.2 hp.le) hq.le) (by linarith : 0 ≤ a - 1))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv.trans_eq (by rw [hpowmul]; dsimp [c]; ring)
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    exact ⟨hnear, htail⟩
  have beta_negative_power_integrable : IntegrableOn (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) (Ioi 0) := by
    have hnearDom : IntegrableOn (fun v : ℝ => p * v ^ (1 - a)) (Ioc 0 1) := by
      change Integrable (fun v : ℝ => p * v ^ (1 - a)) (volume.restrict (Ioc 0 1))
      exact (show IntegrableOn (fun v : ℝ => v ^ (1 - a)) (Ioc 0 1) by rw [integrableOn_congr_set_ae Ioo_ae_eq_Ioc.symm]; exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)).integrable.const_mul p
    have hnear : IntegrableOn
        (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) (Ioc 0 1) := by
      apply hnearDom.integrable.mono' (Measurable.aestronglyMeasurable
        (show Measurable (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) from
          (((measurable_const.add measurable_id).pow_const (-p)).sub measurable_const).mul
            (measurable_id.pow_const (-a))))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hv' := hv
      have hpow : 0 < v ^ (-a) := Real.rpow_pos_of_pos hv'.1 _
      have hpowmul : v * v ^ (-a) = v ^ (1 - a) := by
        calc
          v * v ^ (-a) = v ^ (1 : ℝ) * v ^ (-a) := by rw [Real.rpow_one]
          _ = v ^ (1 + (-a)) := by rw [← Real.rpow_add hv'.1]
          _ = v ^ (1 - a) := by congr 1
      calc
        ‖((1 + v) ^ (-p) - 1) * v ^ (-a)‖ =
            |(1 + v) ^ (-p) - 1| * v ^ (-a) := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpow]
        _ ≤ (p * v) * v ^ (-a) := mul_le_mul_of_nonneg_right (one_sub_rpow_abs_le hv') hpow.le
        _ = p * (v * v ^ (-a)) := by ring
        _ = p * v ^ (1 - a) := by rw [hpowmul]
    have htailPow : IntegrableOn (fun v : ℝ => v ^ (-a)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    have htail : IntegrableOn
        (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) (Ioi 1) := by
      apply htailPow.integrable.mono' (Measurable.aestronglyMeasurable
        (show Measurable (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) from
          (((measurable_const.add measurable_id).pow_const (-p)).sub measurable_const).mul
            (measurable_id.pow_const (-a))))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hvpos := lt_trans zero_lt_one hv
      have : 0 ≤ (1 + v) ^ (-p) := Real.rpow_nonneg (by linarith [hv]) _
      have hle : (1 + v) ^ (-p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hv]) (by linarith)
      have hpow : 0 ≤ v ^ (-a) := Real.rpow_nonneg hvpos.le _
      calc
        ‖((1 + v) ^ (-p) - 1) * v ^ (-a)‖ =
            |(1 + v) ^ (-p) - 1| * v ^ (-a) := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
        _ ≤ v ^ (-a) := by simpa using mul_le_mul_of_nonneg_right (show |(1 + v) ^ (-p) - 1| ≤ 1 by rw [abs_of_nonpos (sub_nonpos.mpr hle)]; linarith) hpow
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    exact ⟨hnear, htail⟩
  have beta_change_variables (x : ℝ) (y : ℝ) : (∫ v : ℝ in Ioi 0, v ^ (x - 1) * (1 + v) ^ (-(x + y))) = ∫ t : ℝ in Ioc 0 1, t ^ (x - 1) * (1 - t) ^ (y - 1) := by
    let f : ℝ → ℝ := fun v => v / (1 + v)
    have hImage : f '' Ioi (0 : ℝ) = Ioo 0 1 := by
      ext t
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hv' := mem_Ioi.mp hv
        have hden : 0 < 1 + v := by linarith
        constructor
        · exact div_pos hv' hden
        · rw [div_lt_one hden]
          linarith
      · rintro ⟨ht, ht1⟩
        refine ⟨t / (1 - t), div_pos ht (sub_pos.mpr ht1), ?_⟩
        dsimp [f]
        field_simp
        ring
    have hInj : InjOn f (Ioi (0 : ℝ)) := by
      intro v hv w hw h
      have := mem_Ioi.mp hv
      have := mem_Ioi.mp hw
      nlinarith [((div_eq_div_iff (by linarith) (by linarith)).mp (by simpa [f] using h) : v * (1 + w) = w * (1 + v))]
    have hderiv : ∀ v ∈ Ioi (0 : ℝ),
        HasDerivWithinAt f ((1 + v) ^ 2)⁻¹ (Ioi (0 : ℝ)) v := by
      intro v hv
      have := mem_Ioi.mp hv
      have hden : HasDerivAt (fun t => 1 + t) 1 v := by
        convert (hasDerivAt_id v).const_add 1 using 1
        · funext t
          simp
      have hfun : HasDerivAt (fun t => t / (1 + t)) ((1 + v) ^ 2)⁻¹ v := by
        convert ((hasDerivAt_id v).div hden (show 0 < 1 + v by linarith).ne') using 1
        · rfl
        · field_simp
          simp only [id_eq]
          ring
      simpa only [f] using hfun.hasDerivWithinAt
    have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Ioi (0 : ℝ)) (f := f) (f' := fun v => ((1 + v) ^ 2)⁻¹)
      measurableSet_Ioi hderiv hInj (fun t => t ^ (x - 1) * (1 - t) ^ (y - 1))
    rw [hImage] at hchange
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc] at hchange
    calc
      ∫ v : ℝ in Ioi 0, v ^ (x - 1) * (1 + v) ^ (-(x + y))
          = ∫ v : ℝ in Ioi 0,
            |((1 + v) ^ 2)⁻¹| * ((f v) ^ (x - 1) * (1 - f v) ^ (y - 1)) := by
              symm
              apply setIntegral_congr_fun measurableSet_Ioi
              intro v hv
              have hv0 : 0 < v := hv
              have hd : 0 < 1 + v := by linarith
              change |((1 + v) ^ 2)⁻¹| *
                  ((f v) ^ (x - 1) * (1 - f v) ^ (y - 1)) =
                v ^ (x - 1) * (1 + v) ^ (-(x + y))
              have hcomp : 1 - f v = 1 / (1 + v) := by
                dsimp [f]
                field_simp
                ring
              rw [hcomp, abs_of_pos (by positivity), ← Real.rpow_natCast (1 + v) 2, Real.div_rpow hv0.le hd.le, Real.div_rpow zero_le_one hd.le, Real.one_rpow, Real.rpow_neg hd.le]
              have hpowers : (1 + v) ^ (2 : ℝ) * (1 + v) ^ (x - 1) * (1 + v) ^ (y - 1) =
                  (1 + v) ^ (x + y) := by
                rw [← Real.rpow_add hd, ← Real.rpow_add hd]
                congr 1
                ring
              field_simp [ne_of_gt (Real.rpow_pos_of_pos hd (x - 1)),
                ne_of_gt (Real.rpow_pos_of_pos hd (y - 1)),
                ne_of_gt (Real.rpow_pos_of_pos hd (x + y))]
              rw [← hpowers]
              ring_nf
      _ = ∫ t : ℝ in Ioc 0 1, t ^ (x - 1) * (1 - t) ^ (y - 1) := hchange.symm
  have hintegrable := beta_negative_power_integrable
  refine ⟨hintegrable, ?_⟩
  let g : ℝ → ℝ := fun x => (1 + x) ^ (-p) - 1
  let G : ℝ → ℝ := fun x => x ^ (1 - a) / (1 - a)
  let gp : ℝ → ℝ := fun x => (-p) * (1 + x) ^ (-p - 1)
  let Gp : ℝ → ℝ := fun x => x ^ (-a)
  have hgderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (gp x) x := by
    intro x hx
    have : 0 < x := hx
    simpa [g, gp, mul_one, sub_eq_add_neg] using ((Real.hasDerivAt_rpow_const (x := 1 + x) (p := -p) (Or.inl (by linarith))).comp x ((hasDerivAt_id x).const_add 1)).sub_const 1
  have hlimits := beta_product_tends_zero
  have hbetaC := Complex.betaIntegral_eq_Gamma_mul_div
    ((2 - a : ℝ) : ℂ) ((p + a - 1 : ℝ) : ℂ)
    (by simpa using (by linarith)) (by simpa using (by linarith))
  rw [betaIntegral_ofReal] at hbetaC
  have hbetaR :
      (∫ t : ℝ in Ioc 0 1, t ^ ((2 - a) - 1) * (1 - t) ^ ((p + a - 1) - 1)) =
      Real.Gamma (2 - a) * Real.Gamma (p + a - 1) / Real.Gamma (p + 1) := by
    apply Complex.ofReal_injective
    have hbetaC' := hbetaC
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      Complex.Gamma_ofReal,
      show (2 - a) + (p + a - 1) = p + 1 by ring] at hbetaC'
    simpa [Complex.ofReal_mul, Complex.ofReal_div] using hbetaC'
  have hparts :
      (∫ v : ℝ in Ioi 0, g v * Gp v) =
        -(((-p) / (1 - a)) *
          (∫ v : ℝ in Ioi 0, v ^ (1 - a) * (1 + v) ^ (-(p + 1)))) := by
    rw [(integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (u := g) (v := G) (u' := gp) (v' := Gp) hgderiv (by intro x hx; convert ((Real.hasDerivAt_rpow_const (x := x) (p := 1 - a) (Or.inl hx.ne')).div_const (1 - a)) using 1; simpa [Gp] using (show (1 - a) * x ^ ((1 - a) - 1) / (1 - a) = x ^ (-a) by rw [show (1 - a) - 1 = -a by ring]; exact mul_div_cancel_left₀ _ (by linarith : 1 - a ≠ 0)).symm) (by simpa [g, Gp, Pi.mul_def] using hintegrable) (by simpa [gp, G, Pi.mul_def] using beta_ibp_derivative_integrable) (by simpa [g, G, Pi.mul_def] using hlimits.1) (by simpa [g, G, Pi.mul_def] using hlimits.2))]
    have hfun : gp * G = fun v : ℝ =>
        ((-p) / (1 - a)) * (v ^ (1 - a) * (1 + v) ^ (-(p + 1))) := by
      funext v
      dsimp [gp, G]
      rw [show -p - 1 = -(p + 1) by ring]
      field_simp [(show 1 - a ≠ 0 by linarith)]
    rw [(show (∫ v : ℝ in Ioi 0, gp v * G v) = ((-p) / (1 - a)) * (∫ v : ℝ in Ioi 0, v ^ (1 - a) * (1 + v) ^ (-(p + 1))) by rw [Pi.mul_def] at hfun; rw [hfun, integral_const_mul])]
    simp
  rw [((show (∫ v : ℝ in Ioi 0, v ^ (1 - a) * (1 + v) ^ (-(p + 1))) = ∫ t : ℝ in Ioc 0 1, t ^ ((2 - a) - 1) * (1 - t) ^ ((p + a - 1) - 1) by simpa only [show (2 - a) - 1 = 1 - a by ring, show (2 - a) + (p + a - 1) = p + 1 by ring] using (beta_change_variables (2 - a) (p + a - 1))).trans hbetaR)] at hparts
  rw [(show -(((-p) / (1 - a)) * (Real.Gamma (2 - a) * Real.Gamma (p + a - 1) / Real.Gamma (p + 1))) = Real.Gamma (1 - a) * Real.Gamma (p + a - 1) / Real.Gamma p by rw [show 2 - a = (1 - a) + 1 by ring, Real.Gamma_add_one (by linarith : 1 - a ≠ 0), Real.Gamma_add_one hp.ne']; field_simp [hp.ne', ne_of_gt (Real.Gamma_pos_of_pos hp), (by linarith : 1 - a ≠ 0)])] at hparts
  simpa [g, Gp] using hparts

end DOZZ.Proofs
