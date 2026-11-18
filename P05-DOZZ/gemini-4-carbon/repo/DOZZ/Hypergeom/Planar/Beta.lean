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
  refine (integral_congr_ae (g := fun t : ℝ => ((t ^ (x - 1) * (1 - t) ^ (y - 1) : ℝ) : ℂ))
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_)).trans integral_ofReal
  dsimp only
  rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
    show (y : ℂ) - 1 = ((y - 1 : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - (t : ℝ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht.1.le, ← Complex.ofReal_cpow (sub_nonneg.2 ht.2), ← Complex.ofReal_mul]


/-- The signed negative-power integral from the one-dimensional identity of [KRV, Lemma 12.6]. -/
theorem beta_negative_power_integral (p a : ℝ) (hp : 0 < p) (ha : 1 < a) (ha₂ : a < 2) :
    IntegrableOn (fun v : ℝ => ((1 + v) ^ (-p) - 1) * v ^ (-a)) (Ioi 0) ∧
      (∫ v : ℝ in Ioi 0, ((1 + v) ^ (-p) - 1) * v ^ (-a)) =
        Real.Gamma (1 - a) * Real.Gamma (p + a - 1) / Real.Gamma p := by
  have integrableOn_Ioi_of_split {f : ℝ → ℝ} (hf : Measurable f) {A B α β : ℝ} (hα : -1 < α) (hβ : β < -1) (hnear : ∀ v ∈ Ioc (0 : ℝ) 1, ‖f v‖ ≤ A * v ^ α) (htail : ∀ v ∈ Ioi (1 : ℝ), ‖f v‖ ≤ B * v ^ β) : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    have hn : IntegrableOn (fun v : ℝ => v ^ α) (Ioc 0 1) := by
      rw [integrableOn_congr_set_ae Ioo_ae_eq_Ioc.symm]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hα
    exact ⟨(hn.integrable.const_mul A).mono' hf.aestronglyMeasurable
        ((ae_restrict_mem measurableSet_Ioc).mono hnear),
      ((integrableOn_Ioi_rpow_of_lt hβ zero_lt_one).integrable.const_mul B).mono'
        hf.aestronglyMeasurable ((ae_restrict_mem measurableSet_Ioi).mono htail)⟩
  let g (x : ℝ) := (1 + x) ^ (-p) - 1
  let G (x : ℝ) := x ^ (1 - a) / (1 - a)
  let gp (x : ℝ) := (-p) * (1 + x) ^ (-p - 1)
  let Gp (x : ℝ) := x ^ (-a)
  have ha1_pos : 0 < a - 1 := sub_pos.2 ha
  have ha1_neg : 1 - a < 0 := sub_neg.2 ha
  have hg_near {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) 1) : |g v| ≤ p * v := by
    have hd : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => (1 + y) ^ (-p)) ((-p) * (1 + x) ^ (-p - 1)) x :=
      fun x hx => by
        simpa [Function.comp_def] using (Real.hasDerivAt_rpow_const (x := 1 + x) (p := -p)
          (Or.inl (by linarith [hx.1]))).comp x ((hasDerivAt_id x).const_add 1)
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun x hx => (hd x hx).differentiableAt)
      (fun x hx => by
        rw [(hd x hx).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hp,
          abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)]
        exact mul_le_of_le_one_right hp.le (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by linarith)))
      (convex_Icc 0 1) (left_mem_Icc.2 zero_le_one) ⟨hv.1.le, hv.2⟩
    simpa [g, Real.norm_eq_abs, abs_of_pos hv.1] using hmv
  have hg_tail {v : ℝ} (hv : 1 < v) : |g v| ≤ 1 := by
    have h0 : 0 ≤ (1 + v) ^ (-p) := Real.rpow_nonneg (by linarith) _
    have h1 : (1 + v) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    rw [abs_of_nonpos (sub_nonpos.2 h1)]; linarith
  have hG_abs {x : ℝ} (hx : 0 < x) : |G x| = x ^ (1 - a) / (a - 1) := by
    dsimp [G]; rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hx _), abs_of_neg ha1_neg, neg_sub]
  have hleft : IntegrableOn (fun v => g v * Gp v) (Ioi 0) :=
    integrableOn_Ioi_of_split (by dsimp [g, Gp]; fun_prop) (by linarith : -1 < 1 - a) (by linarith : -a < -1)
      (A := p) (B := 1)
      (fun v hv => by
        have hpv : 0 < v ^ (-a) := Real.rpow_pos_of_pos hv.1 _
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpv]
        refine (mul_le_mul_of_nonneg_right (hg_near hv) hpv.le).trans_eq ?_
        rw [mul_assoc, ← Real.rpow_one_add' hv.1.le (by linarith)]; ring_nf)
      (fun v hv => by
        have hv0 : 0 < v := lt_trans zero_lt_one hv
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hv0 _), one_mul]
        exact mul_le_of_le_one_left (Real.rpow_nonneg hv0.le _) (hg_tail hv))
  have hright : IntegrableOn (gp * G) (Ioi 0) :=
    integrableOn_Ioi_of_split (by dsimp [gp, G]; fun_prop) (by linarith : -1 < 1 - a)
      (by linarith : -p - a < -1) (A := p / (a - 1)) (B := p / (a - 1))
      (fun v hv => by
        rw [Pi.mul_def, Real.norm_eq_abs, abs_mul, hG_abs hv.1]
        dsimp only [gp]; rw [abs_mul, abs_neg, abs_of_pos hp,
          abs_of_pos (Real.rpow_pos_of_pos (by linarith [hv.1]) _)]
        have h1 : (1 + v) ^ (-p - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hv.1]) (by linarith)
        have hvpos := (Real.rpow_pos_of_pos hv.1 (1 - a)).le
        calc p * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (a - 1))
          _ ≤ p * 1 * (v ^ (1 - a) / (a - 1)) := by gcongr
          _ = p / (a - 1) * v ^ (1 - a) := by ring)
      (fun v hv => by
        have hv0 : 0 < v := lt_trans zero_lt_one hv
        rw [Pi.mul_def, Real.norm_eq_abs, abs_mul, hG_abs hv0]
        dsimp only [gp]; rw [abs_mul, abs_neg, abs_of_pos hp,
          abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
        have h1 : (1 + v) ^ (-p - 1) ≤ v ^ (-p - 1) :=
          Real.rpow_le_rpow_of_nonpos hv0 (by linarith) (by linarith)
        have hvpos := (Real.rpow_pos_of_pos hv0 (1 - a)).le
        calc p * (1 + v) ^ (-p - 1) * (v ^ (1 - a) / (a - 1))
          _ ≤ p * v ^ (-p - 1) * (v ^ (1 - a) / (a - 1)) := by gcongr
          _ = p / (a - 1) * (v ^ (-p - 1) * v ^ (1 - a)) := by ring
          _ = p / (a - 1) * v ^ (-p - a) := by rw [← Real.rpow_add hv0]; congr 2; ring)
  refine ⟨hleft, ?_⟩
  have hlim0 : Tendsto (fun x => g x * G x) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero' (g := fun x => p / (a - 1) * x ^ (2 - a))
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_)
    · filter_upwards [eventually_mem_nhdsWithin,
        (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with x hx hx1
      rw [Real.norm_eq_abs, abs_mul, hG_abs hx]
      calc |g x| * (x ^ (1 - a) / (a - 1))
        _ ≤ (p * x) * (x ^ (1 - a) / (a - 1)) :=
            mul_le_mul_of_nonneg_right (hg_near ⟨hx, hx1.le⟩) (div_nonneg (Real.rpow_nonneg hx.le _) ha1_pos.le)
        _ = p / (a - 1) * (x * x ^ (1 - a)) := by ring
        _ = p / (a - 1) * x ^ (2 - a) := by
            congr 1; rw [← Real.rpow_one_add' hx.le (by linarith)]; congr 1; ring
    · have hp0 : Tendsto (fun x : ℝ => x ^ (2 - a)) (𝓝[>] 0) (𝓝 0) := by
        simpa [Real.zero_rpow (by linarith : 2 - a ≠ 0)] using
          (Real.continuousAt_rpow_const 0 (2 - a) (Or.inr (by linarith))).mono_left nhdsWithin_le_nhds
      simpa using hp0.const_mul (p / (a - 1))
  have hlimTop : Tendsto (fun x => g x * G x) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero' (g := fun x => 1 / (a - 1) * x ^ (1 - a))
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      rw [Real.norm_eq_abs, abs_mul, hG_abs hx0]
      exact (mul_le_of_le_one_left (div_nonneg (Real.rpow_nonneg hx0.le _) ha1_pos.le) (hg_tail hx)).trans_eq (by ring)
    · have hpT : Tendsto (fun x : ℝ => x ^ (1 - a)) atTop (𝓝 0) := by
        simpa [sub_eq_add_neg] using tendsto_rpow_neg_atTop ha1_pos
      simpa using hpT.const_mul (1 / (a - 1))
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (u := g) (v := G) (u' := gp) (v' := Gp)
    (fun x hx => by
      have : 0 < x := hx
      simpa [g, gp, mul_one, sub_eq_add_neg] using
        ((Real.hasDerivAt_rpow_const (x := 1 + x) (p := -p) (Or.inl (by linarith))).comp x
          ((hasDerivAt_id x).const_add 1)).sub_const 1)
    (fun x (hx : 0 < x) => by
      convert (Real.hasDerivAt_rpow_const (x := x) (p := 1 - a) (Or.inl hx.ne')).div_const (1 - a) using 1
      dsimp [Gp]; rw [show 1 - a - 1 = -a by ring, mul_div_cancel_left₀ _ ha1_neg.ne])
    hleft hright hlim0 hlimTop
  have hchg : (∫ v : ℝ in Ioi 0, v ^ (1 - a) * (1 + v) ^ (-(p + 1))) =
      ∫ t : ℝ in Ioc 0 1, t ^ ((2 - a) - 1) * (1 - t) ^ ((p + a - 1) - 1) := by
    let f (v : ℝ) := v / (1 + v)
    have hImg : f '' Ioi (0 : ℝ) = Ioo 0 1 := by
      ext t; constructor
      · rintro ⟨v, hv : 0 < v, rfl⟩
        exact ⟨div_pos hv (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
      · rintro ⟨ht0, ht1⟩
        refine ⟨t / (1 - t), div_pos ht0 (sub_pos.2 ht1), ?_⟩
        dsimp [f]; field_simp [show 1 - t ≠ 0 by linarith]; ring
    have hInj : InjOn f (Ioi 0) := fun v (hv : 0 < v) w (hw : 0 < w) h => by
      have := (div_eq_div_iff (by linarith : 1 + v ≠ 0) (by linarith : 1 + w ≠ 0)).1 h
      linarith
    have hder : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt f (((1 + v) ^ 2)⁻¹) (Ioi 0) v := fun v (hv : 0 < v) => by
      have hd : 0 < 1 + v := by linarith
      have hd1 : HasDerivAt (fun t : ℝ => 1 + t) 1 v := by simpa using (hasDerivAt_id v).const_add 1
      exact (((hasDerivAt_id v).div hd1 hd.ne').congr_deriv (by field_simp [hd.ne']; simp)).hasDerivWithinAt
    have hc := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hInj
      (fun t : ℝ => t ^ ((2 - a) - 1) * (1 - t) ^ ((p + a - 1) - 1))
    rw [hImg, setIntegral_congr_set Ioo_ae_eq_Ioc] at hc
    refine (setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_).trans hc.symm
    have hd : 0 < 1 + v := by linarith
    dsimp only [f, smul_eq_mul]
    rw [show 1 - v / (1 + v) = 1 / (1 + v) by field_simp [hd.ne']; ring,
      abs_of_pos (by positivity), ← Real.rpow_natCast (1 + v) 2,
      Real.div_rpow hv.le hd.le, Real.div_rpow zero_le_one hd.le, Real.one_rpow,
      show 2 - a - 1 = 1 - a by ring, Real.rpow_neg hd.le]
    have hpows : (1 + v) ^ (2 : ℝ) * (1 + v) ^ (1 - a) * (1 + v) ^ (p + a - 1 - 1) = (1 + v) ^ (p + 1) := by
      rw [← Real.rpow_add hd, ← Real.rpow_add hd]; congr 1; ring
    field_simp [(Real.rpow_pos_of_pos hd _).ne', (Real.rpow_pos_of_pos hd _).ne',
      (Real.rpow_pos_of_pos hd _).ne']
    rw [← hpows]; ring
  have hbetaC := Complex.betaIntegral_eq_Gamma_mul_div ((2 - a : ℝ) : ℂ) ((p + a - 1 : ℝ) : ℂ)
    (by simp; linarith) (by simp; linarith)
  rw [betaIntegral_ofReal, ← Complex.ofReal_add, show 2 - a + (p + a - 1) = p + 1 by ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hbetaC
  have hbetaR : (∫ t : ℝ in Ioc 0 1, t ^ ((2 - a) - 1) * (1 - t) ^ ((p + a - 1) - 1)) =
      Real.Gamma (2 - a) * Real.Gamma (p + a - 1) / Real.Gamma (p + 1) :=
    Complex.ofReal_injective (by simpa [Complex.ofReal_mul, Complex.ofReal_div] using hbetaC)
  have hgpG : (∫ v : ℝ in Ioi 0, gp v * G v) =
      (-p / (1 - a)) * ∫ v : ℝ in Ioi 0, v ^ (1 - a) * (1 + v) ^ (-(p + 1)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun v _ => by
      dsimp [gp, G]; rw [show -p - 1 = -(p + 1) by ring]; ring
  rw [show (∫ v : ℝ in Ioi 0, ((1 + v) ^ (-p) - 1) * v ^ (-a)) = ∫ v : ℝ in Ioi 0, g v * Gp v from rfl,
    hibp, hgpG, hchg, hbetaR, show 2 - a = (1 - a) + 1 by ring,
    Real.Gamma_add_one ha1_neg.ne, Real.Gamma_add_one hp.ne']
  field_simp [hp.ne', (Real.Gamma_pos_of_pos hp).ne', ha1_neg.ne]; ring

end DOZZ.Proofs
