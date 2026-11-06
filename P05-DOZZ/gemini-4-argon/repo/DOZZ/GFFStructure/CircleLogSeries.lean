/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CirclePotential
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Integrated logarithmic circle series

The quadratic Fourier majorant is uniform up to unit radius ratio. Complex Taylor expansion,
termwise arc integration and continuous extension give the exact clipped intersection formula,
including equal center distance and radius. All computations use the series coefficients of
`DOZZ.circleLogPotential`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology Interval

namespace DOZZ.Proofs

/-- Fourier coefficient in the clipped circle potential `DOZZ.circleLogPotential`. -/
noncomputable def circleLogSeriesTerm (u θ : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ)^k * u^(k+1) * Real.sin ((k+1 : ℕ)*θ) / ((k+1 : ℕ) : ℝ)^2











/-- The logarithmic arc section has no pole before the antipodal angle, including u = 1. -/
theorem circleLogSection_ne_zero {u t : ℝ} (hu : u ∈ Icc 0 1) (ht : t ∈ Ico 0 Real.pi) :
    1 + (u : ℂ) * Complex.exp ((t : ℂ)*Complex.I) ≠ 0 := by
  have hp : 0 < 1 + u * Real.cos t := by
    by_cases hcos : 0 ≤ Real.cos t
    · exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hu.1 hcos)
    · have hm := mul_le_mul_of_nonpos_right hu.2 (le_of_not_ge hcos)
      simp only [one_mul] at hm
      linarith only [hm, (by simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi ht.1 le_rfl ht.2)]
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.zero_re] at hr
  linarith only [hr, hp]






/-- Squared geometric circle distance in cosine coordinates. -/
theorem norm_circleLogSection_sq (d a t : ℝ) :
    ‖(d : ℂ) + (a : ℂ) * Complex.exp ((t : ℂ)*Complex.I)‖^2 =
      d^2 + a^2 + 2*d*a*Real.cos t := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_add]
  linear_combination a ^ 2 * Real.sin_sq_add_cos_sq t




/-- Interior intersection produces an arccos argument strictly between minus one and one. -/
theorem circleLog_intersection_argument {d a b} (hd : 0 < d) (ha : 0 < a)
    (hb : 0 < b) (hupper : b < d+a) (hlower : |d-a| < b) :
    (b^2-d^2-a^2)/(2*d*a) ∈ Ioo (-1 : ℝ) 1 := by
  have hden : 0 < 2*d*a := by positivity
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith only [(by simpa only [sq_abs, ← sq] using (mul_self_lt_mul_self (abs_nonneg (d-a)) hlower))]
  · apply (div_lt_iff₀ hden).mpr
    linarith only [(mul_self_lt_mul_self hb.le hupper)]

/-- The angular cutoff of `DOZZ.circleLogPotential` is strictly before the antipodal singularity. -/
theorem circleLog_intersection_angle {d a b} (hd : 0 < d) (ha : 0 < a)
    (hb : 0 < b) (hupper : b < d+a) (hlower : |d-a| < b) :
    Real.arccos ((b^2-d^2-a^2)/(2*d*a)) ∈ Ioo (0 : ℝ) Real.pi := by
  have h := circleLog_intersection_argument hd ha hb hupper hlower
  exact ⟨Real.arccos_pos.mpr h.2, Real.arccos_lt_pi.mpr h.1⟩

/-- The geometric circle section decreases in angle on the upper semicircle. -/
theorem antitoneOn_norm_circleLogSection {d a : ℝ} (hd : 0 ≤ d) (ha : 0 ≤ a) :
    AntitoneOn (fun t : ℝ => ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)
      (Icc (0 : ℝ) Real.pi) := by
  intro t ht s hs hts
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith only [(norm_circleLogSection_sq d a t), (norm_circleLogSection_sq d a s), (mul_le_mul_of_nonneg_left (Real.antitoneOn_cos ht hs hts) (show 0 ≤ 2*d*a by positivity))])

/-- The arccos cutoff is exactly where the circle section crosses the clipping radius. -/
theorem norm_circleLogSection_cutoff {d a b : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hb : 0 < b) (hupper : b < d+a) (hlower : |d-a| < b) :
    ‖(d : ℂ)+(a : ℂ)*Complex.exp
      ((Real.arccos ((b^2-d^2-a^2)/(2*d*a)) : ℂ)*Complex.I)‖ = b := by
  have hk := circleLog_intersection_argument hd ha hb hupper hlower
  have hnorm := norm_circleLogSection_sq d a (Real.arccos ((b^2-d^2-a^2)/(2*d*a)))
  rw [Real.cos_arccos hk.1.le hk.2.le, mul_div_cancel₀ _ (show 2*d*a ≠ 0 by positivity)] at hnorm
  exact (pow_left_inj₀ (norm_nonneg _) hb.le two_ne_zero).1 (by rw [hnorm]; ring)


/-- Arc integration of the unnormalized section gives the quadratic Fourier series
`circleLogSeriesTerm`. -/
theorem integral_geometric_circleLog_arc {d a θ : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hθ : θ ∈ Ico 0 Real.pi) :
    (∫ t in 0..θ, Real.log ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖) =
      θ*Real.log (max d a) + ∑' k, circleLogSeriesTerm (min d a / max d a) θ k := by
  have intervalIntegrable_circleLogSection {u : ℝ} {θ} (hu : u ∈ Icc 0 1) (hθ : θ ∈ Ico 0 Real.pi) : IntervalIntegrable (fun t : ℝ => Real.log ‖1+(u : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖) volume 0 θ := by
    have hc : ContinuousOn (fun t : ℝ => Real.log
        ‖1+(u : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖) (uIcc 0 θ) := by
      apply ContinuousOn.log (by fun_prop)
      intro t ht
      rw [uIcc_of_le hθ.1] at ht
      exact norm_ne_zero_iff.mpr (circleLogSection_ne_zero hu ⟨ht.1, ht.2.trans_lt hθ.2⟩)
    exact hc.intervalIntegrable
  have norm_circleLogSection_factor (t : ℝ) : ‖(d : ℂ) + (a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖ = max d a * ‖1 + ((min d a / max d a : ℝ) : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖ := by
    have norm_circleLogSection_swap (d : ℝ) (a : ℝ) (t : ℝ) : ‖(d : ℂ) + (a : ℂ) * Complex.exp ((t : ℂ)*Complex.I)‖ = ‖(a : ℂ) + (d : ℂ) * Complex.exp ((t : ℂ)*Complex.I)‖ := by
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by rw [(norm_circleLogSection_sq d a t), (norm_circleLogSection_sq a d t)]; ring)
    have hfactor (c b : ℝ) (hc : 0 < c) :
        ‖(c : ℂ) + (b : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖ =
          c * ‖1 + ((b/c : ℝ) : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖ := by
      rw [(show (c : ℂ) + (b : ℂ)*Complex.exp ((t : ℂ)*Complex.I) = (c : ℂ)*(1 + ((b/c : ℝ) : ℂ)*Complex.exp ((t : ℂ)*Complex.I)) by push_cast; field_simp [Complex.ofReal_ne_zero.mpr hc.ne']), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rcases le_total a d with h | h
    · rw [max_eq_left h, min_eq_right h]
      exact hfactor d a hd
    · rw [max_eq_right h, min_eq_left h, norm_circleLogSection_swap]
      exact hfactor a d ha
  have circleLog_ratio_mem_Icc : min d a / max d a ∈ Icc (0 : ℝ) 1 := by
    have hc : 0 < max d a := hd.trans_le (le_max_left _ _)
    exact ⟨div_nonneg (le_min hd.le ha.le) hc.le,
      (div_le_one hc).mpr (le_trans (min_le_left _ _) (le_max_left _ _))⟩
  have integral_circleLog_eq_tsum_closed {u : ℝ} {θ} (hu : u ∈ Icc 0 1) (hθ : θ ∈ Ico 0 Real.pi) : (∫ t in 0..θ, Real.log ‖1 + (u : ℂ) * Complex.exp ((t : ℂ)*Complex.I)‖) = ∑' k, circleLogSeriesTerm u θ k := by
    have continuous_circleLogArc : Continuous (fun u : Icc (0 : ℝ) 1 => ∫ t in 0..θ, Real.log ‖1 + (u.val : ℂ) * Complex.exp ((t : ℂ)*Complex.I)‖) := by
      let clip : ℝ → ℝ := fun t => max 0 (min θ t)
      apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) (f := fun u : Icc (0 : ℝ) 1 => fun t : ℝ => Real.log ‖1 + (u.val : ℂ) * Complex.exp ((clip t : ℂ)*Complex.I)‖) (by apply Continuous.log (by unfold clip; fun_prop); intro p; exact norm_ne_zero_iff.mpr (circleLogSection_ne_zero p.1.property ((fun t => by exact ⟨le_max_left _ _, (max_le hθ.1 (min_le_left _ _)).trans_lt hθ.2⟩) p.2))) 0 θ).congr
      intro u
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hθ.1] at ht
      dsimp only [clip]
      rw [min_eq_right ht.2, max_eq_right ht.1]
    have hasSum_integral_circleLogCosine {u : ℝ} (hu : u ∈ Ico 0 1) θ : HasSum (circleLogSeriesTerm u θ) (∫ t in 0..θ, Real.log ‖1 + (u : ℂ) * Complex.exp ((t : ℂ)*Complex.I)‖) := by
      have norm_circleLogCosine_le {u} (hu : u ∈ Icc 0 1) t k : ‖(-1 : ℝ)^k * u^(k+1) * Real.cos ((k+1 : ℕ)*t) / ((k+1 : ℕ) : ℝ)‖ ≤ u^k := by
        have hp : 0 ≤ u^(k+1) := pow_nonneg hu.1 _
        simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
          one_pow, one_mul, abs_of_nonneg hu.1,
          abs_of_nonneg (Nat.cast_nonneg (k+1) : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ))]
        calc
          _ ≤ u^(k+1) / ((k+1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_of_le_one_right hp (Real.abs_cos_le_one _)) (by positivity)
          _ ≤ u^(k+1) := div_le_self hp (by norm_cast; omega)
          _ ≤ u^k := by rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hu.1 _) hu.2
      have hasSum_circleLogCosine {u : ℝ} (hu : |u| < 1) (t : ℝ) : HasSum (fun k : ℕ => (-1 : ℝ)^k * u^(k+1) * Real.cos ((k+1 : ℕ)*t) / ((k+1 : ℕ) : ℝ)) (Real.log ‖1 + (u : ℂ) * Complex.exp ((t : ℂ)*Complex.I)‖) := by
        have re_circleLogTaylorTerm k : ((-1 : ℂ)^(k+1+1) * ((u : ℂ) * Complex.exp ((t : ℂ)*Complex.I))^(k+1) / ((k+1 : ℕ) : ℂ)).re = (-1 : ℝ)^k * u^(k+1) * Real.cos ((k+1 : ℕ)*t) / ((k+1 : ℕ) : ℝ) := by
          have hexp : Complex.exp ((t : ℂ)*Complex.I)^(k+1) =
              Complex.exp (((k+1 : ℕ)*t : ℝ) * Complex.I) := by
            rw [← Complex.exp_nat_mul]
            congr 1
            push_cast
            ring
          rw [(show (-1 : ℂ)^(k+1+1) = ((-1 : ℝ)^k : ℂ) by simp only [pow_add, pow_one, Complex.ofReal_neg, Complex.ofReal_one]; ring), mul_pow, hexp]
          simp only [← Complex.ofReal_pow]
          rw [← mul_assoc, ← Complex.ofReal_mul]
          change ((↑((-1 : ℝ)^k * u^(k+1)) *
            Complex.exp ((↑(((k+1 : ℕ) : ℝ)*t))*Complex.I)) /
            (↑((k+1 : ℕ) : ℝ) : ℂ)).re = _
          rw [Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
        let z := (u : ℂ) * Complex.exp ((t : ℂ)*Complex.I)
        have h := Complex.hasSum_re ((hasSum_nat_add_iff 1 (f := fun n : ℕ => (-1 : ℂ)^(n+1) * z^n / (n : ℂ))).mpr (by simpa only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, add_zero] using (Complex.hasSum_taylorSeries_log (by simpa only [z, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one] using hu))))
        rw [Complex.log_re] at h
        exact h.congr_fun (fun k => (re_circleLogTaylorTerm k).symm)
      have integral_circleLogCosine u θ k : (∫ t in 0..θ, (-1 : ℝ)^k * u^(k+1) * Real.cos ((k+1 : ℕ)*t) / ((k+1 : ℕ) : ℝ)) = circleLogSeriesTerm u θ k := by
        rw [show (fun t => (-1 : ℝ)^k * u^(k+1) * Real.cos ((k+1 : ℕ)*t) /
          ((k+1 : ℕ) : ℝ)) = (fun t => ((-1 : ℝ)^k * u^(k+1) /
          ((k+1 : ℕ) : ℝ)) * Real.cos (((k+1 : ℕ) : ℝ)*t)) by funext t; ring]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ (show ((k+1 : ℕ) : ℝ) ≠ 0 by positivity),
          integral_cos]
        simp only [mul_zero, Real.sin_zero, sub_zero, circleLogSeriesTerm]
        ring
      simpa only [integral_circleLogCosine] using (intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (fun k (_ : ℝ) => u^k) (fun k => (show Continuous (fun t => (-1 : ℝ)^k * u^(k+1) * Real.cos ((k+1 : ℕ)*t) / ((k+1 : ℕ) : ℝ)) from by fun_prop).aestronglyMeasurable) (fun k => Eventually.of_forall (fun t _ => norm_circleLogCosine_le ⟨hu.1, hu.2.le⟩ t k)) (Eventually.of_forall (fun _ _ => summable_geometric_of_lt_one hu.1 hu.2)) (intervalIntegrable_const (a := 0) (b := θ)) (Eventually.of_forall (fun t _ => hasSum_circleLogCosine (by rw [abs_of_nonneg hu.1]; exact hu.2) t)))
    have continuous_circleLogSeries : Continuous (fun p : Icc (0 : ℝ) 1 × ℝ => ∑' k, circleLogSeriesTerm p.1.val p.2 k) := by
      have norm_circleLogSeriesTerm_le {u} (hu : u ∈ Icc 0 1) θ k : ‖circleLogSeriesTerm u θ k‖ ≤ 1 / ((k+1 : ℕ) : ℝ)^2 := by
        simp only [circleLogSeriesTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
          abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg (k+1) : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ))]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        calc
          _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg u) (by rw [abs_of_nonneg hu.1]; exact hu.2)) (Real.abs_sin_le_one ((k+1 : ℕ)*θ)) (abs_nonneg _) (by norm_num)
          _ = _ := one_mul _
      apply continuous_tsum (fun k => by unfold circleLogSeriesTerm; fun_prop)
        ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num)))
      intro k p
      exact norm_circleLogSeriesTerm_le p.1.property p.2 k
    have himage : Subtype.val '' {u : Icc (0 : ℝ) 1 | u.val < 1} = Ico (0 : ℝ) 1 := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.property.1, hw⟩
      · intro hv
        exact ⟨⟨v, hv.1, hv.2.le⟩, hv.2, rfl⟩
    apply (show EqOn (fun u : Icc (0 : ℝ) 1 => ∫ t in 0..θ, Real.log ‖1 + (u.val : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖) (fun u : Icc (0 : ℝ) 1 => ∑' k, circleLogSeriesTerm u.val θ k) {u : Icc (0 : ℝ) 1 | u.val < 1} by intro v hv; exact (fun {u : ℝ} (hu : u ∈ Ico 0 1) (θ : ℝ) => (hasSum_integral_circleLogCosine hu θ).tsum_eq.symm) ⟨v.property.1, hv⟩ θ).closure (continuous_circleLogArc) (continuous_circleLogSeries.comp (continuous_id.prodMk continuous_const)) (x := ⟨u, hu⟩)
    rw [closure_subtype, himage, closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    exact hu
  have hu := circleLog_ratio_mem_Icc
  have heq : EqOn (fun t : ℝ => Real.log
      ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)
      (fun t => Real.log (max d a) + Real.log
        ‖1+((min d a/max d a : ℝ) : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖) (uIcc 0 θ) := by
    intro t ht
    rw [uIcc_of_le hθ.1] at ht
    dsimp only
    rw [norm_circleLogSection_factor t, Real.log_mul (hd.trans_le (le_max_left _ _)).ne'
      (norm_ne_zero_iff.mpr (circleLogSection_ne_zero hu ⟨ht.1, ht.2.trans_lt hθ.2⟩))]
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_add intervalIntegrable_const (intervalIntegrable_circleLogSection hu hθ),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_circleLog_eq_tsum_closed hu hθ]

/-- The clipped upper-semicircle potential has the exact intersecting-circle series of
`DOZZ.circleLogPotential`. -/
theorem clipped_circleLog_integral_intersection {d a b : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hb : 0 < b) (hupper : b < d+a) (hlower : |d-a| < b) :
    (1/Real.pi) * (∫ t in 0..Real.pi,
      Real.log (max b ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)) =
      let θ := Real.arccos ((b^2-d^2-a^2)/(2*d*a))
      let c := max d a
      Real.log b + θ/Real.pi*Real.log (c/b) +
        (1/Real.pi)*(∑' k, circleLogSeriesTerm (min d a/c) θ k) := by
  let θ := Real.arccos ((b^2-d^2-a^2)/(2*d*a))
  let f : ℝ → ℝ := fun t => Real.log
    (max b ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)
  have hθ := circleLog_intersection_angle hd ha hb hupper hlower
  have hf : Continuous f := by
    apply Continuous.log (by fun_prop)
    intro t
    exact (hb.trans_le (le_max_left _ _)).ne'
  have hcut := norm_circleLogSection_cutoff hd ha hb hupper hlower
  change ‖(d : ℂ)+(a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)‖ = b at hcut
  have hmono := antitoneOn_norm_circleLogSection hd.le ha.le
  have hleft : (∫ t in 0..θ, f t) =
      ∫ t in 0..θ, Real.log ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hθ.1.le] at ht
    have hbound := hmono ⟨ht.1, ht.2.trans hθ.2.le⟩ ⟨hθ.1.le, hθ.2.le⟩ ht.2
    dsimp only at hbound
    rw [hcut] at hbound
    dsimp only [f]
    rw [max_eq_right hbound]
  have hright : (∫ t in θ..Real.pi, f t) = (Real.pi-θ)*Real.log b := by
    calc
      _ = ∫ _t in θ..Real.pi, Real.log b := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hθ.2.le] at ht
        have hbound := hmono ⟨hθ.1.le, hθ.2.le⟩ ⟨hθ.1.le.trans ht.1, ht.2⟩ ht.1
        dsimp only at hbound
        rw [hcut] at hbound
        dsimp only [f]
        rw [max_eq_left hbound]
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
  change (1/Real.pi)*(∫ t in 0..Real.pi, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 θ)
      (hf.intervalIntegrable θ Real.pi), hleft, hright,
    integral_geometric_circleLog_arc hd ha ⟨hθ.1.le, hθ.2⟩]
  change (1/Real.pi)*(θ*Real.log (max d a) +
    (∑' k, circleLogSeriesTerm (min d a/max d a) θ k) +
    (Real.pi-θ)*Real.log b) = Real.log b + θ/Real.pi*Real.log (max d a/b) +
    (1/Real.pi)*(∑' k, circleLogSeriesTerm (min d a/max d a) θ k)
  rw [Real.log_div (hd.trans_le (le_max_left d a)).ne' hb.ne']
  field_simp [Real.pi_ne_zero]
  ring

end DOZZ.Proofs
