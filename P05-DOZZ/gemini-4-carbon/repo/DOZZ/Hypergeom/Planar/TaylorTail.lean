/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarTaylorRemainder
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Complex.Norm
public import DOZZ.Hypergeom.Planar.RadialCriteria

/-! Uniform second-order tail bounds for the corrected planar Taylor numerator. -/

@[expose] public section

open Set Metric MeasureTheory

namespace DOZZ.Proofs

private def segNormSq (w : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (1 - (t : ℂ) * w)

private lemma segNormSq_eq (w : ℂ) (t : ℝ) :
    segNormSq w t = 1 - 2 * t * w.re + t ^ 2 * ‖w‖ ^ 2 := by
  dsimp [segNormSq]
  rw [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq]
  simp [Complex.mul_re]; ring

private lemma segNormSq_bounds (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 4 ≤ segNormSq w t ∧ segNormSq w t ≤ 9 / 4 := by
  have hv : ‖(t : ℂ) * w‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans hw
  have h1 := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * w)
  have h2 := norm_sub_le (1 : ℂ) ((t : ℂ) * w)
  rw [norm_one] at h1 h2
  rw [segNormSq, Complex.normSq_eq_norm_sq]
  exact ⟨by linarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : 1 / 2 ≤ ‖(1 : ℂ) - (t : ℂ) * w‖) 2],
    by linarith [pow_le_pow_left₀ (norm_nonneg ((1 : ℂ) - (t : ℂ) * w)) (by linarith : ‖(1 : ℂ) - (t : ℂ) * w‖ ≤ 3 / 2) 2]⟩

/-- The normalized corrected Taylor remainder is quadratically small on the half-unit disk. -/
theorem norm_unit_taylor_remainder_le (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
  let F (t : ℝ) := segNormSq w t ^ (k / 2) - 1 + k * t * w.re
  let D (t : ℝ) := k * ((segNormSq w t ^ (k / 2 - 1) - 1) * (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt F (D t) (Icc 0 1) t := fun t ht => by
    have hq : 0 < segNormSq w t := lt_of_lt_of_le (by norm_num) (segNormSq_bounds w hw ht).1
    have hsq : HasDerivAt (segNormSq w) (2 * t * ‖w‖ ^ 2 - 2 * w.re) t := by
      rw [show segNormSq w = fun s => 1 - 2 * s * w.re + s ^ 2 * ‖w‖ ^ 2 from funext (segNormSq_eq w)]
      convert (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul (2 * w.re))).add
        (((hasDerivAt_id t).pow 2).const_mul (‖w‖ ^ 2))) using 1 <;> [ext s; skip] <;> simp <;> ring
    have hrp := ((Real.hasDerivAt_rpow_const (x := segNormSq w t) (p := k / 2) (Or.inl hq.ne')).comp t hsq).sub_const 1
    have hlin : HasDerivAt (fun s : ℝ => k * s * w.re) (k * w.re) t := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (hasDerivAt_id t).const_mul (k * w.re)
    exact (hrp.add hlin |>.congr_deriv (by dsimp [D]; ring)).hasDerivWithinAt
  let p := k / 2 - 1
  have hp : p < 0 := by dsimp [p]; linarith
  let L := (-p) * (1 / 4 : ℝ) ^ (p - 1)
  have hL_nn : 0 ≤ L := mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
  have hlip : LipschitzOnWith L.toNNReal (fun x : ℝ => x ^ p) (Icc (1 / 4) (9 / 4)) :=
    (convex_Icc (1 / 4 : ℝ) (9 / 4)).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (lt_of_lt_of_le (by norm_num) hx.1).ne')).differentiableAt)
      fun x hx => by
        have hxp : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
        apply NNReal.coe_le_coe.mp
        rw [coe_nnnorm, Real.coe_toNNReal _ hL_nn, Real.deriv_rpow_const, Real.norm_eq_abs,
          abs_mul, abs_of_neg hp, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 (by linarith)) (by linarith)
  have hbd : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖D t‖ ≤ (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have hpd : |segNormSq w t ^ p - 1| ≤ L * |segNormSq w t - 1| := by
      have h := hlip.norm_sub_le (segNormSq_bounds w hw ht') (by norm_num : (1 : ℝ) ∈ Icc (1 / 4) (9 / 4))
      simpa [Real.coe_toNNReal _ hL_nn, Real.norm_eq_abs] using h
    have hRe := Complex.abs_re_le_norm w
    have hss : ‖w‖ ^ 2 ≤ 1 / 2 * ‖w‖ := by nlinarith [norm_nonneg w]
    have hts : t * ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) ht'.2
    have htw : |t * w.re| ≤ ‖w‖ := by
      rw [abs_mul, abs_of_nonneg ht'.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) ht'.2).trans hRe
    have hsqd : |segNormSq w t - 1| ≤ 5 / 2 * ‖w‖ := by
      rw [segNormSq_eq, show 1 - 2 * t * w.re + t ^ 2 * ‖w‖ ^ 2 - 1 = -(2 * (t * w.re)) + t ^ 2 * ‖w‖ ^ 2 by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg ‖w‖))]
      linarith [mul_le_of_le_one_left (sq_nonneg ‖w‖) (pow_le_one₀ ht'.1 ht'.2 (n := 2))]
    have hlin : |t * ‖w‖ ^ 2 - w.re| ≤ 3 / 2 * ‖w‖ :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg (mul_nonneg ht'.1 (sq_nonneg _))]; linarith)
    have hpd' : |segNormSq w t ^ p - 1| ≤ 5 / 2 * L * ‖w‖ := by nlinarith
    have hmain : |(segNormSq w t ^ p - 1) * (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2| ≤
        (15 / 4 * L + 1) * ‖w‖ ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (mul_nonneg ht'.1 (sq_nonneg _))]
      exact (add_le_add (mul_le_mul hpd' hlin (abs_nonneg _) (by positivity)) hts).trans_eq (by ring)
    rw [Real.norm_eq_abs]; dsimp [D]; rw [abs_mul, abs_of_pos hk]
    exact (mul_le_mul_of_nonneg_left hmain hk.le).trans_eq (by dsimp [L, p]; ring)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd 1 (right_mem_Icc.2 zero_le_one)
  have h0 : F 0 = 0 := by simp [F, segNormSq]
  have h1 : F 1 = ‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re := by
    simp only [F, segNormSq, Complex.ofReal_one, one_mul, mul_one, Complex.normSq_eq_norm_sq,
      ← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _)]
    rw [show ((2 : ℕ) : ℝ) * (k / 2) = k by push_cast; ring]
  simpa [h0, h1, Real.norm_eq_abs] using hmean

/-- The corrected Taylor kernel is absolutely integrable in the convergence window of
`DOZZ.planar_taylor_integral`. -/
theorem integrable_planarTaylorRemainder (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    ∀ z : ℂ, Integrable (DOZZ.planarTaylorRemainder k β z) volume := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [show DOZZ.planarTaylorRemainder k β 0 = fun _ => 0 from funext fun u => by simp [DOZZ.planarTaylorRemainder]]
    exact integrable_zero ℂ ℝ volume
  have hmeas : Measurable (DOZZ.planarTaylorRemainder k β z) := by
    change Measurable fun u : ℂ =>
      (‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re) / ‖u‖ ^ β
    fun_prop
  let R := 2 * ‖z‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hk2 : k < 2 := lt_trans hβ hβ₂
  rw [← integrableOn_univ, ← Set.union_compl_self (ball (0 : ℂ) R), integrableOn_union]
  refine ⟨?_, ?_⟩
  · -- Local ball `‖u‖ < 2 ‖z‖`
    have hi0 := ((integrableOn_norm_rpow_ball_iff (-β) R hR).2 (by linarith)).const_mul ((3 * ‖z‖) ^ k)
    have hi1 := (integrableOn_norm_rpow_ball_iff (k - β) R hR).2 (by linarith)
    have hi2 := ((integrableOn_norm_rpow_ball_iff (k - 1 - β) R hR).2 (by linarith)).const_mul (k * ‖z‖)
    refine ((hi0.add hi1).add hi2).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with u hu
    rw [Real.norm_eq_abs]
    have hball : ‖u‖ < 2 * ‖z‖ := by simpa [R, Metric.mem_ball, dist_zero_right] using hu
    rcases eq_or_ne u 0 with rfl | hu0
    · simp [DOZZ.planarTaylorRemainder, Real.zero_rpow hk.ne',
        Real.zero_rpow (lt_trans hk hβ).ne',
        Real.zero_rpow (neg_ne_zero.2 (lt_trans hk hβ).ne'),
        Real.zero_rpow (by linarith : k - β ≠ 0), Real.zero_rpow (by linarith : k - 1 - β ≠ 0)]
    have hr : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos hr β
    have hshift : ‖u - z‖ ^ k ≤ (3 * ‖z‖) ^ k :=
      Real.rpow_le_rpow (norm_nonneg _) ((norm_sub_le u z).trans (by linarith)) hk.le
    let w := z / u
    have hlin : |(z / u + star z / star u).re| ≤ 2 * (‖z‖ / ‖u‖) := by
      rw [show star z / star u = star w by simp [w]]
      exact (Complex.abs_re_le_norm (w + star w)).trans
        ((norm_add_le w (star w)).trans_eq (by simp [w, two_mul]))
    have hcnt : |(k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re| ≤ k * ‖z‖ * ‖u‖ ^ (k - 1) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k / 2) * ‖u‖ ^ k)]
      refine (mul_le_mul_of_nonneg_left hlin (by positivity)).trans_eq ?_
      rw [Real.rpow_sub hr k 1, Real.rpow_one]; field_simp [hr.ne']
    have hnum : |‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re| ≤
        (3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1) :=
      (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (by rwa [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) k)])
          (le_of_eq (abs_of_nonneg (Real.rpow_nonneg hr.le k))))) hcnt)
    change |(_) / ‖u‖ ^ β| ≤ _
    rw [abs_div, abs_of_pos hden]
    refine (div_le_div_of_nonneg_right hnum hden.le).trans_eq ?_
    dsimp only [Pi.add_apply]
    calc ((3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1)) / ‖u‖ ^ β
      _ = (3 * ‖z‖) ^ k * (‖u‖ ^ β)⁻¹ + ‖u‖ ^ k / ‖u‖ ^ β + k * ‖z‖ * (‖u‖ ^ (k - 1) / ‖u‖ ^ β) := by ring
      _ = (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) + ‖u‖ ^ (k - β) + k * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
          rw [← Real.rpow_neg hr.le, ← Real.rpow_sub hr k β, ← Real.rpow_sub hr (k - 1) β]
  · -- Tail `2 ‖z‖ ≤ ‖u‖`
    let C := k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
    have hC0 : 0 ≤ C := mul_nonneg hk.le (add_nonneg zero_le_one
      (mul_nonneg (by norm_num) (mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _))))
    refine (((integrableOn_norm_rpow_ball_compl_iff (k - 2 - β) R hR).2 (by linarith)).const_mul
      (C * ‖z‖ ^ 2)).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with u hu
    have hlarge : 2 * ‖z‖ ≤ ‖u‖ := not_lt.1 fun h => hu (by simpa [R, Metric.mem_ball, dist_zero_right] using h)
    have hr : 0 < ‖u‖ := lt_of_lt_of_le hR hlarge
    have hu0 : u ≠ 0 := norm_pos_iff.1 hr
    let w := z / u
    have hw : ‖w‖ ≤ 1 / 2 := by dsimp [w]; rw [norm_div, div_le_iff₀ hr]; linarith
    have hfac : ‖u - z‖ ^ k = ‖u‖ ^ k * ‖(1 : ℂ) - w‖ ^ k := by
      rw [show u - z = u * (1 - w) by dsimp [w]; field_simp [hu0], norm_mul,
        Real.mul_rpow hr.le (norm_nonneg _)]
    have hre : (z / u + star z / star u).re = 2 * w.re := by
      rw [show star z / star u = star w by simp [w]]; simp [Complex.add_re]; ring
    rw [Real.norm_eq_abs]
    change |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re) / ‖u‖ ^ β| ≤ _
    rw [show ‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re =
        ‖u‖ ^ k * (‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re) by rw [hfac, hre]; ring,
      abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr.le k), abs_of_pos (Real.rpow_pos_of_pos hr β)]
    refine (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (norm_unit_taylor_remainder_le k hk hk2 w hw) (Real.rpow_nonneg hr.le k))
      (Real.rpow_nonneg hr.le β)).trans_eq ?_
    dsimp only [w]; rw [norm_div, div_pow]
    calc ‖u‖ ^ k * (C * (‖z‖ ^ 2 / ‖u‖ ^ 2)) / ‖u‖ ^ β
      _ = C * ‖z‖ ^ 2 * ((‖u‖ ^ k / ‖u‖ ^ (2 : ℝ)) / ‖u‖ ^ β) := by rw [Real.rpow_two]; ring
      _ = C * ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by rw [← Real.rpow_sub hr k 2, ← Real.rpow_sub hr]

end DOZZ.Proofs
