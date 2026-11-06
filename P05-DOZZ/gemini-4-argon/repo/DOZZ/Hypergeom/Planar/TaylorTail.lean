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

open Set
open Metric
open MeasureTheory

namespace DOZZ.Proofs


private def segmentNormSq (u z : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (u - (t : ℂ) * z)



private noncomputable def segmentRpow (k : ℝ) (u z : ℂ) (t : ℝ) : ℝ :=
  segmentNormSq u z t ^ (k / 2)



private noncomputable def unitTaylorPath (k : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  segmentRpow k 1 w t - 1 + k * t * w.re



/-- The normalized corrected Taylor remainder is quadratically small on the half-unit disk. -/
theorem norm_unit_taylor_remainder_le k (hk : 0 < k) (hk₂ : k < 2)
    (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
  have unitSegment_normSq_bounds {t} (ht : t ∈ Icc (0 : ℝ) 1) : 1 / 4 ≤ segmentNormSq 1 w t ∧ segmentNormSq 1 w t ≤ 9 / 4 := by
    have hv : ‖(t : ℂ) * w‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans hw
    have hlow : 1 / 2 ≤ ‖(1 : ℂ) - (t : ℂ) * w‖ := by
      have h := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * w)
      rw [norm_one] at h
      exact (show 1 / 2 ≤ 1 - ‖(t : ℂ) * w‖ by linarith only [hv]).trans h
    have hupp : ‖(1 : ℂ) - (t : ℂ) * w‖ ≤ 3 / 2 := by
      have h := norm_sub_le (1 : ℂ) ((t : ℂ) * w)
      rw [norm_one] at h
      linarith only [h, hv]
    rw [(show segmentNormSq 1 w t = ‖(1 : ℂ) - (t : ℂ) * w‖ ^ 2 by dsimp [segmentNormSq]; rw [Complex.normSq_eq_norm_sq])]
    exact ⟨by linarith only [(pow_le_pow_left₀ (by norm_num) hlow 2)], by linarith only [(pow_le_pow_left₀ (norm_nonneg _) hupp 2)]⟩
  have segmentNormSq_formula u z t : segmentNormSq u z t = ‖u‖ ^ 2 - 2 * t * (z * star u).re + t ^ 2 * ‖z‖ ^ 2 := by
    dsimp [segmentNormSq]
    rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    simp only [starRingEnd_apply, (show star ((t : ℂ) * z) = (t : ℂ) * star z by simp)]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring_nf
  have unitTaylorPath_deriv_bound {t} (ht : t ∈ Icc (0 : ℝ) 1) : ‖k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) * (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)‖ ≤ (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
    have rpow_lipschitz_on {p} (hp : p < 0) : LipschitzOnWith ((-p * (1/4 : ℝ) ^ (p - 1)).toNNReal) (fun x => x ^ p) (Icc (1/4 : ℝ) (9/4)) := by
      apply (convex_Icc (1/4 : ℝ) (9/4)).lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        exact (Real.hasDerivAt_rpow_const
          (Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)))).differentiableAt
      · intro x hx
        apply NNReal.coe_le_coe.mp
        rw [coe_nnnorm, Real.coe_toNNReal _ (mul_nonneg (le_of_lt (neg_pos.mpr hp)) (Real.rpow_nonneg (by norm_num) _))]
        change ‖deriv (fun y : ℝ => y ^ p) x‖ ≤ _
        rw [Real.deriv_rpow_const, Real.norm_eq_abs, abs_mul, abs_of_neg hp,
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le (by norm_num) hx.1)) _)]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 (by linarith only [hp])) (by linarith only [hp])
    let p := k / 2 - 1
    let L := (-p) * (1 / 4 : ℝ) ^ (p - 1)
    have hp : p < 0 := by dsimp [p]; linarith only [hk₂]
    have hLpos : 0 ≤ (-p) * (1 / 4 : ℝ) ^ (p - 1) := mul_nonneg (by linarith only [hp]) (Real.rpow_nonneg (by norm_num) _)
    have hpowdiff : |segmentNormSq 1 w t ^ p - 1| ≤ L * |segmentNormSq 1 w t - 1| := by
      have h := (rpow_lipschitz_on hp).norm_sub_le (unitSegment_normSq_bounds ht) (show (1 : ℝ) ∈ Icc (1 / 4 : ℝ) (9 / 4) by norm_num)
      rw [Real.coe_toNNReal _ hLpos] at h
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
      rw [Real.one_rpow] at h
      change |segmentNormSq 1 w t ^ p - 1| ≤ L * |segmentNormSq 1 w t - 1| at h
      exact h
    have ht₀ := ht.1
    have ht₁ := ht.2
    have hRe := Complex.abs_re_le_norm w
    have hss : ‖w‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖w‖ := by
      linarith only [mul_le_mul_of_nonneg_left hw (norm_nonneg w)]
    have hts := mul_le_of_le_one_left (sq_nonneg ‖w‖) ht₁
    have htw : |t * w.re| ≤ ‖w‖ := by
      calc
        |t * w.re| = t * |w.re| := by rw [abs_mul, abs_of_nonneg ht₀]
        _ ≤ |w.re| := mul_le_of_le_one_left (abs_nonneg _) ht₁
        _ ≤ ‖w‖ := hRe
    have hqdiff : |segmentNormSq 1 w t - 1| ≤ (5 / 2 : ℝ) * ‖w‖ := by
      have hqformula : segmentNormSq 1 w t - 1 =
          -(2 * (t * w.re)) + t ^ 2 * ‖w‖ ^ 2 := by
        rw [segmentNormSq_formula]
        simp
        ring
      rw [hqformula]
      calc
        |-(2 * (t * w.re)) + t ^ 2 * ‖w‖ ^ 2| ≤
            |-(2 * (t * w.re))| + |t ^ 2 * ‖w‖ ^ 2| := abs_add_le _ _
        _ = 2 * |t * w.re| + t ^ 2 * ‖w‖ ^ 2 := by
          rw [abs_neg, abs_mul, abs_of_pos (by norm_num),
            abs_of_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg ‖w‖))]
        _ ≤ 2 * ‖w‖ + (1 / 2 : ℝ) * ‖w‖ := by
          linarith only [htw, hss, mul_le_of_le_one_left (sq_nonneg ‖w‖) (pow_le_one₀ ht₀ ht₁ : t ^ 2 ≤ 1)]
        _ = (5 / 2 : ℝ) * ‖w‖ := by ring
    have hlin : |t * ‖w‖ ^ 2 - w.re| ≤ (3 / 2 : ℝ) * ‖w‖ := by
      calc
        |t * ‖w‖ ^ 2 - w.re| ≤ |t * ‖w‖ ^ 2| + |w.re| := abs_sub _ _
        _ = t * ‖w‖ ^ 2 + |w.re| := by rw [abs_of_nonneg (mul_nonneg ht₀ (sq_nonneg _))]
        _ ≤ (1 / 2 : ℝ) * ‖w‖ + ‖w‖ := by linarith only [hts, hRe, hss]
        _ = (3 / 2 : ℝ) * ‖w‖ := by ring
    have hpowdiff' : |segmentNormSq 1 w t ^ p - 1| ≤ (5 / 2 : ℝ) * L * ‖w‖ := by
      calc
        _ ≤ L * |segmentNormSq 1 w t - 1| := hpowdiff
        _ ≤ L * ((5 / 2 : ℝ) * ‖w‖) := mul_le_mul_of_nonneg_left hqdiff (by dsimp [L]; exact mul_nonneg (by linarith only [hp]) (Real.rpow_nonneg (by norm_num) _))
        _ = _ := by ring
    have hmain : |(segmentNormSq 1 w t ^ p - 1) *
        (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2| ≤
          ((15 / 4 : ℝ) * L + 1) * ‖w‖ ^ 2 := by
      calc
        _ ≤ |segmentNormSq 1 w t ^ p - 1| *
            |t * ‖w‖ ^ 2 - w.re| + |t * ‖w‖ ^ 2| := by
              calc
                _ ≤ |(segmentNormSq 1 w t ^ p - 1) * (t * ‖w‖ ^ 2 - w.re)| +
                    |t * ‖w‖ ^ 2| := abs_add_le _ _
                _ = _ := by rw [abs_mul]
        _ = |segmentNormSq 1 w t ^ p - 1| *
            |t * ‖w‖ ^ 2 - w.re| + |t * ‖w‖ ^ 2| := by rw [abs_mul]
        _ ≤ ((5 / 2 : ℝ) * L * ‖w‖) * ((3 / 2 : ℝ) * ‖w‖) + ‖w‖ ^ 2 := by
              apply add_le_add
              · exact mul_le_mul hpowdiff' hlin (abs_nonneg _) (by positivity)
              · exact (by rw [abs_of_nonneg (mul_nonneg ht₀ (sq_nonneg _))]; exact hts)
        _ = _ := by ring
    rw [Real.norm_eq_abs]
    have hk_nonneg := le_of_lt hk
    calc
      _ = k * |(segmentNormSq 1 w t ^ p - 1) *
          (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2| := by rw [abs_mul, abs_of_nonneg hk_nonneg]
      _ ≤ k * (((15 / 4 : ℝ) * L + 1) * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left hmain hk_nonneg
      _ = _ := by dsimp [L, p]; ring_nf
  have unitTaylorPath_hasDerivAt t (ht : t ∈ Icc (0 : ℝ) 1) (hw : ‖w‖ ≤ 1 / 2) : HasDerivAt (unitTaylorPath k w) (k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) * (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)) t := by
    have segmentRpow_hasDerivAt u z t (hq : 0 < segmentNormSq u z t) : HasDerivAt (segmentRpow k u z) (k * segmentNormSq u z t ^ (k / 2 - 1) * (t * ‖z‖ ^ 2 - (z * star u).re)) t := by
      have segmentNormSq_hasDerivAt : HasDerivAt (segmentNormSq u z) (2 * t * ‖z‖ ^ 2 - 2 * (z * star u).re) t := by
        change HasDerivAt (fun s : ℝ => segmentNormSq u z s) _ _
        rw [(show (fun s => segmentNormSq u z s) = fun s => ‖u‖ ^ 2 - 2 * s * (z * star u).re + s ^ 2 * ‖z‖ ^ 2 by funext s; exact segmentNormSq_formula u z s)]
        convert (((hasDerivAt_const t (‖u‖ ^ 2)).sub
          ((hasDerivAt_id t).const_mul (2 * (z * star u).re))).add
          (((hasDerivAt_id t).pow 2).const_mul (‖z‖ ^ 2))) using 1
        · ext s
          simp
          ring_nf
        · simp
          ring_nf
      unfold segmentRpow
      change HasDerivAt ((fun x : ℝ => x ^ (k / 2)) ∘ segmentNormSq u z) _ _
      convert ((Real.hasDerivAt_rpow_const (x := segmentNormSq u z t) (p := k / 2) (Or.inl hq.ne')).comp t (segmentNormSq_hasDerivAt)) using 1
      all_goals ring_nf
    have hlinear : HasDerivAt (fun s => k * s * w.re) (k * w.re) t := by
      convert (hasDerivAt_id t).const_mul (k * w.re) using 1
      · ext s
        simp
        ring
      · ring
    unfold unitTaylorPath
    convert (((segmentRpow_hasDerivAt 1 w t (lt_of_lt_of_le (by norm_num) (unitSegment_normSq_bounds ht).1)).sub_const 1).add hlinear) using 1
    · simp [star_one]
      ring_nf
  let D : ℝ → ℝ := fun t =>
    k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) *
      (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' (by intro t ht; exact (unitTaylorPath_hasDerivAt t ht hw).hasDerivWithinAt) (by intro t ht; simpa [D] using (unitTaylorPath_deriv_bound (Ico_subset_Icc_self ht)))
    (1 : ℝ) (right_mem_Icc.2 (by norm_num : (0 : ℝ) ≤ 1))
  have hone : unitTaylorPath k w 1 = ‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re := by
    simp [unitTaylorPath, segmentRpow, segmentNormSq, Complex.normSq_eq_norm_sq]
    calc
      (‖(1 : ℂ) - w‖ ^ 2) ^ (k / 2) =
          (‖(1 : ℂ) - w‖ ^ ((2 : ℕ) : ℝ)) ^ (k / 2) := by rw [← (Real.rpow_natCast _ 2)]
      _ = ‖(1 : ℂ) - w‖ ^ ((2 : ℝ) * (k / 2)) :=
        (Real.rpow_mul (norm_nonneg _) 2 (k / 2)).symm
      _ = _ := by congr 1; ring_nf
  simpa [(show unitTaylorPath k w 0 = 0 by simp [unitTaylorPath, segmentRpow, segmentNormSq]), hone, Real.norm_eq_abs] using hmean




private theorem measurable_nonneg_rpow {f : ℂ → ℝ} (hf : Measurable f)
    (hfn : ∀ u, 0 ≤ f u) (p : ℝ) : Measurable (fun u => f u ^ p) := by
  have hrepr : (fun u => f u ^ p) =
      fun u => if f u = 0 then 0 ^ p else Real.exp (p * Real.log (f u)) := by
    funext u
    by_cases hu : f u = 0
    · simp [hu]
    · rw [ite_eq_right hu,
        Real.rpow_def_of_pos (lt_of_le_of_ne (hfn u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℝ)) hf
  · exact measurable_const
  · fun_prop

private theorem measurable_complex_norm_rpow (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) :=
  measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg u) p






/-- The corrected Taylor kernel is absolutely integrable in the convergence window of
`DOZZ.planar_taylor_integral`. -/
theorem integrable_planarTaylorRemainder k β
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    ∀ z : ℂ, Integrable (DOZZ.planarTaylorRemainder k β z) volume := by
  have measurable_planarTaylorRemainder (z : ℂ) : Measurable (DOZZ.planarTaylorRemainder k β z) := by
    change Measurable (fun u : ℂ =>
      (‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
        (z / u + star z / star u).re) / ‖u‖ ^ β)
    apply Measurable.div
    · have hshift : Measurable (fun u : ℂ => ‖u - z‖ ^ k) :=
        measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg (u - z)) k
      exact (hshift.sub (measurable_complex_norm_rpow k)).add
        ((measurable_const.mul (measurable_complex_norm_rpow k)).mul (by fun_prop))
    · exact measurable_complex_norm_rpow β
  have integrableOn_planarTaylorRemainder_ball z (hz : z ≠ 0) : IntegrableOn (DOZZ.planarTaylorRemainder k β z) (ball (0 : ℂ) (2 * ‖z‖)) volume := by
    have abs_planarTaylorRemainder_local_le u (hball : ‖u‖ < 2 * ‖z‖) : |DOZZ.planarTaylorRemainder k β z u| ≤ (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) + ‖u‖ ^ (k - β) + k * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
      have abs_planarTaylorNumerator_local_le (hu : u ≠ 0) (hball : ‖u‖ < 2 * ‖z‖) : |‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re| ≤ (3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1) := by
        have hr := norm_pos_iff.mpr hu
        have hshift : ‖u - z‖ ^ k ≤ (3 * ‖z‖) ^ k := by
          have hnorm : ‖u - z‖ ≤ 3 * ‖z‖ := by
            calc
              ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le _ _
              _ ≤ 3 * ‖z‖ := by linarith only [hball]
          exact Real.rpow_le_rpow (norm_nonneg _) hnorm (le_of_lt hk)
        let w := z / u
        have hlin : |(z / u + star z / star u).re| ≤ 2 * (‖z‖ / ‖u‖) := by
          rw [(show star z / star u = star w by dsimp [w]; simp)]
          calc
            |(w + star w).re| ≤ ‖w + star w‖ := Complex.abs_re_le_norm _
            _ ≤ ‖w‖ + ‖star w‖ := norm_add_le _ _
            _ = 2 * ‖w‖ := by simp [two_mul]
            _ = 2 * (‖z‖ / ‖u‖) := by rw [norm_div]
        have hcounter : |(k / 2) * ‖u‖ ^ k *
            (z / u + star z / star u).re| ≤ k * ‖z‖ * ‖u‖ ^ (k - 1) := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k / 2) * ‖u‖ ^ k)]
          calc
            (k / 2) * ‖u‖ ^ k * |(z / u + star z / star u).re|
                ≤ (k / 2) * ‖u‖ ^ k * (2 * (‖z‖ / ‖u‖)) := by
                    exact mul_le_mul_of_nonneg_left hlin (by positivity)
            _ = k * (‖u‖ ^ k * (‖z‖ / ‖u‖)) := by ring
            _ = k * ‖z‖ * ‖u‖ ^ (k - 1) := by rw [(show ‖u‖ ^ k * (‖z‖ / ‖u‖) = ‖z‖ * ‖u‖ ^ (k - 1) by rw [(show ‖u‖ ^ (k - 1) = ‖u‖ ^ k / ‖u‖ by simpa using (Real.rpow_sub hr k 1))]; field_simp [hr.ne'])]; ring
        calc
          _ ≤ |‖u - z‖ ^ k - ‖u‖ ^ k| +
              |(k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re| := abs_add_le _ _
          _ ≤ |‖u - z‖ ^ k| + |‖u‖ ^ k| +
              k * ‖z‖ * ‖u‖ ^ (k - 1) := by
                exact add_le_add (abs_sub _ _) hcounter
          _ ≤ (3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1) := by
                exact add_le_add (add_le_add (by rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) k)]; exact hshift) (le_of_eq (abs_of_nonneg (Real.rpow_nonneg hr.le k)))) le_rfl
      by_cases hu : u = 0
      · subst u
        simp [DOZZ.planarTaylorRemainder, Real.zero_rpow, ne_of_gt hk,
          ne_of_gt (lt_trans hk hβ), ne_of_lt (by linarith only [hβ] : k - β < 0),
          ne_of_lt (by linarith only [hβ] : k - 1 - β < 0)]
      · have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
        have hden := Real.rpow_pos_of_pos hr β
        have hpow₀ : ‖u‖ ^ (-β) = 1 / ‖u‖ ^ β := by
          calc
            ‖u‖ ^ (-β) = ‖u‖ ^ (0 - β) := by congr 1; ring
            _ = ‖u‖ ^ (0 : ℝ) / ‖u‖ ^ β := Real.rpow_sub hr 0 β
            _ = 1 / ‖u‖ ^ β := by rw [Real.rpow_zero]
        change |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
          (z / u + star z / star u).re) / ‖u‖ ^ β| ≤ _
        rw [abs_div, abs_of_pos hden]
        calc
          _ ≤ ((3 * ‖z‖) ^ k + ‖u‖ ^ k +
              k * ‖z‖ * ‖u‖ ^ (k - 1)) / ‖u‖ ^ β :=
                div_le_div_of_nonneg_right (abs_planarTaylorNumerator_local_le hu hball) hden.le
          _ = (3 * ‖z‖) ^ k * (1 / ‖u‖ ^ β) +
              ‖u‖ ^ k / ‖u‖ ^ β +
              k * ‖z‖ * (‖u‖ ^ (k - 1) / ‖u‖ ^ β) := by ring
          _ = (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) +
              ‖u‖ ^ (k - β) + k * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
                rw [← hpow₀, ((Real.rpow_sub hr k β).symm), ((Real.rpow_sub hr (k - 1) β).symm)]
    let R := 2 * ‖z‖
    let A := (3 * ‖z‖) ^ k
    let p₀ := -β
    let p₁ := k - β
    let p₂ := k - 1 - β
    have hR : 0 < R := by dsimp [R]; positivity
    change Integrable (DOZZ.planarTaylorRemainder k β z)
      (volume.restrict (ball 0 R))
    apply (((((integrableOn_norm_rpow_ball_iff p₀ R hR).2 (by dsimp [p₀]; linarith only [hβ₂])).const_mul A).add ((integrableOn_norm_rpow_ball_iff p₁ R hR).2 (by dsimp [p₁]; linarith only [hβ₂, hk]))).add (((integrableOn_norm_rpow_ball_iff p₂ R hR).2 (by dsimp [p₂]; linarith only [hβlin])).const_mul (k * ‖z‖))).mono' (measurable_planarTaylorRemainder z).aestronglyMeasurable
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with u hu
    rw [Real.norm_eq_abs]
    change |DOZZ.planarTaylorRemainder k β z u| ≤
      A * ‖u‖ ^ p₀ + ‖u‖ ^ p₁ + (k * ‖z‖) * ‖u‖ ^ p₂
    simpa [A, p₀, p₁, p₂, mul_assoc, mul_left_comm, mul_comm] using (abs_planarTaylorRemainder_local_le u (by dsimp [R] at hu; simpa [Metric.mem_ball, dist_zero_right] using hu))
  have integrableOn_planarTaylorRemainder_tail z (hz : z ≠ 0) : IntegrableOn (DOZZ.planarTaylorRemainder k β z) (ball (0 : ℂ) (2 * ‖z‖))ᶜ volume := by
    have abs_planarTaylorRemainder_le (hk₂ : k < 2) z u (hu : u ≠ 0) (hlarge : 2 * ‖z‖ ≤ ‖u‖) : |DOZZ.planarTaylorRemainder k β z u| ≤ (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by
      have rpow_tail_normalize (r : ℝ) (s : ℝ) (k : ℝ) (β : ℝ) (hr : 0 < r) : r ^ k * (s / r) ^ 2 / r ^ β = s ^ 2 * r ^ (k - 2 - β) := by
        calc
          _ = r ^ k * (s ^ 2 / r ^ 2) / r ^ β := by rw [div_pow]
          _ = s ^ 2 * ((r ^ k / r ^ 2) / r ^ β) := by ring
          _ = _ := by rw [(show r ^ k / r ^ 2 = r ^ (k - 2) by simpa using (Real.rpow_sub hr k (2 : ℝ)).symm), ((Real.rpow_sub hr (k - 2) β).symm)]
      have abs_planarTaylorNumerator_le : |‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re| ≤ (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖u‖ ^ k * ‖z / u‖ ^ 2 := by
        let w := z / u
        have hlinear : (z / u + star z / star u).re = 2 * w.re := by
          rw [(show star z / star u = star w by dsimp [w]; simp)]
          simp [Complex.add_re]
          change (z / u).re + (z / u).re = 2 * (z / u).re
          ring
        rw [(show ‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re = ‖u‖ ^ k * (‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re) by rw [(show ‖u - z‖ ^ k = ‖u‖ ^ k * ‖(1 : ℂ) - w‖ ^ k by rw [(show u - z = u * ((1 : ℂ) - w) by dsimp [w]; field_simp [hu]), norm_mul, Real.mul_rpow (norm_nonneg u) (norm_nonneg (1 - w))]), hlinear]; ring)]
        have hnorm := Real.rpow_nonneg (norm_nonneg u) k
        calc
          _ = ‖u‖ ^ k * |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re| := by
            rw [abs_mul, abs_of_nonneg hnorm]
          _ ≤ ‖u‖ ^ k * ((k * (1 + (15 / 4) *
                ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (norm_unit_taylor_remainder_le k hk hk₂ w (by dsimp [w]; rw [norm_div]; apply (div_le_iff₀ (norm_pos_iff.mpr hu)).2; linarith only [hlarge])) hnorm
          _ = _ := by dsimp [w]; ring
      have hr := norm_pos_iff.mpr hu
      change |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
          (z / u + star z / star u).re) / ‖u‖ ^ β| ≤ _
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hr β)]
      calc
        _ ≤ (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
            ‖u‖ ^ k * ‖z / u‖ ^ 2 / ‖u‖ ^ β := by simpa using (div_le_div_of_nonneg_right (abs_planarTaylorNumerator_le) (Real.rpow_nonneg hr.le β))
        _ = (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
            ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by
          rw [norm_div]
          calc
            _ = (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
                (‖u‖ ^ k * (‖z‖ / ‖u‖) ^ 2 / ‖u‖ ^ β) := by ring
            _ = _ := by rw [(rpow_tail_normalize ‖u‖ ‖z‖ k β hr)]; ring
    let p := k - 2 - β
    let C := k * (1 + (15 / 4) *
      ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
    let B := C * ‖z‖ ^ 2
    have hr : 0 < 2 * ‖z‖ := by positivity
    change Integrable (DOZZ.planarTaylorRemainder k β z)
        (volume.restrict (ball (0 : ℂ) (2 * ‖z‖))ᶜ)
    apply (((integrableOn_norm_rpow_ball_compl_iff p (2 * ‖z‖) hr).2 (by dsimp [p]; linarith only [hβ])).const_mul B).mono' (measurable_planarTaylorRemainder z).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.compl)] with u hu
    have hlarge : 2 * ‖z‖ ≤ ‖u‖ := by
      by_contra h
      have := lt_of_not_ge h
      exact hu (by simpa [Metric.mem_ball, dist_zero_right] using this)
    rw [Real.norm_eq_abs]
    change |DOZZ.planarTaylorRemainder k β z u| ≤ B * ‖u‖ ^ p
    calc
      _ ≤ C * ‖z‖ ^ 2 * ‖u‖ ^ p := by simpa [C, p] using (abs_planarTaylorRemainder_le (lt_trans hβ hβ₂) z u (by intro hu0; subst u; linarith only [(by simpa using hlarge), hr]) hlarge)
      _ = B * ‖u‖ ^ p := by dsimp [B]
  intro z
  by_cases hz : z = 0
  · subst z
    rw [(show DOZZ.planarTaylorRemainder k β 0 = fun _ : ℂ => (0 : ℝ) by funext u; simp [DOZZ.planarTaylorRemainder])]
    exact integrable_zero ℂ ℝ volume
  · have hball := integrableOn_planarTaylorRemainder_ball z hz
    rw [← integrableOn_univ, ← Set.union_compl_self (ball (0 : ℂ) (2 * ‖z‖)),
      integrableOn_union]
    exact ⟨hball, (integrableOn_planarTaylorRemainder_tail z hz)⟩

end DOZZ.Proofs
