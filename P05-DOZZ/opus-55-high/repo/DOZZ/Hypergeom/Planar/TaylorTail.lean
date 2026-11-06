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

private theorem rpow_lipschitz_on {p : ℝ} (hp : p < 0) :
    LipschitzOnWith ((-p * (1/4 : ℝ) ^ (p - 1)).toNNReal)
      (fun x : ℝ => x ^ p) (Icc (1/4 : ℝ) (9/4)) := by
  apply (convex_Icc (1/4) (9/4)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)))).differentiableAt
  · intro x hx
    have hxpos : 0 < x := by grind
    have hpow : x ^ (p - 1) ≤ (1/4 : ℝ) ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 (by linarith)
    have hB : 0 ≤ (-p) * (1/4 : ℝ) ^ (p - 1) :=
      by bound
    apply NNReal.coe_le_coe.mp
    change ‖deriv (fun y : ℝ => y ^ p) x‖ ≤ _
    rw [Real.deriv_rpow_const, Real.norm_eq_abs, abs_mul, abs_of_neg hp,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt hxpos) _)]
    simp_all

private def segmentNormSq (u z : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (u - (t : ℂ) * z)
section
variable (u z : ℂ) (t : ℝ)

private theorem segmentNormSq_formula :
    segmentNormSq u z t = ‖u‖ ^ 2 - 2 * t * (z * star u).re + t ^ 2 * ‖z‖ ^ 2 := by
  dsimp [segmentNormSq]
  rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hstar : star (t * z) = t * star z := by simp
  simp only [starRingEnd_apply, hstar]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring_nf

private theorem segmentNormSq_hasDerivAt :
    HasDerivAt (segmentNormSq u z) (2 * t * ‖z‖ ^ 2 - 2 * (z * star u).re) t := by
  have hformula : (fun s : ℝ => segmentNormSq u z s) =
      fun s => ‖u‖ ^ 2 - 2 * s * (z * star u).re + s ^ 2 * ‖z‖ ^ 2 := by
    funext s
    exact segmentNormSq_formula u z s
  change HasDerivAt (fun s : ℝ => segmentNormSq u z s) _ _
  rw [hformula]
  convert (((hasDerivAt_const t (‖u‖ ^ 2)).sub
    ((hasDerivAt_id t).const_mul (2 * (z * star u).re))).add
    (((hasDerivAt_id t).pow 2).const_mul (‖z‖ ^ 2))) using 1
  · ext s
    simp
    ring_nf
  grind

end

private noncomputable def segmentRpow (k : ℝ) (u z : ℂ) (t : ℝ) : ℝ :=
  segmentNormSq u z t ^ (k / 2)

private theorem segmentRpow_hasDerivAt (k : ℝ) (u z : ℂ) (t : ℝ)
    (hq : 0 < segmentNormSq u z t) :
    HasDerivAt (segmentRpow k u z)
      (k * segmentNormSq u z t ^ (k / 2 - 1) *
        (t * ‖z‖ ^ 2 - (z * star u).re)) t := by
  unfold segmentRpow
  change HasDerivAt ((fun x : ℝ => x ^ (k / 2)) ∘ segmentNormSq u z) _ _
  have hpow := (Real.hasDerivAt_rpow_const (x := segmentNormSq u z t)
    (p := k / 2) (Or.inl hq.ne')).comp t (segmentNormSq_hasDerivAt u z t)
  grind

private theorem unitSegment_normSq_bounds (w : ℂ) (hw : ‖w‖ ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 4 ≤ segmentNormSq 1 w t ∧ segmentNormSq 1 w t ≤ 9 / 4 := by
  have ht₁ := ht.2
  have hs := norm_nonneg w
  have hv : ‖t * w‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith
  have hlow : 1 / 2 ≤ ‖1 - t * w‖ := by
    have h := norm_sub_norm_le 1 (t * w)
    rw [norm_one] at h
    linarith
  have hupp : ‖1 - t * w‖ ≤ 3 / 2 := by
    have h := norm_sub_le 1 (t * w)
    rw [norm_one] at h
    linarith
  have hqnorm : segmentNormSq 1 w t = ‖1 - t * w‖ ^ 2 := by
    dsimp [segmentNormSq]
    rw [Complex.normSq_eq_norm_sq]
  rw [hqnorm]
  have hlo2 := pow_le_pow_left₀ (by norm_num) hlow 2
  have hup2 := pow_le_pow_left₀ (norm_nonneg _) hupp 2
  grind

private noncomputable def unitTaylorPath (k : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  segmentRpow k 1 w t - 1 + k * t * w.re
section
variable (k : ℝ)

private theorem unitTaylorPath_hasDerivAt (w : ℂ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hw : ‖w‖ ≤ 1 / 2) :
    HasDerivAt (unitTaylorPath k w)
      (k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) *
        (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)) t := by
  have hq : 0 < segmentNormSq 1 w t := lt_of_lt_of_le (by norm_num) (unitSegment_normSq_bounds w hw ht).1
  have hlinear : HasDerivAt (fun s => k * s * w.re) (k * w.re) t := by
    convert (hasDerivAt_id t).const_mul (k * w.re) using 1
    · grind
    · ring
  unfold unitTaylorPath
  convert (((segmentRpow_hasDerivAt k 1 w t hq).sub_const 1).add hlinear) using 1
  · simp [star_one]
    ring_nf
section
variable (hk : 0 < k) (hk₂ : k < 2) (w : ℂ) (hw : ‖w‖ ≤ 1 / 2)
include hk hk₂ hw

private theorem unitTaylorPath_deriv_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) *
      (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)‖ ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
  let p := k / 2 - 1
  let L := (-p) * (1 / 4) ^ (p - 1)
  have hp : p < 0 := by grind
  have hL : 0 ≤ L := by
    bound
  have hone : 1 ∈ Icc (1 / 4 : ℝ) (9 / 4) := by norm_num
  have hLpos : 0 ≤ (-p) * (1 / 4 : ℝ) ^ (p - 1) := by
    assumption
  have hpowdiff : |segmentNormSq 1 w t ^ p - 1| ≤ L * |segmentNormSq 1 w t - 1| := by
    have h := (rpow_lipschitz_on hp).norm_sub_le ((unitSegment_normSq_bounds w hw ht)) hone
    rw [Real.coe_toNNReal _ hLpos, Real.norm_eq_abs, Real.norm_eq_abs, Real.one_rpow] at h
    change |segmentNormSq 1 w t ^ p - 1| ≤ L * |segmentNormSq 1 w t - 1| at h
    exact h
  have ht₀ := ht.1
  have ht₁ := ht.2
  have hRe := Complex.abs_re_le_norm w
  have hss : ‖w‖ ^ 2 ≤ (1 / 2) * ‖w‖ := by
    linarith only [mul_le_mul_of_nonneg_left hw (norm_nonneg w)]
  have hts : t * ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    exact mul_le_of_le_one_left (sq_nonneg ‖w‖) ht₁
  have htSq : t ^ 2 ≤ 1 := pow_le_one₀ ht₀ ht₁
  have htw : |t * w.re| ≤ ‖w‖ := by
    calc
      |t * w.re| = t * |w.re| := by simp_all
      _ ≤ |w.re| := mul_le_of_le_one_left (abs_nonneg _) ht₁
      _ ≤ ‖w‖ := hRe
  have hqdiff : |segmentNormSq 1 w t - 1| ≤ (5 / 2) * ‖w‖ := by
    have hqformula : segmentNormSq 1 w t - 1 =
        -(2 * (t * w.re)) + t ^ 2 * ‖w‖ ^ 2 := by
      rw [segmentNormSq_formula]
      simp
      ring
    rw [hqformula]
    calc
      |-(2 * (t * w.re)) + t ^ 2 * ‖w‖ ^ 2| ≤
          |-(2 * (t * w.re))| + |t ^ 2 * ‖w‖ ^ 2| := abs_add_le ..
      _ = 2 * |t * w.re| + t ^ 2 * ‖w‖ ^ 2 := by
        rw [abs_neg, abs_mul, abs_of_pos (by norm_num),
          abs_of_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg ‖w‖))]
      _ ≤ 2 * ‖w‖ + (1 / 2) * ‖w‖ := by
        linarith only [htw, hss, mul_le_of_le_one_left (sq_nonneg ‖w‖) htSq]
      _ = (5 / 2) * ‖w‖ := by ring
  have hlin : |t * ‖w‖ ^ 2 - w.re| ≤ (3 / 2) * ‖w‖ := by
    calc
      |t * ‖w‖ ^ 2 - w.re| ≤ |t * ‖w‖ ^ 2| + |w.re| := abs_sub ..
      _ = t * ‖w‖ ^ 2 + |w.re| := by simp_all
      _ ≤ (1 / 2) * ‖w‖ + ‖w‖ := by linarith
      _ = (3 / 2) * ‖w‖ := by ring
  have hpowdiff' : |segmentNormSq 1 w t ^ p - 1| ≤ (5 / 2) * L * ‖w‖ := by
    calc
      _ ≤ L * |segmentNormSq 1 w t - 1| := hpowdiff
      _ ≤ L * ((5 / 2) * ‖w‖) := mul_le_mul_of_nonneg_left hqdiff hL
      _ = _ := by ring
  have hlast : |t * ‖w‖ ^ 2| ≤ ‖w‖ ^ 2 := by
    rwa [abs_of_nonneg (mul_nonneg ht₀ (sq_nonneg _))]
  have hmain : |(segmentNormSq 1 w t ^ p - 1) *
      (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2| ≤
        ((15 / 4) * L + 1) * ‖w‖ ^ 2 := by
    calc
      _ ≤ |segmentNormSq 1 w t ^ p - 1| *
          |t * ‖w‖ ^ 2 - w.re| + |t * ‖w‖ ^ 2| := by
            calc
              _ ≤ |(segmentNormSq 1 w t ^ p - 1) * (t * ‖w‖ ^ 2 - w.re)| +
                  |t * ‖w‖ ^ 2| := abs_add_le ..
              _ = _ := by simp
      _ = |segmentNormSq 1 w t ^ p - 1| *
          |t * ‖w‖ ^ 2 - w.re| + |t * ‖w‖ ^ 2| := by rfl
      _ ≤ ((5 / 2) * L * ‖w‖) * ((3 / 2) * ‖w‖) + ‖w‖ ^ 2 := by
            apply add_le_add
            · bound
            · exact hlast
      _ = _ := by ring
  rw [Real.norm_eq_abs]
  calc
    _ = k * |(segmentNormSq 1 w t ^ p - 1) *
        (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2| := by grind
    _ ≤ k * (((15 / 4) * L + 1) * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left hmain (le_of_lt hk)
    _ = _ := by grind

/-- The normalized corrected Taylor remainder is quadratically small on the half-unit disk. -/
theorem norm_unit_taylor_remainder_le :
    |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
  let D : ℝ → ℝ := fun t =>
    k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) *
      (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)
  have hderiv : ∀ t ∈ Icc 0 1,
      HasDerivWithinAt (unitTaylorPath k w) (D t) (Icc 0 1) t := by
    intro t ht
    exact (unitTaylorPath_hasDerivAt k w t ht hw).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico 0 1,
      ‖D t‖ ≤ (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
    intro t ht
    exact unitTaylorPath_deriv_bound k hk hk₂ w hw (Ico_subset_Icc_self ht)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    1 (right_mem_Icc.2 (by norm_num))
  have hzero : unitTaylorPath k w 0 = 0 := by
    simp [unitTaylorPath, segmentRpow, segmentNormSq]
  have hone : unitTaylorPath k w 1 = ‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re := by
    simp [unitTaylorPath, segmentRpow, segmentNormSq, Complex.normSq_eq_norm_sq]
    have htwo : ‖(1 : ℂ) - w‖ ^ ((2 : ℕ) : ℝ) = ‖(1 : ℂ) - w‖ ^ 2 :=
      Real.rpow_natCast _ 2
    calc
      (‖1 - w‖ ^ 2) ^ (k / 2) =
          (‖1 - w‖ ^ ((2 : ℕ) : ℝ)) ^ (k / 2) := by simp
      _ = ‖1 - w‖ ^ (2 * (k / 2)) :=
        (Real.rpow_mul (norm_nonneg _) 2 _).symm
      _ = _ := by ring
  simpa [hzero, hone, Real.norm_eq_abs] using hmean

end

/-- The corrected numerator has a pointwise quadratic tail bound, with no angular averaging. -/
theorem abs_planarTaylorNumerator_le (hk : 0 < k) (hk₂ : k < 2)
    (z u : ℂ) (hu : u ≠ 0) (hlarge : 2 * ‖z‖ ≤ ‖u‖) :
    |‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
        ‖u‖ ^ k * ‖z / u‖ ^ 2 := by
  let w := z / u
  have hw : ‖w‖ ≤ 1 / 2 := by
    dsimp [w]
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hu)).2
    linarith
  have hfactor : ‖u - z‖ ^ k = ‖u‖ ^ k * ‖1 - w‖ ^ k := by
    have heq : u - z = u * (1 - w) := by
      grind
    rw [heq, norm_mul, Real.mul_rpow (norm_nonneg u) (norm_nonneg (1 - w))]
  have hstar : star z / star u = star w := by
    aesop
  have hlinear : (z / u + star z / star u).re = 2 * w.re := by
    rw [hstar]
    simp [Complex.add_re]
    linarith
  have hnum : ‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re =
      ‖u‖ ^ k * (‖1 - w‖ ^ k - 1 + k * w.re) := by
    grind
  rw [hnum]
  have hconst : 0 ≤ k * (1 + (15 / 4) *
      ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2))) := by
    have hfirst : 0 ≤ 1 - k / 2 := by linarith
    positivity
  have hnorm := Real.rpow_nonneg (norm_nonneg u) k
  calc
    _ = ‖u‖ ^ k * |‖1 - w‖ ^ k - 1 + k * w.re| := by
      rw [abs_mul, abs_of_nonneg hnorm]
    _ ≤ ‖u‖ ^ k * ((k * (1 + (15 / 4) *
          ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))) * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_unit_taylor_remainder_le k hk hk₂ w hw) hnorm
    _ = _ := by linarith

end

private theorem rpow_tail_normalize (r s k β : ℝ) (hr : 0 < r) :
    r ^ k * (s / r) ^ 2 / r ^ β = s ^ 2 * r ^ (k - 2 - β) := by
  have hpow1 : r ^ k / r ^ 2 = r ^ (k - 2) := by
    simpa using (Real.rpow_sub hr k 2).symm
  have hpow2 :=
    (Real.rpow_sub hr (k - 2) β).symm
  grind

/-- The full Taylor kernel inherits the same pointwise tail comparison. -/
theorem abs_planarTaylorRemainder_le (k β : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (z u : ℂ) (hu : u ≠ 0) (hlarge : 2 * ‖z‖ ≤ ‖u‖) :
    |DOZZ.planarTaylorRemainder k β z u| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
        ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by
  have hr := norm_pos_iff.mpr hu
  change |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re) / ‖u‖ ^ β| ≤ _
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hr β)]
  have htail := div_le_div_of_nonneg_right (abs_planarTaylorNumerator_le k hk hk₂ z u hu hlarge) (Real.rpow_nonneg hr.le β)
  calc
    _ ≤ (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))) *
        ‖u‖ ^ k * ‖z / u‖ ^ 2 / ‖u‖ ^ β := by assumption
    _ = (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))) *
        ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by
      rw [norm_div]
      have hpower : ‖u‖ ^ k * (‖z‖ / ‖u‖) ^ 2 / ‖u‖ ^ β =
          ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := rpow_tail_normalize ‖u‖ ‖z‖ k β hr
      grind

private theorem measurable_complex_norm_rpow (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) :=
  by fun_prop
section
variable (k β : ℝ)

private theorem measurable_planarTaylorRemainder (z : ℂ) :
    Measurable (DOZZ.planarTaylorRemainder k β z) := by
  change Measurable (fun u =>
    (‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re) / ‖u‖ ^ β)
  fun_prop

theorem integrableOn_planarTaylorRemainder_tail (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) (hz : z ≠ 0) :
    IntegrableOn (DOZZ.planarTaylorRemainder k β z)
      (ball (0 : ℂ) (2 * ‖z‖))ᶜ volume := by
  let p := k - 2 - β
  let C := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))
  let B := C * ‖z‖ ^ 2
  have hr : 0 < 2 * ‖z‖ := by positivity
  have hp : p < -2 := by linarith
  have hB : 0 ≤ B := by
    bound
  have hrad :=
    (integrableOn_norm_rpow_ball_compl_iff p _ hr).2 hp
  change Integrable _
      (volume.restrict _ᶜ)
  apply (hrad.const_mul B).mono' (measurable_planarTaylorRemainder k β z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.compl)] with u hu
  have hlarge : 2 * ‖z‖ ≤ ‖u‖ := by
    simp_all
  have hu : u ≠ 0 := by
    intro hu0
    subst u
    have hlarge0 : 2 * ‖z‖ ≤ 0 := by simp_all
    linarith only [hlarge0, hr]
  calc
    _ ≤ C * ‖z‖ ^ 2 * ‖u‖ ^ p := by simpa [C, p] using (abs_planarTaylorRemainder_le k β hk (lt_trans hβ hβ₂) z u hu hlarge)
    _ = B * ‖u‖ ^ p := by rfl

end

private theorem abs_planarTaylorNumerator_local_le (k : ℝ) (hk : 0 < k)
    (z u : ℂ) (hu : u ≠ 0) (hball : ‖u‖ < 2 * ‖z‖) :
    |‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re| ≤
      (3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1) := by
  have hr := norm_pos_iff.mpr hu
  have ha := norm_nonneg z
  have hshift : ‖u - z‖ ^ k ≤ (3 * ‖z‖) ^ k := by
    have hnorm : ‖u - z‖ ≤ 3 * ‖z‖ := by
      calc
        ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le ..
        _ ≤ 3 * ‖z‖ := by linarith
    bound
  let w := z / u
  have hstar : star z / star u = star w := by
    aesop
  have hlin : |(z / u + star z / star u).re| ≤ 2 * (‖z‖ / ‖u‖) := by
    rw [hstar]
    calc
      |(w + star w).re| ≤ ‖w + star w‖ := Complex.abs_re_le_norm _
      _ ≤ ‖w‖ + ‖star w‖ := norm_add_le ..
      _ = 2 * ‖w‖ := by simp [two_mul]
      _ = 2 * (‖z‖ / ‖u‖) := by aesop
  have hpow : ‖u‖ ^ (k - 1) = ‖u‖ ^ k / ‖u‖ := by
    have h := Real.rpow_sub hr k 1
    simp_all
  have hscale : ‖u‖ ^ k * (‖z‖ / ‖u‖) = ‖z‖ * ‖u‖ ^ (k - 1) := by
    grind
  have hcounter : |(k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re| ≤ k * ‖z‖ * ‖u‖ ^ (k - 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc
      (k / 2) * ‖u‖ ^ k * |(z / u + star z / star u).re|
          ≤ (k / 2) * ‖u‖ ^ k * (2 * (‖z‖ / ‖u‖)) := mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = k * (‖u‖ ^ k * (‖z‖ / ‖u‖)) := by ring
      _ = k * ‖z‖ * ‖u‖ ^ (k - 1) := by nlinarith
  have hshift' : |‖u - z‖ ^ k| ≤ (3 * ‖z‖) ^ k := by
    rwa [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) k)]
  calc
    _ ≤ |‖u - z‖ ^ k - ‖u‖ ^ k| +
        |(k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re| := abs_add_le ..
    _ ≤ |‖u - z‖ ^ k| + |‖u‖ ^ k| +
        k * ‖z‖ * ‖u‖ ^ (k - 1) := add_le_add (abs_sub ..) hcounter
    _ ≤ (3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1) := add_le_add (add_le_add hshift' (le_of_eq (abs_of_nonneg (Real.rpow_nonneg hr.le k)))) le_rfl
section
variable (k β : ℝ)

private theorem abs_planarTaylorRemainder_local_le (hk : 0 < k) (hβ : k < β)
    (z u : ℂ) (hball : ‖u‖ < 2 * ‖z‖) :
    |DOZZ.planarTaylorRemainder k β z u| ≤
      (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) +
        ‖u‖ ^ (k - β) + k * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
  by_cases hu : u = 0
  · subst u
    have hβpos : 0 < β := lt_trans hk hβ
    simp [DOZZ.planarTaylorRemainder, Real.zero_rpow, ne_of_gt hk,
      ne_of_gt hβpos, ne_of_lt (by linarith : k - β < 0),
      ne_of_lt (by linarith : k - 1 - β < 0)]
  · have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos hr β
    have hpow₀ : ‖u‖ ^ (-β) = 1 / ‖u‖ ^ β := by
      calc
        ‖u‖ ^ (-β) = ‖u‖ ^ (0 - β) := by simp
        _ = ‖u‖ ^ (0 : ℝ) / ‖u‖ ^ β := Real.rpow_sub hr 0 β
        _ = 1 / ‖u‖ ^ β := by simp
    have hpow₁ : ‖u‖ ^ k / ‖u‖ ^ β = ‖u‖ ^ (k - β) :=
      (Real.rpow_sub hr k β).symm
    have hpow₂ : ‖u‖ ^ (k - 1) / ‖u‖ ^ β =
        ‖u‖ ^ (k - 1 - β) := (Real.rpow_sub hr _ β).symm
    change |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re) / ‖u‖ ^ β| ≤ _
    rw [abs_div, abs_of_pos hden]
    calc
      _ ≤ ((3 * ‖z‖) ^ k + ‖u‖ ^ k +
          k * ‖z‖ * ‖u‖ ^ (k - 1)) / ‖u‖ ^ β :=
            div_le_div_of_nonneg_right (abs_planarTaylorNumerator_local_le k hk z u hu hball) hden.le
      _ = (3 * ‖z‖) ^ k * (1 / ‖u‖ ^ β) +
          ‖u‖ ^ k / ‖u‖ ^ β +
          k * ‖z‖ * (‖u‖ ^ (k - 1) / ‖u‖ ^ β) := by ring
      _ = (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) +
          ‖u‖ ^ (k - β) + k * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
            simp_all
section
variable (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1)
include hk hβ hβ₂ hβlin

theorem integrableOn_planarTaylorRemainder_ball (z : ℂ) (hz : z ≠ 0) :
    IntegrableOn (DOZZ.planarTaylorRemainder k β z)
      (ball (0 : ℂ) (2 * ‖z‖)) volume := by
  let R : ℝ := 2 * ‖z‖
  let A := (3 * ‖z‖) ^ k
  let p₀ := -β
  let p₁ := k - β
  let p₂ := k - 1 - β
  have hR : 0 < R := by positivity
  have hp₀ : -2 < p₀ := by linarith
  have hp₁ : -2 < p₁ := by linarith
  have hp₂ : -2 < p₂ := by linarith
  have hA : 0 ≤ A := by positivity
  have hC := mul_nonneg (le_of_lt hk) (norm_nonneg z)
  have h₀ :=
    ((integrableOn_norm_rpow_ball_iff p₀ R hR).2 hp₀).const_mul A
  have h₁ :=
    (integrableOn_norm_rpow_ball_iff p₁ R hR).2 hp₁
  have h₂ :=
    ((integrableOn_norm_rpow_ball_iff p₂ R hR).2 hp₂).const_mul (k * ‖z‖)
  change Integrable _
    (volume.restrict _)
  apply ((h₀.add h₁).add h₂).mono' (measurable_planarTaylorRemainder k β z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with u hu
  have hball : ‖u‖ < 2 * ‖z‖ := by
    simpa [Metric.mem_ball, dist_zero_right] using hu
  change |DOZZ.planarTaylorRemainder k β z u| ≤
    A * ‖u‖ ^ p₀ + ‖u‖ ^ p₁ + (k * ‖z‖) * ‖u‖ ^ p₂
  simpa [A, p₀, p₁, p₂, mul_assoc, mul_left_comm, mul_comm] using (abs_planarTaylorRemainder_local_le k β hk hβ z u hball)

/-- The corrected Taylor kernel is absolutely integrable in the convergence window of
`DOZZ.planar_taylor_integral`. -/
theorem integrable_planarTaylorRemainder :
    ∀ z : ℂ, Integrable (DOZZ.planarTaylorRemainder k β z) volume := by
  intro z
  by_cases hz : z = 0
  · subst z
    have hzero : DOZZ.planarTaylorRemainder k β 0 = fun _ : ℂ => 0 := by
      funext u
      simp [DOZZ.planarTaylorRemainder]
    simp_all
  · have hball := integrableOn_planarTaylorRemainder_ball k β hk hβ hβ₂ hβlin z hz
    rw [← integrableOn_univ, ← Set.union_compl_self _,
      integrableOn_union]
    exact ⟨hball, (integrableOn_planarTaylorRemainder_tail k β hk hβ hβ₂ z hz)⟩

end

end

end DOZZ.Proofs
