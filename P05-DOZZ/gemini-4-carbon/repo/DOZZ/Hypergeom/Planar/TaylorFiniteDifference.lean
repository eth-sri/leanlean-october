/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Calculus.Taylor
public import DOZZ.Hypergeom.Planar.TaylorTail

/-! Smooth radial-power calculations away from the moving singularity. -/

@[expose] public section

open Filter Set
open scoped Topology

namespace DOZZ.Proofs

private noncomputable def radialShiftSq (x : ℂ) (t : ℝ) : ℝ :=
  ‖x‖ ^ 2 + x.re * t * 2 + t ^ 2


/-- A global second-difference majorant, including increments that reach or cross the origin. -/
theorem norm_rpow_centered_difference_le_global (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (x y : ℂ) (hx : x ≠ 0) :
    |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤
      (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
  let C : ℝ := k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  let B : ℝ := 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hC : 0 ≤ C := by
    dsimp [C]
    have : 0 ≤ 1 - k / 2 := by linarith
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  by_cases hsmall : ‖y‖ ≤ ‖x‖ / 2
  · let q : ℂ := y / x
    have hqn : ‖q‖ = ‖y‖ / ‖x‖ := norm_div y x
    have hq : ‖q‖ ≤ 1 / 2 := by rw [hqn, div_le_iff₀ hxpos]; linarith
    have hp1 : ‖x + y‖ ^ k = ‖x‖ ^ k * ‖1 + q‖ ^ k := by
      rw [show x + y = x * (1 + q) by dsimp [q]; field_simp [hx], norm_mul,
        Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    have hm1 : ‖x - y‖ ^ k = ‖x‖ ^ k * ‖1 - q‖ ^ k := by
      rw [show x - y = x * (1 - q) by dsimp [q]; field_simp [hx], norm_mul,
        Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    have hrM : |‖1 - q‖ ^ k - 1 + k * q.re| ≤ C * ‖q‖ ^ 2 :=
      norm_unit_taylor_remainder_le k hk hk₂ q hq
    have hrP : |‖1 + q‖ ^ k - 1 - k * q.re| ≤ C * ‖q‖ ^ 2 := by
      rw [show ‖1 + q‖ ^ k - 1 - k * q.re = ‖1 - -q‖ ^ k - 1 + k * (-q).re by
            simp only [sub_neg_eq_add, Complex.neg_re]; ring,
        ← norm_neg q]
      exact norm_unit_taylor_remainder_le k hk hk₂ (-q) (by simpa using hq)
    have hpair : ‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k =
        ‖x‖ ^ k * ((‖1 + q‖ ^ k - 1 - k * q.re) + (‖1 - q‖ ^ k - 1 + k * q.re)) := by
      rw [hp1, hm1]; ring
    have hxk : 0 ≤ ‖x‖ ^ k := Real.rpow_nonneg (norm_nonneg _) _
    have hloc : |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤ 2 * C * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by
      rw [hpair, abs_mul, abs_of_nonneg hxk]
      refine (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hrP hrM)) hxk).trans_eq ?_
      rw [hqn, div_pow, ← Real.rpow_natCast ‖x‖ 2,
        show ‖x‖ ^ k * (C * (‖y‖ ^ 2 / ‖x‖ ^ ((2 : ℕ) : ℝ)) + C * (‖y‖ ^ 2 / ‖x‖ ^ ((2 : ℕ) : ℝ))) =
          2 * C * ‖y‖ ^ 2 * (‖x‖ ^ k / ‖x‖ ^ (2 : ℝ)) by push_cast; ring,
        ← Real.rpow_sub hxpos]
    exact hloc.trans (by
      have hw : 0 ≤ ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by positivity
      change 2 * C * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) ≤ (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2)
      nlinarith)
  · have hlarge : ‖x‖ / 2 < ‖y‖ := lt_of_not_ge hsmall
    have hypos : 0 < ‖y‖ := (half_pos hxpos).trans hlarge
    have hp3 : ‖x + y‖ ^ k ≤ (3 * ‖y‖) ^ k :=
      Real.rpow_le_rpow (norm_nonneg _) ((norm_add_le _ _).trans (by linarith)) hk.le
    have hm3 : ‖x - y‖ ^ k ≤ (3 * ‖y‖) ^ k :=
      Real.rpow_le_rpow (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) hk.le
    have hx2 : ‖x‖ ^ k ≤ (2 * ‖y‖) ^ k :=
      Real.rpow_le_rpow (norm_nonneg _) (by linarith) hk.le
    have hraw : |‖x + y‖ ^ k + ‖x - y‖ ^ k - 2 * ‖x‖ ^ k| ≤ 2 * (3 ^ k + 2 ^ k) * ‖y‖ ^ k := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      rw [Real.mul_rpow (by norm_num) (norm_nonneg y)] at hp3 hm3 hx2
      linarith
    have hyB : ‖y‖ ^ k ≤ ‖y‖ ^ 2 * (2 ^ (2 - k) * ‖x‖ ^ (k - 2)) := by
      have hdec : ‖y‖ ^ (k - 2) ≤ (‖x‖ / 2) ^ (k - 2) :=
        Real.rpow_le_rpow_of_nonpos (half_pos hxpos) hlarge.le (by linarith)
      have hhalf : (‖x‖ / 2) ^ (k - 2) = 2 ^ (2 - k) * ‖x‖ ^ (k - 2) := by
        rw [div_eq_mul_inv, Real.mul_rpow (norm_nonneg _) (by norm_num),
          Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          show -(k - 2) = 2 - k by ring, mul_comm]
      rw [show ‖y‖ ^ k = ‖y‖ ^ (2 : ℝ) * ‖y‖ ^ (k - 2) by
          rw [← Real.rpow_add hypos]; congr 1; ring, Real.rpow_two]
      exact mul_le_mul_of_nonneg_left (hdec.trans_eq hhalf) (sq_nonneg _)
    refine hraw.trans ((mul_le_mul_of_nonneg_left hyB (by positivity)).trans ?_)
    have hw : 0 ≤ ‖y‖ ^ 2 * ‖x‖ ^ (k - 2) := by positivity
    change 2 * (3 ^ k + 2 ^ k) * (‖y‖ ^ 2 * (2 ^ (2 - k) * ‖x‖ ^ (k - 2))) ≤
      (2 * C + B) * ‖y‖ ^ 2 * ‖x‖ ^ (k - 2)
    dsimp [B]; nlinarith

/-- The four-direction discrete Laplacian is dominated by the positive radial kernel, uniformly
in every nonzero step. -/
theorem norm_rpow_discrete_laplacian_le (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (x : ℂ) (t : ℝ) (hx : x ≠ 0) (ht : t ≠ 0) :
    |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
      ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
      4 * ‖x‖ ^ k) / t ^ 2| ≤
      (2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
  have hR := norm_rpow_centered_difference_le_global k hk hk₂ x (t : ℂ) hx
  have hI := norm_rpow_centered_difference_le_global k hk hk₂ x ((t : ℂ) * Complex.I) hx
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hR hI
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  rw [abs_div, abs_of_pos ht2, div_le_iff₀ ht2,
    show ‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k + ‖x + (t : ℂ) * Complex.I‖ ^ k +
        ‖x - (t : ℂ) * Complex.I‖ ^ k - 4 * ‖x‖ ^ k =
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) +
        (‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k - 2 * ‖x‖ ^ k) by ring]
  exact ((abs_add_le _ _).trans (add_le_add hR hI)).trans_eq (by ring)

section
variable (k : ℝ) (x : ℂ) (hx : x ≠ 0)
include k hx

/-- The real-coordinate centered difference of `‖x+t‖^k` converges to its second derivative
at every nonzero center. -/
theorem norm_rpow_real_centered_difference_tendsto :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) *
          (2 * x.re) ^ 2 + (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
  have radialShiftSq_eq (x : ℂ) (t : ℝ) : radialShiftSq x t = ‖x + (t : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp [radialShiftSq, Complex.mul_re, Complex.normSq_eq_norm_sq]
    ring
  let p := k / 2
  let q := radialShiftSq x
  let f : ℝ → ℝ := fun t => ‖x + (t : ℂ)‖ ^ k
  have hfq (t : ℝ) : f t = q t ^ p := by
    dsimp [f, q, p]
    rw [radialShiftSq_eq, ← Real.rpow_natCast_mul (norm_nonneg _), show (2 : ℕ) * (k / 2) = k by push_cast; ring]
  have hq_hd (t : ℝ) : HasDerivAt q (2 * x.re + 2 * t) t := by
    change HasDerivAt (fun s : ℝ => ‖x‖ ^ 2 + x.re * s * 2 + s ^ 2) _ t
    have hlin : HasDerivAt (fun s : ℝ => x.re * s * 2) (2 * x.re) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (hasDerivAt_id t).const_mul (2 * x.re)
    convert (hasDerivAt_const t (‖x‖ ^ 2)).add (hlin.add ((hasDerivAt_id t).pow 2)) using 1
    · ext s; simp only [Pi.add_apply, Pi.pow_apply, id_eq]; ring
    · simp
  have hq0 : q 0 = ‖x‖ ^ 2 := by simp [q, radialShiftSq]
  have hq0_pos : 0 < q 0 := by rw [hq0]; positivity
  have hf_d1 : ∀ᶠ t in 𝓝 (0 : ℝ), deriv f t = p * q t ^ (p - 1) * (2 * x.re + 2 * t) := by
    have hqc : Continuous q := by unfold q radialShiftSq; fun_prop
    filter_upwards [hqc.continuousAt.eventually (isOpen_Ioi.mem_nhds hq0_pos)] with t ht
    rw [funext hfq]
    exact (((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).comp t (hq_hd t)).deriv).trans (by ring)
  have hf_d2 : deriv (deriv f) 0 =
      p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 + p * (‖x‖ ^ 2) ^ (p - 1) * 2 := by
    have hd_rhs : HasDerivAt (fun t : ℝ => p * q t ^ (p - 1) * (2 * x.re + 2 * t))
        (p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * x.re) ^ 2 + p * (‖x‖ ^ 2) ^ (p - 1) * 2) 0 := by
      have hp1 := (Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hq0_pos.ne')).comp 0 (hq_hd 0)
      have hl1 : HasDerivAt (fun t : ℝ => 2 * x.re + 2 * t) 2 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_add (2 * x.re)
      convert ((hp1.const_mul p).mul hl1) using 1
      · ext t; simp only [Pi.mul_apply, Function.comp_apply]
      · dsimp only [Function.comp_apply]; rw [hq0]; ring
    exact (hd_rhs.congr_of_eventuallyEq hf_d1).deriv
  let ρ := ‖x‖ / 2
  let s := Ioo (-ρ) ρ
  have hsO : IsOpen s := isOpen_Ioo
  have h0s : (0 : ℝ) ∈ s := ⟨by dsimp [ρ]; linarith [norm_pos_iff.2 hx], by dsimp [ρ]; positivity⟩
  have hq_ne : ∀ t ∈ s, q t ≠ 0 := fun t ht => by
    dsimp only [q]; rw [radialShiftSq_eq]
    have hlt : |t| < ‖x‖ / 2 := abs_lt.2 ht
    have hlb : ‖x‖ - |t| ≤ ‖x + (t : ℂ)‖ := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using norm_sub_norm_le x (-(t : ℂ))
    have hp0 : 0 < ‖x + (t : ℂ)‖ := by linarith [norm_pos_iff.2 hx]
    exact pow_ne_zero 2 hp0.ne'
  have hfC2 : ContDiffOn ℝ 2 f s := by
    rw [funext hfq]
    exact (by unfold q radialShiftSq; fun_prop : ContDiff ℝ 2 q).contDiffOn.rpow_const_of_ne hq_ne
  let P : ℝ → ℝ := fun t => taylorWithinEval f 2 s 0 t
  have hTay : Tendsto (fun t : ℝ => (f t - P t) / t ^ 2) (𝓝 0) (𝓝 0) := by
    have h := Real.taylor_tendsto (convex_Ioo (-ρ) ρ) h0s hfC2
    rw [hsO.nhdsWithin_eq h0s] at h
    simpa [P] using h
  have hid : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_right nhdsWithin_le_nhds
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by simpa using hid.neg
  have hP_eq (t : ℝ) : P t = f 0 + t * deriv f 0 + (t ^ 2 / 2) * deriv (deriv f) 0 := by
    have h1 : iteratedDerivWithin 1 f s 0 = deriv f 0 := by
      simpa [iteratedDeriv_eq_iterate] using iteratedDerivWithin_of_isOpen_eq_iterate (n := 1) hsO h0s
    have h2 : iteratedDerivWithin 2 f s 0 = deriv (deriv f) 0 := by
      simpa [iteratedDeriv_eq_iterate] using iteratedDerivWithin_of_isOpen_eq_iterate (n := 2) hsO h0s
    simp only [P, taylorWithinEval_succ, taylor_within_zero_eval, h1, h2,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero, Nat.cast_one,
      zero_add, one_mul, inv_one, sub_zero, pow_one]; ring
  have hsum : Tendsto (fun t : ℝ => deriv (deriv f) 0 + ((f t - P t) / t ^ 2 + (f (-t) - P (-t)) / t ^ 2))
      (𝓝[≠] 0) (𝓝 (deriv (deriv f) 0)) := by
    have hnE : Tendsto (fun t : ℝ => (f (-t) - P (-t)) / t ^ 2) (𝓝[≠] 0) (𝓝 0) :=
      (hTay.comp hneg).congr fun t => by dsimp; rw [neg_sq]
    simpa [add_assoc] using tendsto_const_nhds.add ((hTay.comp hid).add hnE)
  rw [← hf_d2]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  dsimp only [f]
  rw [hP_eq t, hP_eq (-t)]
  dsimp only [f]
  rw [Complex.ofReal_zero, add_zero, show x + ((-t : ℝ) : ℂ) = x - (t : ℂ) by push_cast; ring]
  field_simp [ht]; ring

/-- The symmetric four-direction discrete Laplacian of a radial power converges to its
planar Laplacian away from the origin. -/
theorem norm_rpow_discrete_laplacian_tendsto :
    Tendsto (fun t : ℝ =>
      (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
        ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
        4 * ‖x‖ ^ k) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (k ^ 2 * ‖x‖ ^ (k - 2))) := by
  let y := -Complex.I * x
  have hy : y ≠ 0 := mul_ne_zero (by simp) hx
  have hIm : Tendsto (fun t : ℝ => (‖x + (t : ℂ) * Complex.I‖ ^ k +
      ‖x - (t : ℂ) * Complex.I‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2) (𝓝[≠] 0)
      (𝓝 ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) * (2 * x.im) ^ 2 +
        (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2)) := by
    have hyn : ‖y‖ = ‖x‖ := by simp [y]
    have hyr : y.re = x.im := by simp [y, Complex.mul_re]
    have hp (t : ℝ) : ‖x + (t : ℂ) * Complex.I‖ = ‖y + (t : ℂ)‖ := by
      calc ‖x + (t : ℂ) * Complex.I‖ = ‖(-Complex.I) * (x + (t : ℂ) * Complex.I)‖ := by simp
        _ = ‖y + (t : ℂ)‖ := by congr 1; dsimp [y]; rw [mul_add]; simp [mul_left_comm]
    have hm (t : ℝ) : ‖x - (t : ℂ) * Complex.I‖ = ‖y - (t : ℂ)‖ := by
      calc ‖x - (t : ℂ) * Complex.I‖ = ‖(-Complex.I) * (x - (t : ℂ) * Complex.I)‖ := by simp
        _ = ‖y - (t : ℂ)‖ := by congr 1; dsimp [y]; rw [mul_sub]; simp [mul_left_comm]
    simpa [hyr, hyn, ← hp, ← hm] using norm_rpow_real_centered_difference_tendsto k y hy
  have hcoef : ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) * (2 * x.re) ^ 2 +
        (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) +
      ((k / 2) * (k / 2 - 1) * (‖x‖ ^ 2) ^ (k / 2 - 2) * (2 * x.im) ^ 2 +
        (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) * 2) = k ^ 2 * ‖x‖ ^ (k - 2) := by
    have hr : 0 < ‖x‖ ^ 2 := by positivity
    have hre_im : (2 * x.re) ^ 2 + (2 * x.im) ^ 2 = 4 * ‖x‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hpow : (‖x‖ ^ 2) ^ (k / 2 - 2) * ‖x‖ ^ 2 = (‖x‖ ^ 2) ^ (k / 2 - 1) := by
      calc (‖x‖ ^ 2) ^ (k / 2 - 2) * ‖x‖ ^ 2 = (‖x‖ ^ 2) ^ (k / 2 - 2) * (‖x‖ ^ 2) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (‖x‖ ^ 2) ^ (k / 2 - 1) := by rw [← Real.rpow_add hr]; congr 1; ring
    have hnp : (‖x‖ ^ 2) ^ (k / 2 - 1) = ‖x‖ ^ (k - 2) := by
      rw [← Real.rpow_natCast_mul (norm_nonneg x)]; congr 1; push_cast; ring
    calc _ = (k / 2) * (k / 2 - 1) * ((‖x‖ ^ 2) ^ (k / 2 - 2) * ((2 * x.re) ^ 2 + (2 * x.im) ^ 2)) +
          4 * (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) := by ring
      _ = (k / 2) * (k / 2 - 1) * ((‖x‖ ^ 2) ^ (k / 2 - 2) * ‖x‖ ^ 2 * 4) +
          4 * (k / 2) * (‖x‖ ^ 2) ^ (k / 2 - 1) := by rw [hre_im]; ring
      _ = k ^ 2 * ‖x‖ ^ (k - 2) := by rw [hpow, hnp]; ring
  rw [← hcoef]
  exact ((norm_rpow_real_centered_difference_tendsto k x hx).add hIm).congr
    fun t => by ring


end
end DOZZ.Proofs
