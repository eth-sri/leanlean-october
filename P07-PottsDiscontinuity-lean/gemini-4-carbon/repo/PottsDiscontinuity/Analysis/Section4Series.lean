module

public import Mathlib
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Bethe.Prop21Coeff
public import PottsDiscontinuity.Bethe.Prop21Tau
public import PottsDiscontinuity.Bethe.RatioProducts

/-! # Section 4 Fourier series, Abel regularization, and source-coordinate exponent -/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-! ### 1. Explicit `P` profile, sine kernel integrals, and Identity (4.3) -/

noncomputable def fourierP (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else (1 / 2 : ℝ) * Real.log ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α))

private theorem fourierP_eq_log_norm {lam c α : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1) :
    fourierP lam α = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))‖ := by
  have hα : α ≠ 0 := fun h => by subst h; norm_num at hcos
  let E : ℂ := (Real.exp lam : ℂ); let w : ℂ := Complex.exp (I * (α : ℂ))
  have hwNe : w ≠ 0 := Complex.exp_ne_zero _
  have hEw : E - w ≠ 0 := Bethe.ofReal_sub_ne_zero (by simpa using hlam) (by simp [w])
  have h1w : 1 - w ≠ 0 := fun h => by
    have hre := congrArg Complex.re (show w = 1 by linear_combination -h)
    change (Complex.exp (I * (α : ℂ))).re = 1 at hre
    rw [Bethe.exp_I_mul_ofReal] at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
    linarith
  have hEpos : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  have hEc : E ≠ 0 := by change (Real.exp lam : ℂ) ≠ 0; exact_mod_cast hEpos
  have hcsq : (c : ℂ) ^ 2 = (E + 1) ^ 2 / E := by
    simpa [E] using congrArg (fun x : ℝ => (x : ℂ)) (show c ^ 2 = (Real.exp lam + 1) ^ 2 / Real.exp lam by
      rw [hc, Real.cosh_eq, Real.exp_neg]; field_simp [hEpos]; ring)
  have hz : Complex.exp (I * (Bethe.kMap lam α : ℂ)) = (w * E - 1) / (E - w) := by
    rw [Bethe.exp_I_mul_kMap_aux hlam α, Complex.exp_neg]; dsimp [w, E]; field_simp [hwNe]
  have hden : 1 - Complex.exp (I * (Bethe.kMap lam α : ℂ)) = (E + 1) * (1 - w) / (E - w) := by
    rw [hz]; field_simp [hEw]; ring
  have hM : BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ))) = (w - E ^ 2) / (E * (1 - w)) := by
    rw [BetheAnsatz.M, hden, hcsq]; field_simp [hEw, h1w, hEc]; ring
  have hwform : w = (Real.cos α : ℂ) + (Real.sin α : ℂ) * I := by simpa [w] using Bethe.exp_I_mul_ofReal α
  have hwRe : w.re = Real.cos α := by
    rw [hwform]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hwIm : w.im = Real.sin α := by
    rw [hwform]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero]; simp
  have hnum : Complex.normSq (w - E ^ 2) = Real.exp lam ^ 4 - 2 * Real.exp lam ^ 2 * Real.cos α + 1 := by
    have hE2re : (E ^ 2).re = Real.exp lam ^ 2 := by change ((Real.exp lam : ℂ) ^ 2).re = _; rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hE2im : (E ^ 2).im = 0 := by change ((Real.exp lam : ℂ) ^ 2).im = _; rw [← Complex.ofReal_pow, Complex.ofReal_im]
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm, hE2re, hE2im]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h1wSq : Complex.normSq (1 - w) = 2 - 2 * Real.cos α := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm]; simp; nlinarith [Real.sin_sq_add_cos_sq α]
  have hnormSq : ‖BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))‖ ^ 2 =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
    rw [← Complex.normSq_eq_norm_sq, hM, Complex.normSq_div, Complex.normSq_mul, hnum, h1wSq,
      show Complex.normSq E = Real.exp lam ^ 2 by dsimp [E]; rw [Complex.normSq_ofReal]; ring,
      show Real.cosh (2 * lam) = (Real.exp lam ^ 2 + (Real.exp lam ^ 2)⁻¹) / 2 by
        rw [Real.cosh_eq, show 2 * lam = lam + lam by ring, Real.exp_neg, Real.exp_add]; ring]
    have : 2 - 2 * Real.cos α ≠ 0 := by linarith
    field_simp [hEpos]; ring
  unfold fourierP; rw [ite_eq_right hα]; change (1 / 2 : ℝ) * _ = _; rw [← hnormSq, Real.log_pow]; ring

private theorem fourier_one_sub_cos_lower {α : ℝ} (hα : α ∈ Icc (-π) π) :
    2 * α ^ 2 / π ^ 2 ≤ 1 - Real.cos α := by
  have hx : |α / 2| ≤ π / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_le.mpr ⟨by linarith [hα.1], hα.2⟩]
  have hjSq := (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 (Real.mul_abs_le_abs_sin hx)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), show (2 / π * (|α| / 2)) ^ 2 = α ^ 2 / π ^ 2 by
    field_simp [Real.pi_ne_zero]; rw [sq_abs], sq_abs] at hjSq
  have hsin := Real.sin_sq_eq_half_sub (α / 2)
  rw [show 2 * (α / 2) = α by ring] at hsin
  rw [show 2 * α ^ 2 / π ^ 2 = 2 * (α ^ 2 / π ^ 2) by ring]; linarith

noncomputable def fourierPPrime (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else (1 / 2 : ℝ) * (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) - Real.sin α / (1 - Real.cos α))

private theorem fourierP_hasDerivAt {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    HasDerivAt (fourierP lam) (fourierPPrime lam α) α := by
  have hden : 0 < 1 - Real.cos α := lt_of_lt_of_le
    (div_pos (mul_pos two_pos (sq_pos_of_ne_zero hα0)) (by positivity))
    (fourier_one_sub_cos_lower (Ioo_subset_Icc_self hα))
  have hnum : 0 < Real.cosh (2 * lam) - Real.cos α := by
    linarith [Real.one_lt_cosh.mpr (show (2 * lam : ℝ) ≠ 0 by positivity), Real.cos_le_one α]
  have hu : HasDerivAt (fun x => Real.cosh (2 * lam) - Real.cos x) (Real.sin α) α := by
    simpa using (Real.hasDerivAt_cos α).const_sub _
  have hv : HasDerivAt (fun x => 1 - Real.cos x) (Real.sin α) α := by
    simpa using (Real.hasDerivAt_cos α).const_sub _
  refine (((hu.div hv hden.ne').log (div_ne_zero hnum.ne' hden.ne')).const_mul (1 / 2 : ℝ)).congr_deriv
    (by simp [fourierPPrime, hα0]; field_simp [hden.ne', hnum.ne']) |>.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hα0] with x hx; simp [fourierP, hx]

private noncomputable def fourierCotSin (n : ℕ) (α : ℝ) : ℝ :=
  if α = 0 then 0 else Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (1 - Real.cos α)

private theorem fourierP_prime_sine_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ∫ α in (-π)..π, fourierPPrime lam α * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      π * (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1) := by
  have hcot : IntervalIntegrable (fourierCotSin n) volume (-π) π ∧ ∫ α in (-π)..π, fourierCotSin n α = 2 * π := by
    have hden_pos {α : ℝ} (hα : α ∈ uIoc (-π) π) (hα0 : α ≠ 0) : 1 - Real.cos α ≠ 0 := by
      have hio : α ∈ Ioc (-π) π := by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
      exact (lt_of_lt_of_le (div_pos (mul_pos two_pos (sq_pos_of_ne_zero hα0)) (by positivity))
        (fourier_one_sub_cos_lower (Ioc_subset_Icc_self hio))).ne'
    induction n with
    | zero =>
      have hEq : fourierCotSin 0 =ᵐ[volume.restrict (uIoc (-π) π)] fun α => 1 + Real.cos α := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
        have hd := hden_pos hα hα0; simp [fourierCotSin, hα0]; field_simp [hd]; nlinarith [Real.sin_sq_add_cos_sq α]
      refine ⟨((by fun_prop : Continuous fun α : ℝ => 1 + Real.cos α).intervalIntegrable _ _).congr_ae hEq.symm, ?_⟩
      rw [intervalIntegral.integral_congr_ae_restrict hEq,
        intervalIntegral.integral_add intervalIntegrable_const (Real.continuous_cos.intervalIntegrable _ _),
        intervalIntegral.integral_const]; simp; ring
    | succ k ih =>
      have hEq : fourierCotSin (k + 1) =ᵐ[volume.restrict (uIoc (-π) π)]
          fun α => fourierCotSin k α + Real.cos (((k + 2 : ℕ) : ℝ) * α) + Real.cos (((k + 1 : ℕ) : ℝ) * α) := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
        have hd := hden_pos hα hα0
        have hrec : Real.sin α * (Real.sin (((k + 2 : ℕ) : ℝ) * α) - Real.sin (((k + 1 : ℕ) : ℝ) * α)) =
            (1 - Real.cos α) * (Real.cos (((k + 2 : ℕ) : ℝ) * α) + Real.cos (((k + 1 : ℕ) : ℝ) * α)) := by
          rw [show ((k + 2 : ℕ) : ℝ) * α = ((k + 1 : ℕ) : ℝ) * α + α by push_cast; ring, Real.sin_add, Real.cos_add]
          have hsq := Real.sin_sq_add_cos_sq α
          nlinarith [hsq, congrArg (Real.cos (((k + 1 : ℕ) : ℝ) * α) * ·) hsq]
        simp only [fourierCotSin, hα0, ↓reduceIte]; field_simp [hd]
        rw [show ((k + 1 + 1 : ℕ) : ℝ) * α = ((k + 2 : ℕ) : ℝ) * α by push_cast; ring,
          show α * ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * α by ring]; linarith
      have hc1 : IntervalIntegrable (fun α : ℝ => Real.cos (((k + 2 : ℕ) : ℝ) * α)) volume (-π) π :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      have hc2 : IntervalIntegrable (fun α : ℝ => Real.cos (((k + 1 : ℕ) : ℝ) * α)) volume (-π) π :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      refine ⟨((ih.1.add hc1).add hc2).congr_ae hEq.symm, ?_⟩
      rw [intervalIntegral.integral_congr_ae_restrict hEq,
        intervalIntegral.integral_add (ih.1.add hc1) hc2, intervalIntegral.integral_add ih.1 hc1,
        ih.2, Bethe.integral_cos_nat_mul (by omega), Bethe.integral_cos_nat_mul (by omega)]; ring
  let μ := 2 * lam; have hμ : 0 < μ := by positivity
  let r := Real.exp (-μ)
  have hker : ∫ α in (-π)..π, Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (Real.cosh μ - Real.cos α) = 2 * π * r ^ (n + 1) := by
    have hcoeff (k : ℕ) : ∫ α in (-π)..π, Bethe.Xi μ α * Real.cos ((k : ℝ) * α) = 2 * π * r ^ k := by
      have h : Bethe.cosCoeff (Bethe.Xi μ) k = 2 * π * r ^ k := by
        cases k with
        | zero => rw [Bethe.Xi_eq_trigSeries hμ, Bethe.cosCoeff_trigSeries_zero (Bethe.summable_two_mul_exp_pow hμ) summable_zero 1]; simp
        | succ k => rw [Bethe.Xi_eq_trigSeries hμ, Bethe.cosCoeff_trigSeries_succ (Bethe.summable_two_mul_exp_pow hμ) summable_zero 1 k]; dsimp [r]; ring
      simpa [Bethe.cosCoeff] using h
    have hprod : (fun α : ℝ => Bethe.Xi μ α * Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) =
        fun α => (1 / 2 : ℝ) * (Bethe.Xi μ α * Real.cos ((n : ℝ) * α)) -
          (1 / 2 : ℝ) * (Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α)) := funext fun α => by
      have hcM := Real.cos_sub (((n + 1 : ℕ) : ℝ) * α) α
      have hcP := Real.cos_add (((n + 1 : ℕ) : ℝ) * α) α
      rw [show ((n + 1 : ℕ) : ℝ) * α - α = (n : ℝ) * α by push_cast; ring] at hcM
      rw [show ((n + 1 : ℕ) : ℝ) * α + α = ((n + 2 : ℕ) : ℝ) * α by push_cast; ring] at hcP
      rw [mul_assoc, show Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
        (Real.cos ((n : ℝ) * α) - Real.cos (((n + 2 : ℕ) : ℝ) * α)) / 2 by linarith]; ring
    have hInt (k : ℕ) : IntervalIntegrable (fun α : ℝ => (1 / 2 : ℝ) * (Bethe.Xi μ α * Real.cos ((k : ℝ) * α))) volume (-π) π :=
      (((Bethe.continuous_Xi hμ).mul (by fun_prop)).const_mul _).intervalIntegrable _ _
    have hsinhNe : Real.sinh μ ≠ 0 := (Real.sinh_pos_iff.mpr hμ).ne'
    have hfun : (fun α : ℝ => Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (Real.cosh μ - Real.cos α)) =
        fun α => (Real.sinh μ)⁻¹ * (Bethe.Xi μ α * Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) := funext fun α => by
      have hd : Real.cosh μ - Real.cos α ≠ 0 := by linarith [Real.one_lt_cosh.mpr hμ.ne', Real.cos_le_one α]
      rw [Bethe.Xi]; field_simp [hsinhNe, hd]
    rw [hfun, intervalIntegral.integral_const_mul, hprod, intervalIntegral.integral_sub (hInt n) (hInt (n + 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcoeff n, hcoeff (n + 2)]
    have hsinh : 1 - r ^ 2 = 2 * r * Real.sinh μ := by dsimp [r]; rw [Real.sinh_eq, Real.exp_neg]; field_simp [Real.exp_ne_zero]
    change (Real.sinh μ)⁻¹ * (1 / 2 * (2 * π * r ^ n) - 1 / 2 * (2 * π * r ^ (n + 2))) = 2 * π * r ^ (n + 1)
    rw [show 1 / 2 * (2 * π * r ^ n) - 1 / 2 * (2 * π * r ^ (n + 2)) = π * r ^ n * (1 - r ^ 2) by rw [pow_add]; ring,
      hsinh, pow_succ]; field_simp [hsinhNe]
  have hratioInt : IntervalIntegrable (fun α : ℝ =>
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (Real.cosh μ - Real.cos α)) volume (-π) π :=
    ((by fun_prop : Continuous _).div (by fun_prop) fun α => by
      linarith [Real.one_lt_cosh.mpr hμ.ne', Real.cos_le_one α]).intervalIntegrable _ _
  have hEq : (fun α => fourierPPrime lam α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) =ᵐ[volume.restrict (uIoc (-π) π)]
      fun α => (1 / 2 : ℝ) * (Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (Real.cosh μ - Real.cos α) - fourierCotSin n α) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα0
    simp [fourierPPrime, fourierCotSin, μ, hα0]; ring
  rw [intervalIntegral.integral_congr_ae_restrict hEq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hratioInt hcot.1, hker, hcot.2,
    show Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) = r ^ (n + 1) by
      dsimp [r, μ]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
  ring

/-- The ordered partial sums of `∑ (-1)^m tanh(λm)/m`. -/
noncomputable def altTanhPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam)

private noncomputable def logCoshTauCorrectionPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) * (Real.exp (-2 * lam * m) - 1)

private theorem identity43 (lam : ℝ) (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (fun N => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N) atTop (𝓝 (lam + 2 * S)) := by
  obtain ⟨S, _, hS, _, _, _⟩ := identity44 lam hlam
  have hS' : Tendsto (altTanhPartial lam) atTop (𝓝 S) := hS
  refine ⟨S, hS', ?_⟩
  let q := Real.exp (-2 * lam)
  have hq : 0 < q := Real.exp_pos _; have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let logTerm (m : ℕ) : ℝ := (-1 : ℝ) ^ m / (m : ℝ) * (Real.exp (-2 * lam * m) - 1)
  have hlogExp : Tendsto (fun N => ∑ m ∈ Finset.Icc 1 N, logTerm m) atTop (𝓝 (lam - Real.log (Real.cosh lam))) := by
    have hpart (N : ℕ) : (∑ m ∈ Finset.Icc 1 N, logTerm m) = ∫ x in q..1, (1 - (-x) ^ N) / (1 + x) := by
      rw [sum_Icc_one_eq_sum_range]
      have hterm (n : ℕ) : logTerm (n + 1) = ∫ x in q..1, (-x) ^ n := by
        dsimp [logTerm]
        rw [show (fun x : ℝ => (-x) ^ n) = fun x => (-1 : ℝ) ^ n * x ^ n from funext fun _ => neg_pow _ _,
          intervalIntegral.integral_const_mul, integral_pow,
          show Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) = q ^ (n + 1) by dsimp [q]; rw [← Real.exp_nat_mul]; congr 1; ring]
        push_cast; rw [pow_succ, pow_succ]; ring
      simp_rw [hterm]
      rw [← intervalIntegral.integral_finsetSum (f := fun n (x : ℝ) => (-x) ^ n)
        fun n _ => (continuous_id.neg.pow n).intervalIntegrable _ _]
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hd : 1 + x ≠ 0 := by linarith [hq.le.trans ((by simpa [uIcc_of_le hq1.le] using hx : x ∈ Icc q 1).1)]
      induction N with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; field_simp [hd]; ring
    have htarg : ∫ x in q..1, (1 + x)⁻¹ = Real.log 2 - Real.log (1 + q) := by
      rw [show (fun x : ℝ => (1 + x)⁻¹) = fun x => (x + 1)⁻¹ from funext fun _ => by ring,
        intervalIntegral.integral_comp_add_right, integral_inv_of_pos (by linarith) (by norm_num),
        show (1 + 1) / (q + 1) = 2 / (1 + q) by ring, Real.log_div two_ne_zero (by positivity)]
    have hrem (N : ℕ) : |(∑ m ∈ Finset.Icc 1 N, logTerm m) - (Real.log 2 - Real.log (1 + q))| ≤ 1 / ((N : ℝ) + 1) := by
      have hdom (x) (hx : x ∈ uIcc q 1) : 1 + x ≠ 0 := by
        linarith [(by simpa [uIcc_of_le hq1.le] using hx : x ∈ Icc q 1).1]
      have hkInt : IntervalIntegrable (fun x : ℝ => (1 - (-x) ^ N) / (1 + x)) volume q 1 :=
        ((continuousOn_const.sub (continuousOn_id.neg.pow N)).div (continuousOn_const.add continuousOn_id) hdom).intervalIntegrable
      have hiInt : IntervalIntegrable (fun x : ℝ => (1 + x)⁻¹) volume q 1 :=
        ((continuousOn_const.add continuousOn_id).inv₀ hdom).intervalIntegrable
      have hjInt : IntervalIntegrable (fun x : ℝ => x ^ N / (1 + x)) volume q 1 :=
        ((continuousOn_id.pow N).div (continuousOn_const.add continuousOn_id) hdom).intervalIntegrable
      have hpInt : IntervalIntegrable (fun x : ℝ => x ^ N) volume q 1 := (continuous_id.pow N).intervalIntegrable _ _
      rw [hpart N, ← htarg, ← intervalIntegral.integral_sub hkInt hiInt,
        show (fun x : ℝ => (1 - (-x) ^ N) / (1 + x) - (1 + x)⁻¹) = fun x => -((-1 : ℝ) ^ N) * (x ^ N / (1 + x)) from
          funext fun x => by rw [neg_pow]; field_simp; ring,
        intervalIntegral.integral_const_mul, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (intervalIntegral.integral_nonneg hq1.le fun x hx =>
          div_nonneg (pow_nonneg (hq.le.trans hx.1) _) (by linarith [hx.1]))]
      refine (intervalIntegral.integral_mono_on hq1.le hjInt hpInt
        fun x hx => div_le_self (pow_nonneg (hq.le.trans hx.1) _) (by linarith [hx.1])).trans ?_
      rw [integral_pow, one_pow]; exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hq.le (N + 1)]) (by positivity)
    have hval : Real.log 2 - Real.log (1 + q) = lam - Real.log (Real.cosh lam) := by
      have hc : Real.cosh lam = Real.exp lam * ((1 + q) / 2) := by
        rw [Real.cosh_eq, show Real.exp (-lam) = Real.exp lam * q by dsimp [q]; rw [← Real.exp_add]; congr 1; ring]; ring
      rw [hc, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp, Real.log_div (by positivity) two_ne_zero]; ring
    rw [← hval, tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun N => by simpa [Real.norm_eq_abs] using hrem N)
      (by simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpoint (N : ℕ) : Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N =
      Real.log (Real.cosh lam) + (∑ m ∈ Finset.Icc 1 N, logTerm m) + 2 * altTanhPartial lam N := by
    have hsum : (∑ m ∈ Finset.Icc 1 N, logTerm m) + logCoshTauCorrectionPartial lam N = -2 * altTanhPartial lam N := by
      unfold logCoshTauCorrectionPartial altTanhPartial
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      dsimp [logTerm]
      have ht : (1 + Real.tanh ((m : ℝ) * lam)) * (Real.exp (-2 * lam * (m : ℝ)) - 1) = -2 * Real.tanh ((m : ℝ) * lam) := by
        rw [Real.tanh_eq, show -2 * lam * (m : ℝ) = -((m : ℝ) * lam) - (m : ℝ) * lam by ring, Real.exp_sub]
        field_simp [(Real.exp_pos _).ne']; ring
      linear_combination ((-1 : ℝ) ^ m / (m : ℝ)) * ht
    linarith
  simp_rw [hpoint]
  have htot := ((tendsto_const_nhds (x := Real.log (Real.cosh lam))).add hlogExp).add (hS'.const_mul 2)
  rwa [show Real.log (Real.cosh lam) + (lam - Real.log (Real.cosh lam)) + 2 * S = lam + 2 * S by ring] at htot

/-! ### 2. Abel Regularization of the `τ` Integral -/

private noncomputable def fourierPrimeControl (lam : ℝ) : ℝ :=
  (π / (Real.cosh (2 * lam) - 1) + π ^ 2 / 2) / 2

private theorem fourierPPrime_alpha_bound {lam α : ℝ} (hlam : 0 < lam) (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α| * |α| ≤ fourierPrimeControl lam := by
  have hcoshden : 0 < Real.cosh (2 * lam) - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr (by positivity))
  by_cases hα0 : α = 0
  · simp only [fourierPPrime, hα0, ↓reduceIte, abs_zero, zero_mul, fourierPrimeControl]; positivity
  · have hcosLower := fourier_one_sub_cos_lower hα
    have hαabs : |α| ≤ π := abs_le.mpr ⟨by linarith [hα.1], hα.2⟩
    have hdenLower : 0 < 1 - Real.cos α := lt_of_lt_of_le
      (div_pos (mul_pos two_pos (sq_pos_of_ne_zero hα0)) (by positivity)) hcosLower
    have hden1 : 0 < Real.cosh (2 * lam) - Real.cos α := by linarith [Real.cos_le_one α]
    have h1 : |Real.sin α| * |α| / (Real.cosh (2 * lam) - Real.cos α) ≤ π / (Real.cosh (2 * lam) - 1) := by
      rw [div_le_div_iff₀ hden1 hcoshden]
      exact (mul_le_mul_of_nonneg_right (by nlinarith [Real.abs_sin_le_one α, abs_nonneg α]) hcoshden.le).trans
        (mul_le_mul_of_nonneg_left (by linarith [Real.cos_le_one α]) Real.pi_pos.le)
    have h2 : |Real.sin α| * |α| / (1 - Real.cos α) ≤ π ^ 2 / 2 := by
      rw [div_le_iff₀ hdenLower]
      have : |Real.sin α| * |α| ≤ α ^ 2 := by nlinarith [Real.abs_sin_le_abs (x := α), sq_abs α, abs_nonneg α]
      have hmul := mul_le_mul_of_nonneg_left hcosLower (show (0 : ℝ) ≤ π ^ 2 / 2 by positivity)
      rw [show (π ^ 2 / 2) * (2 * α ^ 2 / π ^ 2) = α ^ 2 by field_simp [Real.pi_ne_zero]] at hmul
      linarith
    simp only [fourierPPrime, hα0, ↓reduceIte, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hab := mul_le_mul_of_nonneg_right (abs_sub (Real.sin α / (Real.cosh (2 * lam) - Real.cos α))
      (Real.sin α / (1 - Real.cos α))) (abs_nonneg α)
    rw [add_mul, abs_div, abs_div, abs_of_pos hden1, abs_of_pos hdenLower, div_mul_eq_mul_div, div_mul_eq_mul_div] at hab
    unfold fourierPrimeControl; linarith

private noncomputable def tauFourierTerm (lam α : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) * Real.sin (((n + 1 : ℕ) : ℝ) * α)

private noncomputable def tauAbel (lam μ α : ℝ) : ℝ :=
  ∑' n : ℕ, tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)

private noncomputable def tauAbelCorrectionTerm (lam μ α : ℝ) (n : ℕ) : ℝ :=
  (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) * Bethe.tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

private theorem summable_tauAbelCorrection {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (α : ℝ) :
    Summable (tauAbelCorrectionTerm lam μ α) := by
  refine Summable.of_norm_bounded (g := fun n => |Bethe.tauCoeff lam n| / (2 * π))
    ((Bethe.summable_tauCoeff hlam).abs.div_const _) fun n => ?_
  rw [Real.norm_eq_abs, tauAbelCorrectionTerm, abs_mul, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π)), abs_of_nonneg (by positivity)]
  have hpow : Real.exp (-μ) ^ (n + 1) ≤ 1 := pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
  have hs := Real.abs_sin_le_one (((n + 1 : ℕ) : ℝ) * α)
  calc 1 / (2 * π) * Real.exp (-μ) ^ (n + 1) * |Bethe.tauCoeff lam n| * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
      ≤ 1 / (2 * π) * 1 * |Bethe.tauCoeff lam n| * 1 := by gcongr
    _ = |Bethe.tauCoeff lam n| / (2 * π) := by ring

private theorem tauAbel_eq_sawS_add_correction {lam μ α : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) :
    tauAbel lam μ α = (1 / (2 * π) : ℝ) * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by
  let r := Real.exp (-μ)
  have hr : 0 < r := Real.exp_pos _; have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hbase : Summable fun n : ℕ => 2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => 2 * r ^ (n + 1))
      (((summable_geometric_of_lt_one hr.le hr1).mul_left (2 * r)).congr fun n => by rw [pow_succ]; ring) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_mul, abs_of_pos two_pos, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by positivity : 0 ≤ r ^ (n + 1)), abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have hs := Real.abs_sin_le_one (((n + 1 : ℕ) : ℝ) * α)
    calc 2 * 1 * r ^ (n + 1) / ((n : ℝ) + 1) * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
        ≤ 2 * 1 * r ^ (n + 1) / 1 * 1 := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) n]
      _ = 2 * r ^ (n + 1) := by ring
  have hcorr := summable_tauAbelCorrection hlam hμ α
  have hterm (n : ℕ) : tauFourierTerm lam α n * r ^ (n + 1) =
      (1 / (2 * π) : ℝ) * (2 * (-1 : ℝ) ^ (n + 1) * r ^ (n + 1) / ((n : ℝ) + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * α)) +
        tauAbelCorrectionTerm lam μ α n := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [tauFourierTerm, tauAbelCorrectionTerm]; dsimp [Bethe.tauCoeff, r]
    rw [show lam * ((n + 1 : ℕ) : ℝ) = lam * ((n : ℝ) + 1) by push_cast; ring, pow_succ (-1 : ℝ)]
    field_simp [Real.pi_ne_zero, hn]; ring
  unfold tauAbel; simp_rw [show Real.exp (-μ) = r from rfl, hterm]
  rw [(hbase.mul_left _).tsum_add hcorr, tsum_mul_left]; simp [Bethe.sawS, r]

private noncomputable def tauCoeffWeightedSum (lam : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|

private noncomputable def fourierTauProductControl (lam : ℝ) : ℝ :=
  let loc := 1 / π + (1 / (2 * π)) * tauCoeffWeightedSum lam
  let glob := 1 / 2 + (1 / 2) * tauCoeffWeightedSum lam
  max (fourierPrimeControl lam * loc) ((2 * fourierPrimeControl lam / π) * glob)

private theorem fourierTauProductControl_nonneg {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ fourierTauProductControl lam := by
  have : 0 < Real.cosh (2 * lam) - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr (by positivity))
  have : 0 ≤ tauCoeffWeightedSum lam := tsum_nonneg fun _ => by positivity
  dsimp [fourierTauProductControl, fourierPrimeControl]; positivity

private theorem fourierPPrime_mul_tauAbel_abs_bound {lam μ α : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * tauAbel lam μ α| ≤ fourierTauProductControl lam := by
  have hprime := fourierPPrime_alpha_bound hlam hα
  have : 0 < Real.cosh (2 * lam) - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr (by positivity))
  have hW : 0 ≤ tauCoeffWeightedSum lam := tsum_nonneg fun _ => by positivity
  have hprimeNN : 0 ≤ fourierPrimeControl lam := by dsimp [fourierPrimeControl]; positivity
  let loc := 1 / π + (1 / (2 * π)) * tauCoeffWeightedSum lam
  let glob := 1 / 2 + (1 / 2) * tauCoeffWeightedSum lam
  have hdecomp := tauAbel_eq_sawS_add_correction (lam := lam) (μ := μ) (α := α) hlam hμ
  let c : ℝ := 1 / (2 * π); have hc : 0 < c := by dsimp [c]; positivity
  have hcorr : |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤ c * |α| * tauCoeffWeightedSum lam := by
    have hsw : Summable fun n : ℕ => ((n : ℝ) + 1) * |Bethe.tauCoeff lam n| := by
      let r := Real.exp (-lam)
      have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]; linarith
      have hpoly : Summable fun n : ℕ => (n : ℝ) * r ^ n :=
        summable_norm_iff.mp (by simpa using summable_norm_pow_mul_geometric_of_norm_lt_one (k := 1) hrnorm)
      have hgeom : Summable fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1) := by
        simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) * r ^ n)).mpr hpoly
      refine Summable.of_norm_bounded (hgeom.mul_left 2) fun n => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [mul_le_mul_of_nonneg_left (Bethe.abs_tauCoeff_le lam n) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    have hnorm0 := (summable_tauAbelCorrection hlam hμ α).norm
    have h1 := norm_tsum_le_tsum_norm hnorm0
    simp only [Real.norm_eq_abs] at hnorm0 h1
    have hbound (n : ℕ) : |tauAbelCorrectionTerm lam μ α n| ≤ c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by
      rw [tauAbelCorrectionTerm, abs_mul, abs_mul, abs_mul, abs_of_pos hc,
        abs_of_nonneg (by positivity : 0 ≤ Real.exp (-μ) ^ (n + 1))]
      have hp : Real.exp (-μ) ^ (n + 1) ≤ 1 := pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
      have hs : |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ ((n : ℝ) + 1) * |α| :=
        Real.abs_sin_le_abs.trans_eq (by rw [abs_mul, abs_of_nonneg (by positivity)]; push_cast; rfl)
      calc c * Real.exp (-μ) ^ (n + 1) * |Bethe.tauCoeff lam n| * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
          ≤ c * 1 * |Bethe.tauCoeff lam n| * (((n : ℝ) + 1) * |α|) := by gcongr
        _ = c * |α| * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|) := by ring
    exact h1.trans ((hnorm0.tsum_le_tsum hbound (hsw.mul_left _)).trans_eq
      (by change (∑' n : ℕ, (c * |α|) * (((n : ℝ) + 1) * |Bethe.tauCoeff lam n|)) = (c * |α|) * (∑' n : ℕ, ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|); exact tsum_mul_left))
  rw [abs_mul]; unfold fourierTauProductControl
  by_cases hnear : |α| ≤ π / 2
  · have hsaw : |Bethe.sawS μ α| ≤ 2 * |α| := by
      rw [Bethe.sawS_eq_arctan hμ α, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
      have hden : 1 ≤ Real.exp μ + Real.cos α :=
        by linarith [Real.one_lt_exp_iff.mpr hμ, Real.cos_nonneg_of_mem_Icc (abs_le.mp hnear)]
      have hr : |Real.arctan (Real.sin α / (Real.exp μ + Real.cos α))| ≤ |α| :=
        Real.abs_arctan_le_abs.trans (by
          rw [abs_div, abs_of_pos (show 0 < Real.exp μ + Real.cos α by linarith)]
          exact (div_le_self (abs_nonneg _) hden).trans Real.abs_sin_le_abs)
      linarith
    have htau : |tauAbel lam μ α| ≤ loc * |α| := by
      rw [hdecomp]; refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hc]
      have h1 := mul_le_mul_of_nonneg_left hsaw hc.le
      have hid : c * (2 * |α|) + c * |α| * tauCoeffWeightedSum lam = loc * |α| := by
        dsimp [loc, c]; field_simp [Real.pi_ne_zero]
      change c * |Bethe.sawS μ α| + _ ≤ _; linarith
    have hlocNN : 0 ≤ loc := by dsimp [loc]; positivity
    calc |fourierPPrime lam α| * |tauAbel lam μ α|
        ≤ |fourierPPrime lam α| * (loc * |α|) := mul_le_mul_of_nonneg_left htau (abs_nonneg _)
      _ = loc * (|fourierPPrime lam α| * |α|) := by ring
      _ ≤ fourierPrimeControl lam * loc := by nlinarith
      _ ≤ _ := le_max_left _ _
  · have hfar : π / 2 ≤ |α| := le_of_not_ge hnear
    have hsaw : |Bethe.sawS μ α| ≤ π := by
      rw [Bethe.sawS_eq_arctan hμ α, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
      have := abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan (Real.sin α / (Real.exp μ + Real.cos α))).le,
        (Real.arctan_lt_pi_div_two _).le⟩
      linarith
    have hαabs : |α| ≤ π := abs_le.mpr ⟨by linarith [hα.1], hα.2⟩
    have htau : |tauAbel lam μ α| ≤ glob := by
      rw [hdecomp]; refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hc]
      have h1 := mul_le_mul_of_nonneg_left hsaw hc.le
      have h2 : c * |α| * tauCoeffWeightedSum lam ≤ c * π * tauCoeffWeightedSum lam := by gcongr
      have hid : c * π + c * π * tauCoeffWeightedSum lam = glob := by dsimp [glob, c]; field_simp [Real.pi_ne_zero]
      change c * |Bethe.sawS μ α| + _ ≤ _; linarith
    have hαpos : 0 < |α| := lt_of_lt_of_le (by positivity) hfar
    have hprimeFar : |fourierPPrime lam α| ≤ 2 * fourierPrimeControl lam / π :=
      ((le_div_iff₀ hαpos).2 (by linarith)).trans
        ((div_le_div_of_nonneg_left hprimeNN (by positivity) hfar).trans_eq (by field_simp [Real.pi_ne_zero]))
    exact (mul_le_mul hprimeFar htau (abs_nonneg _) (by positivity)).trans (le_max_right _ _)

private theorem abel_seq_tendsto {f : ℕ → ℝ} {L : ℝ}
    (hpart : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ∑' n : ℕ, f n * Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)) atTop (𝓝 L) := by
  let r (N : ℕ) := Real.exp (-(1 / ((N : ℝ) + 1)))
  have hsm : Tendsto (fun N : ℕ => -(1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hr0 : Tendsto r atTop (𝓝 1) := by
    simpa only [r, Function.comp_def, Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp hsm
  have hr : Tendsto r atTop (𝓝[<] 1) := tendsto_nhdsWithin_iff.mpr
    ⟨hr0, Filter.Eventually.of_forall fun N => Real.exp_lt_one_iff.mpr (by linarith [show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity])⟩
  have hmul : Tendsto (fun N => r N * ∑' n : ℕ, f n * r N ^ n) atTop (𝓝 (1 * L)) :=
    hr0.mul ((Real.tendsto_tsum_powerSeries_nhdsWithin_lt hpart).comp hr)
  rw [one_mul] at hmul
  refine hmul.congr fun N => ?_
  rw [← tsum_mul_left]; exact tsum_congr fun n => by dsimp [r]; rw [pow_succ]; ring

private theorem tauAbelSeq_tendsto_tauSeries {lam α : ℝ} (hlam : 0 < lam) (hα : |α| < π) :
    Tendsto (fun N : ℕ => tauAbel lam (1 / ((N : ℝ) + 1)) α) atTop (𝓝 (Bethe.tauSeries lam α)) := by
  have hp := Bethe.tendsto_tauPartial hlam hα
  rw [← Bethe.tauSeries_eq hlam hα] at hp
  exact abel_seq_tendsto (hp.congr fun N => by simp [tauFourierTerm, Bethe.tauPartial])

private theorem measurable_fourierPPrime (lam : ℝ) : Measurable (fourierPPrime lam) := by
  unfold fourierPPrime; exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private theorem fourierPPrime_tauSeries_abs_bound {lam α : ℝ} (hlam : 0 < lam) (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * Bethe.tauSeries lam α| ≤ fourierTauProductControl lam := by
  by_cases hαp : α = π
  · subst hαp; simp [Bethe.tauSeries_pi, fourierTauProductControl_nonneg hlam]
  by_cases hαm : α = -π
  · subst hαm; simp [Bethe.tauSeries_neg_pi, fourierTauProductControl_nonneg hlam]
  have hαabs : |α| < π := abs_lt.mpr ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩
  have hprod : Tendsto (fun N : ℕ => |fourierPPrime lam α * tauAbel lam (1 / ((N : ℝ) + 1)) α|) atTop
      (𝓝 |fourierPPrime lam α * Bethe.tauSeries lam α|) := by
    simpa only [Real.norm_eq_abs] using (tendsto_const_nhds.mul (tauAbelSeq_tendsto_tauSeries hlam hαabs)).norm
  exact le_of_tendsto hprod (Filter.Eventually.of_forall fun N =>
    fourierPPrime_mul_tauAbel_abs_bound hlam (by positivity) hα)

private theorem fourierPPrime_tauSeries_integral {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (logCoshTauCorrectionPartial lam) atTop
        (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
  obtain ⟨S, hS, hId⟩ := identity43 lam hlam
  let corrTerm (n : ℕ) : ℝ := (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
    (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1)
  have hpeq (N : ℕ) : (∑ n ∈ Finset.range N, corrTerm n) = logCoshTauCorrectionPartial lam N := by
    unfold logCoshTauCorrectionPartial; rw [sum_Icc_one_eq_sum_range]
    exact Finset.sum_congr rfl fun n _ => by dsimp [corrTerm]; push_cast; ring_nf
  have hCorr : Tendsto (logCoshTauCorrectionPartial lam) atTop (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) :=
    ((tendsto_const_nhds (x := Real.log (Real.cosh lam))).sub hId).congr fun _ => by ring
  have hAbel := abel_seq_tendsto (hCorr.congr fun N => (hpeq N).symm)
  have hcontAbel {μ : ℝ} (hμ : 0 < μ) : Continuous (tauAbel lam μ) := by
    let coeff (n : ℕ) : ℝ := (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) * Bethe.tauCoeff lam n
    have hsc : Summable coeff := Summable.of_norm_bounded ((Bethe.summable_tauCoeff hlam).abs.mul_left (1 / (2 * π))) fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π)),
        abs_of_nonneg (by positivity : 0 ≤ Real.exp (-μ) ^ (n + 1))]
      have hp : Real.exp (-μ) ^ (n + 1) ≤ 1 := pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
      calc 1 / (2 * π) * Real.exp (-μ) ^ (n + 1) * |Bethe.tauCoeff lam n|
          ≤ 1 / (2 * π) * 1 * |Bethe.tauCoeff lam n| := by gcongr
        _ = 1 / (2 * π) * |Bethe.tauCoeff lam n| := by ring
    have heq : tauAbel lam μ = fun α => (1 / (2 * π) : ℝ) * Bethe.sawS μ α + Bethe.trigSeries 0 (fun _ => 0) coeff α :=
      funext fun α => (tauAbel_eq_sawS_add_correction hlam hμ).trans (by simp [Bethe.trigSeries, tauAbelCorrectionTerm, coeff])
    rw [heq]
    exact (continuous_const.mul (continuous_iff_continuousAt.mpr fun α => (Bethe.hasDerivAt_sawS hμ α).continuousAt)).add
      (Bethe.continuous_trigSeries summable_zero hsc 0)
  have htauTerm_bd (α : ℝ) (n : ℕ) : |tauFourierTerm lam α n| ≤ |α| / π := by
    have hm : 0 < (n : ℝ) + 1 := by positivity
    have hs : |Real.sin (((n + 1 : ℕ) : ℝ) * α)| ≤ ((n : ℝ) + 1) * |α| :=
      Real.abs_sin_le_abs.trans_eq (by rw [abs_mul, abs_of_nonneg (by positivity)]; push_cast; rfl)
    rw [tauFourierTerm, abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (mul_pos Real.pi_pos hm)]
    calc 1 / (π * ((n : ℝ) + 1)) * |Real.tanh (lam * ((n + 1 : ℕ) : ℝ))| * |Real.sin (((n + 1 : ℕ) : ℝ) * α)|
        ≤ 1 / (π * ((n : ℝ) + 1)) * 1 * (((n : ℝ) + 1) * |α|) := by gcongr; exact (Real.abs_tanh_lt_one _).le
      _ = |α| / π := by field_simp [Real.pi_ne_zero]
  have hAbelInt {μ : ℝ} (hμ : 0 < μ) :
      ∫ α in (-π)..π, fourierPPrime lam α * tauAbel lam μ α = ∑' n : ℕ, corrTerm n * Real.exp (-μ) ^ (n + 1) := by
    let r := Real.exp (-μ)
    have hr : 0 < r := Real.exp_pos _; have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    let B (n : ℕ) := (fourierPrimeControl lam / π) * r ^ (n + 1)
    let G (n : ℕ) (α : ℝ) := fourierPPrime lam α * tauFourierTerm lam α n * r ^ (n + 1)
    have hgeo : Summable fun n : ℕ => r ^ (n + 1) :=
      ((summable_geometric_of_lt_one hr.le hr1).mul_left r).congr fun n => by rw [pow_succ]; ring
    have hmeas (n : ℕ) : AEStronglyMeasurable (G n) (volume.restrict (uIoc (-π) π)) :=
      (((measurable_fourierPPrime lam).mul (by unfold tauFourierTerm; fun_prop)).mul measurable_const).aestronglyMeasurable
    have hbound (n : ℕ) : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π → ‖G n α‖ ≤ B n := Filter.Eventually.of_forall fun α hα => by
      have hIcc : α ∈ Icc (-π) π := Ioc_subset_Icc_self (by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα)
      have h1 := mul_le_mul_of_nonneg_left (htauTerm_bd α n) (abs_nonneg (fourierPPrime lam α))
      have h2 : |fourierPPrime lam α| * (|α| / π) ≤ fourierPrimeControl lam / π := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (fourierPPrime_alpha_bound hlam hIcc) Real.pi_pos.le
      change ‖fourierPPrime lam α * tauFourierTerm lam α n * r ^ (n + 1)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr.le (n + 1))]
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (pow_nonneg hr.le (n + 1))
    have hlim : ∀ᵐ α ∂volume, α ∈ uIoc (-π) π → HasSum (fun n => G n α) (fourierPPrime lam α * tauAbel lam μ α) :=
      Filter.Eventually.of_forall fun α _ => by
        have hs : Summable fun n => tauFourierTerm lam α n * r ^ (n + 1) :=
          Summable.of_norm_bounded (hgeo.mul_left (|α| / π)) fun n => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.le (n + 1))]
            exact mul_le_mul_of_nonneg_right (htauTerm_bd α n) (pow_nonneg hr.le (n + 1))
        exact (hs.hasSum.mul_left (fourierPPrime lam α)).congr_fun fun n => by dsimp [G, r]; ring
    have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => B n) hmeas hbound
      (Filter.Eventually.of_forall fun _ _ => hgeo.mul_left _) intervalIntegrable_const hlim
    rw [← hsum.tsum_eq]
    refine tsum_congr fun n => ?_
    have hfun : G n = fun α => (r ^ (n + 1) * ((-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) * Real.tanh (lam * ((n + 1 : ℕ) : ℝ)))) *
        (fourierPPrime lam α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) := funext fun _ => by dsimp [G, tauFourierTerm]; ring
    rw [hfun, intervalIntegral.integral_const_mul, fourierP_prime_sine_integral hlam n]
    dsimp [corrTerm, r]; have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [Real.pi_ne_zero]
  let F (N : ℕ) (α : ℝ) := fourierPPrime lam α * tauAbel lam (1 / ((N : ℝ) + 1)) α
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
    (fun _ => fourierTauProductControl lam)
    (Filter.Eventually.of_forall fun N =>
      ((measurable_fourierPPrime lam).mul (hcontAbel (by positivity)).measurable).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun N => Filter.Eventually.of_forall fun α (hα : α ∈ uIoc (-π) π) => by
      have hio : α ∈ Ioc (-π) π := by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
      rw [Real.norm_eq_abs]; exact fourierPPrime_mul_tauAbel_abs_bound hlam (by positivity) (Ioc_subset_Icc_self hio))
    intervalIntegrable_const
    (by filter_upwards [Measure.ae_ne volume π] with α hαπ (hα : α ∈ uIoc (-π) π)
        have hio : α ∈ Ioc (-π) π := by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
        exact tendsto_const_nhds.mul (tauAbelSeq_tendsto_tauSeries hlam
          (abs_lt.mpr ⟨by linarith [hio.1], lt_of_le_of_ne hio.2 hαπ⟩)))
  have hDCT' := hDCT.congr fun N => hAbelInt (by positivity)
  rw [← tendsto_nhds_unique hDCT' hAbel] at hCorr
  exact ⟨S, hS, hCorr⟩

/-! ### 3. Source-Coordinate Pullback and Eigenvalue-Ratio Exponent -/

noncomputable def fourierEll (lam x : ℝ) : ℝ := fourierP lam (Bethe.kInv lam x)

noncomputable def fourierEllPrime (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else fourierPPrime lam (Bethe.kInv lam x) / Bethe.Xi lam (Bethe.kInv lam x)

private theorem kInv_mem_Ioo {lam x : ℝ} (hlam : 0 < lam) (hx : x ∈ Ioo (-π) π) : Bethe.kInv lam x ∈ Ioo (-π) π := by
  have hIcc := Bethe.kInv_mem_Icc hlam (Ioo_subset_Icc_self hx)
  refine ⟨lt_of_le_of_ne hIcc.1 fun h => ?_, lt_of_le_of_ne hIcc.2 fun h => ?_⟩
  · have hx' := Bethe.kMap_kInv hlam x; rw [← h, Bethe.kMap_neg_pi] at hx'; linarith [hx.1]
  · have hx' := Bethe.kMap_kInv hlam x; rw [h, Bethe.kMap_pi] at hx'; linarith [hx.2]

private theorem kInv_ne_zero {lam x : ℝ} (hlam : 0 < lam) (hx : x ≠ 0) : Bethe.kInv lam x ≠ 0 := fun h => by
  have := Bethe.kMap_kInv hlam x; rw [h, Bethe.kMap_zero] at this; exact hx this.symm

private theorem cos_lt_one_of_Ioo {α : ℝ} (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) : Real.cos α < 1 :=
  lt_of_le_of_ne (Real.cos_le_one α) fun h => hα0 <| by
    have hp := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hα.1]) (by linarith [Real.pi_pos, hα.2])).mp h
    omega

theorem fourierEll_hasDerivAt {lam x : ℝ} (hlam : 0 < lam)
    (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    HasDerivAt (fourierEll lam) (fourierEllPrime lam x) x := by
  let α := Bethe.kInv lam x
  have hki := (Bethe.analyticAt_kInv hlam x).differentiableAt.hasDerivAt
  have hc := (Bethe.hasDerivAt_kMap hlam α).comp x hki
  change HasDerivAt (fun y : ℝ => Bethe.kMap lam (Bethe.kInv lam y)) (Bethe.Xi lam α * deriv (Bethe.kInv lam) x) x at hc
  rw [funext (Bethe.kMap_kInv hlam)] at hc
  have hprod : Bethe.Xi lam α * deriv (Bethe.kInv lam) x = 1 := by simpa using hc.deriv.symm
  have hXi : Bethe.Xi lam α ≠ 0 := (Bethe.Xi_pos hlam α).ne'
  have hki' : HasDerivAt (Bethe.kInv lam) (Bethe.Xi lam α)⁻¹ x :=
    hki.congr_deriv (by apply mul_left_cancel₀ hXi; rw [hprod, mul_inv_cancel₀ hXi])
  change HasDerivAt (fourierP lam ∘ Bethe.kInv lam) (fourierEllPrime lam x) x
  exact ((fourierP_hasDerivAt hlam (kInv_mem_Ioo hlam hx) (kInv_ne_zero hlam hx0)).comp x hki').congr_deriv
    (by simp [fourierEllPrime, hx0, α, div_eq_mul_inv])

theorem fourierEll_eq_log_norm {lam c x : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) :
    fourierEll lam x = Real.log ‖BetheAnsatz.M c (Complex.exp (I * (x : ℂ)))‖ := by
  rw [fourierEll, fourierP_eq_log_norm hlam hc (cos_lt_one_of_Ioo (kInv_mem_Ioo hlam hx) (kInv_ne_zero hlam hx0)),
    Bethe.kMap_kInv hlam]

/-- The analytic exponent in the eigenvalue-ratio formula (`Δ = -cosh λ`). -/
theorem fourierRatioExponent {lam r : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      -r * Real.log (abs (-Real.cosh lam)) +
          r * (∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =
        -r * (lam + 2 * S) := by
  let tauACont (α : ℝ) := Bethe.TcontFn lam α / (2 * π)
  let tauXCont (x : ℝ) := tauACont (Bethe.kInv lam x)
  let ellTauCont (x : ℝ) := fourierEllPrime lam x * tauXCont x
  let q (α : ℝ) := ellTauCont (Bethe.kMap lam α) * Bethe.Xi lam α
  have hcontA : Continuous tauACont := (Bethe.continuous_TcontFn hlam).div_const _
  have hcontX : Continuous tauXCont := hcontA.comp (Bethe.continuous_kInv hlam)
  have hcontAt {x : ℝ} (hx : x ∈ Ioo (-π) π) (hx0 : x ≠ 0) : ContinuousAt ellTauCont x := by
    have hα := kInv_mem_Ioo hlam hx; have hα0 := kInv_ne_zero hlam hx0
    have hcos := cos_lt_one_of_Ioo hα hα0
    have hd1 : Real.cosh (2 * lam) - Real.cos (Bethe.kInv lam x) ≠ 0 := by linarith [Real.one_le_cosh (2 * lam)]
    have hd2 : 1 - Real.cos (Bethe.kInv lam x) ≠ 0 := by linarith
    have hP : ContinuousAt (fourierPPrime lam) (Bethe.kInv lam x) :=
      ((continuousAt_const (y := (1 / 2 : ℝ))).mul ((Real.continuous_sin.continuousAt.div (continuousAt_const.sub Real.continuous_cos.continuousAt) hd1).sub
        (Real.continuous_sin.continuousAt.div (continuousAt_const.sub Real.continuous_cos.continuousAt) hd2))).congr
        (by filter_upwards [eventually_ne_nhds hα0] with y hy; simp [fourierPPrime, hy])
    have hE : ContinuousAt (fourierEllPrime lam) x :=
      ((hP.comp (Bethe.continuous_kInv hlam).continuousAt).div
        ((Bethe.continuous_Xi hlam).continuousAt.comp (Bethe.continuous_kInv hlam).continuousAt) (Bethe.Xi_pos hlam _).ne').congr
        (by filter_upwards [eventually_ne_nhds hx0] with y hy; simp [fourierEllPrime, hy])
    exact hE.mul hcontX.continuousAt
  have hqf : q =ᵐ[volume.restrict (Icc (-π) π)] fun α => fourierPPrime lam α * Bethe.tauSeries lam α := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (Measure.ae_ne volume π),
      ae_restrict_of_ae (Measure.ae_ne volume (-π)), ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hαp hαm hα0
    have hαoo : α ∈ Ioo (-π) π := ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩
    have hk0 : Bethe.kMap lam α ≠ 0 := fun h => hα0 ((Bethe.strictMono_kMap hlam).injective (by rwa [Bethe.kMap_zero]))
    dsimp [q, ellTauCont, tauXCont, tauACont]; unfold fourierEllPrime
    rw [ite_eq_right hk0, Bethe.kInv_kMap hlam, ← Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hαoo.1, hαoo.2⟩)]
    field_simp [(Bethe.Xi_pos hlam α).ne']
  have hfInt : IntegrableOn (fun α => fourierPPrime lam α * Bethe.tauSeries lam α) (Icc (-π) π) volume := by
    have hae : (fun α => fourierPPrime lam α * tauACont α) =ᵐ[volume.restrict (Icc (-π) π)]
        fun α => fourierPPrime lam α * Bethe.tauSeries lam α := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (Measure.ae_ne volume π),
        ae_restrict_of_ae (Measure.ae_ne volume (-π))] with α hα hαp hαm
      rw [Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩)]
    refine (Measure.integrableOn_of_bounded (f := fun α => fourierPPrime lam α * tauACont α)
      (M := fourierTauProductControl lam) (by simp)
      ((measurable_fourierPPrime lam).mul hcontA.measurable).aestronglyMeasurable ?_).congr_fun_ae hae
    filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with α h1 hα
    rw [h1, Real.norm_eq_abs]; exact fourierPPrime_tauSeries_abs_bound hlam hα
  have hqInt : IntegrableOn q (Icc (-π) π) volume := hfInt.congr_fun_ae hqf.symm
  let xiLow := Real.sinh lam / (Real.cosh lam + 1)
  have hxiLow : 0 < xiLow := div_pos (Real.sinh_pos_iff.mpr hlam) (by positivity)
  have hgInt : IntegrableOn ellTauCont (Icc (-π) π) volume := by
    have hm : Measurable ellTauCont :=
      (Measurable.ite (measurableSet_singleton 0) (measurable_const (a := (0 : ℝ)))
        (((measurable_fourierPPrime lam).comp (Bethe.continuous_kInv hlam).measurable).div
          ((Bethe.continuous_Xi hlam).comp (Bethe.continuous_kInv hlam)).measurable)).mul hcontX.measurable
    refine Measure.integrableOn_of_bounded (M := fourierTauProductControl lam / xiLow) (by simp) hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (Measure.ae_ne volume π),
      ae_restrict_of_ae (Measure.ae_ne volume (-π))] with x hx hxp hxm
    rw [Real.norm_eq_abs]
    by_cases hx0 : x = 0
    · subst hx0; simp [ellTauCont, fourierEllPrime]
      exact div_nonneg (fourierTauProductControl_nonneg hlam) hxiLow.le
    · have hα := kInv_mem_Ioo hlam ⟨lt_of_le_of_ne hx.1 (Ne.symm hxm), lt_of_le_of_ne hx.2 hxp⟩
      have hxiPos := Bethe.Xi_pos hlam (Bethe.kInv lam x)
      have hrew : ellTauCont x =
          (fourierPPrime lam (Bethe.kInv lam x) * Bethe.tauSeries lam (Bethe.kInv lam x)) / Bethe.Xi lam (Bethe.kInv lam x) := by
        simp [ellTauCont, fourierEllPrime, tauXCont, tauACont, hx0,
          ← Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨hα.1, hα.2⟩), div_mul_eq_mul_div]
      rw [hrew, abs_div, abs_of_pos hxiPos]
      exact (div_le_div_of_nonneg_right (fourierPPrime_tauSeries_abs_bound hlam (Ioo_subset_Icc_self hα)) hxiPos.le).trans
        (div_le_div_of_nonneg_left (fourierTauProductControl_nonneg hlam) hxiLow (Bethe.Xi_bounds hlam _).1)
  have hsub {a b : ℝ} (hab : a ≤ b) (ha : -π ≤ a) (hb : b ≤ π) (h0 : ∀ α ∈ Ioo a b, α ≠ 0) :
      ∫ α in a..b, q α = ∫ x in Bethe.kMap lam a..Bethe.kMap lam b, ellTauCont x := by
    have hsubIcc : Icc a b ⊆ Icc (-π) π := fun α hα => ⟨ha.trans hα.1, hα.2.trans hb⟩
    refine intervalIntegral.integral_comp_mul_deriv'''
      (f := Bethe.kMap lam) (f' := Bethe.Xi lam) (g := ellTauCont)
      (Bethe.continuous_kMap hlam).continuousOn
      (fun α _ => (Bethe.hasDerivAt_kMap hlam α).hasDerivWithinAt)
      (fun x ⟨α, hα, hx⟩ => ?_)
      (by rw [uIcc_of_le hab]; exact hgInt.mono_set fun x ⟨α, hα, hx⟩ => hx ▸ Bethe.mapsTo_kMap hlam (hsubIcc hα))
      (by rw [uIcc_of_le hab]; exact hqInt.mono_set hsubIcc)
    subst hx
    have hαab : α ∈ Ioo a b := by simpa [min_eq_left hab, max_eq_right hab] using hα
    have hαfull : α ∈ Ioo (-π) π := ⟨lt_of_le_of_lt ha hαab.1, lt_of_lt_of_le hαab.2 hb⟩
    have hinj := (Bethe.strictMono_kMap hlam).injective
    have hxIoo : Bethe.kMap lam α ∈ Ioo (-π) π :=
      ⟨lt_of_le_of_ne (Bethe.mapsTo_kMap hlam (Ioo_subset_Icc_self hαfull)).1 fun h => by
          have := hinj (h.symm.trans (Bethe.kMap_neg_pi lam).symm); linarith [hαfull.1],
       lt_of_le_of_ne (Bethe.mapsTo_kMap hlam (Ioo_subset_Icc_self hαfull)).2 fun h => by
          have := hinj (h.trans (Bethe.kMap_pi lam).symm); linarith [hαfull.2]⟩
    exact (hcontAt hxIoo fun hx0 => h0 α hαab (hinj (by rwa [Bethe.kMap_zero]))).continuousWithinAt
  have hsubL := hsub (neg_nonpos.mpr Real.pi_pos.le) le_rfl Real.pi_pos.le (fun _ h => h.2.ne)
  have hsubR := hsub Real.pi_pos.le (neg_nonpos.mpr Real.pi_pos.le) le_rfl (fun _ h => h.1.ne')
  rw [Bethe.kMap_neg_pi, Bethe.kMap_zero] at hsubL
  rw [Bethe.kMap_zero, Bethe.kMap_pi] at hsubR
  have hII {f : ℝ → ℝ} (hf : IntegrableOn f (Icc (-π) π) volume) {a b : ℝ} (hab : a ≤ b) (ha : -π ≤ a) (hb : b ≤ π) :
      IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hf.mono_set fun x hx => ⟨ha.trans hx.1.le, hx.2.trans hb⟩
  have hsrcAE : (fun x => fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x) =ᵐ[volume.restrict (uIoc (-π) π)]
      ellTauCont := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (Measure.ae_ne volume π)] with x hx hxp
    have hio : x ∈ Ioc (-π) π := by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hx
    have hparam : Bethe.lamOf (-Real.cosh lam) = lam := (Bethe.eq_lamOf hlam (by simp)).symm
    change fourierEllPrime lam x * Bethe.tauSeries (Bethe.lamOf (-Real.cosh lam)) (Bethe.kInv (Bethe.lamOf (-Real.cosh lam)) x) = _
    rw [hparam, Bethe.tauSeries_eq hlam (abs_lt.mpr ⟨(kInv_mem_Ioo hlam ⟨hio.1, lt_of_le_of_ne hio.2 hxp⟩).1,
      (kInv_mem_Ioo hlam ⟨hio.1, lt_of_le_of_ne hio.2 hxp⟩).2⟩)]
  have hqAE : q =ᵐ[volume.restrict (uIoc (-π) π)] fun α => fourierPPrime lam α * Bethe.tauSeries lam α := by
    rw [uIoc_of_le (neg_le_self Real.pi_nonneg)]; exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hqf
  have hIntEq : ∫ x in (-π)..π, fourierEllPrime lam x * Bethe.tau (-Real.cosh lam) x =
      ∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α := by
    rw [intervalIntegral.integral_congr_ae_restrict hsrcAE,
      ← intervalIntegral.integral_add_adjacent_intervals (hII hgInt (by linarith [Real.pi_pos]) le_rfl (by linarith [Real.pi_pos]))
        (hII hgInt Real.pi_pos.le (by linarith [Real.pi_pos]) le_rfl),
      ← hsubL, ← hsubR,
      intervalIntegral.integral_add_adjacent_intervals (hII hqInt (by linarith [Real.pi_pos]) le_rfl (by linarith [Real.pi_pos]))
        (hII hqInt Real.pi_pos.le (by linarith [Real.pi_pos]) le_rfl),
      intervalIntegral.integral_congr_ae_restrict hqAE]
  obtain ⟨S, hS, hCorr⟩ := fourierPPrime_tauSeries_integral hlam
  obtain ⟨S', hS', hId⟩ := identity43 lam hlam
  have hSS' : S = S' := tendsto_nhds_unique hS hS'
  have hEq := tendsto_nhds_unique (tendsto_const_nhds.sub hCorr) hId
  rw [← hSS', ← hIntEq] at hEq
  refine ⟨S, hS, ?_⟩
  rw [abs_neg, abs_of_pos (Real.cosh_pos lam)]
  linear_combination -r * hEq

end PottsDiscontinuity
