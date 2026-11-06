module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Bethe.Prop21Coeff
public import PottsDiscontinuity.Bethe.RatioProducts

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

noncomputable def fourierP (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) * Real.log
      ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α))

private theorem exp_I_mul_kMap_fraction {lam α : ℝ} (hlam : 0 < lam) :
    Complex.exp (I * (Bethe.kMap lam α : ℂ)) =
      (Complex.exp (I * (α : ℂ)) * (Real.exp lam : ℂ) - 1) /
        ((Real.exp lam : ℂ) - Complex.exp (I * (α : ℂ))) := by
  rw [Bethe.exp_I_mul_kMap_aux hlam α, Complex.exp_neg]
  have hw : Complex.exp (I * (α : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp [hw]

theorem normSq_M_kMap_eq_ratio {lam c α : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1) :
    Complex.normSq (BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))) =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
  let E : ℂ := (Real.exp lam : ℂ)
  let w : ℂ := Complex.exp (I * (α : ℂ))
  have hEreal : 1 < Real.exp lam := by simpa using hlam
  have hEw : E - w ≠ 0 := Bethe.ofReal_sub_ne_zero hEreal (by simp [w])
  have h1w : 1 - w ≠ 0 := fun h => by
    have hre := congrArg Complex.re (sub_eq_zero.mp h).symm
    change (Complex.exp (I * (α : ℂ))).re = 1 at hre
    rw [Bethe.exp_I_mul_ofReal] at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
    linarith
  have hEpos : Real.exp lam ≠ 0 := (Real.exp_pos lam).ne'
  have hcsq : (c : ℂ) ^ 2 = (E + 1) ^ 2 / E := by
    have hreal : c ^ 2 = (Real.exp lam + 1) ^ 2 / Real.exp lam := by
      rw [hc, Real.cosh_eq, Real.exp_neg]; field_simp [hEpos]; ring
    simpa [E] using congrArg (fun x : ℝ => (x : ℂ)) hreal
  have hz : Complex.exp (I * (Bethe.kMap lam α : ℂ)) = (w * E - 1) / (E - w) := by
    simpa [w, E, mul_comm] using exp_I_mul_kMap_fraction hlam
  have hden : 1 - Complex.exp (I * (Bethe.kMap lam α : ℂ)) =
      (E + 1) * (1 - w) / (E - w) := by
    rw [hz]; field_simp [hEw]; ring
  have hM : BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ))) =
      (w - E ^ 2) / (E * (1 - w)) := by
    rw [BetheAnsatz.M, hden, hcsq]
    have hEc : E ≠ 0 := by change (Real.exp lam : ℂ) ≠ 0; exact_mod_cast hEpos
    field_simp [hEw, h1w, hEc]; ring
  rw [hM]
  have hwRe : w.re = Real.cos α := by
    simp only [w, Bethe.exp_I_mul_ofReal, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hwIm : w.im = Real.sin α := by
    simp only [w, Bethe.exp_I_mul_ofReal, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero, zero_add]
  have hnum : Complex.normSq (w - E ^ 2) =
      Real.exp lam ^ 4 - 2 * Real.exp lam ^ 2 * Real.cos α + 1 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm]
    simp only [E, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h1wSq : Complex.normSq (1 - w) = 2 - 2 * Real.cos α := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm]
    simp; nlinarith [Real.sin_sq_add_cos_sq α]
  have hdenSq : Complex.normSq (E * (1 - w)) =
      Real.exp lam ^ 2 * (2 - 2 * Real.cos α) := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, h1wSq]; ring
  rw [Complex.normSq_div, hnum, hdenSq]
  have hdiv : Real.exp lam ^ 2 * (2 - 2 * Real.cos α) ≠ 0 :=
    mul_ne_zero (by positivity) (by linarith)
  have hcosh : Real.cosh (2 * lam) =
      (Real.exp lam ^ 2 + (Real.exp lam ^ 2)⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, show 2 * lam = lam + lam by ring, Real.exp_add]
    ring
  rw [hcosh]
  field_simp [hdiv, hEpos]
  ring

theorem fourierP_eq_log_norm {lam c α : ℝ} (hlam : 0 < lam)
    (hc : c ^ 2 = 2 + 2 * Real.cosh lam) (hcos : Real.cos α < 1) :
    fourierP lam α = Real.log
      ‖BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))‖ := by
  let z : ℂ := BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α : ℂ)))
  have hα : α ≠ 0 := by rintro rfl; norm_num at hcos
  have hnormSq : ‖z‖ ^ 2 =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_M_kMap_eq_ratio hlam hc hcos
  unfold fourierP
  rw [ite_eq_right hα, ← hnormSq, Real.log_pow]
  ring

theorem fourier_one_sub_cos_lower {α : ℝ} (hα : α ∈ Icc (-π) π) :
    2 * α ^ 2 / π ^ 2 ≤ 1 - Real.cos α := by
  have hx : |α / 2| ≤ π / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_le.mpr ⟨by linarith [hα.1], hα.2⟩]
  have hj := (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 (Real.mul_abs_le_abs_sin hx)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), sq_abs] at hj
  have hsin := Real.sin_sq_eq_half_sub (α / 2)
  rw [show 2 * (α / 2) = α by ring] at hsin
  calc
    2 * α ^ 2 / π ^ 2 = 2 * (2 / π * (|α| / 2)) ^ 2 := by
      field_simp [Real.pi_ne_zero]; rw [sq_abs]
    _ ≤ 2 * Real.sin (α / 2) ^ 2 := mul_le_mul_of_nonneg_left hj zero_le_two
    _ = 1 - Real.cos α := by rw [hsin]; ring

noncomputable def fourierPPrime (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2 : ℝ) *
      (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
        Real.sin α / (1 - Real.cos α))

theorem fourierP_hasDerivAt {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    HasDerivAt (fourierP lam) (fourierPPrime lam α) α := by
  have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
  have hden : 0 < 1 - Real.cos α :=
    lt_of_lt_of_le (by positivity) (fourier_one_sub_cos_lower (Ioo_subset_Icc_self hα))
  have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
  have hnum : 0 < Real.cosh (2 * lam) - Real.cos α := by linarith [Real.cos_le_one α]
  have hu : HasDerivAt (fun x => Real.cosh (2 * lam) - Real.cos x) (Real.sin α) α := by
    simpa using (Real.hasDerivAt_cos α).const_sub (Real.cosh (2 * lam))
  have hv : HasDerivAt (fun x => 1 - Real.cos x) (Real.sin α) α := by
    simpa using (Real.hasDerivAt_cos α).const_sub (1 : ℝ)
  have hraw := ((hu.div hv hden.ne').log (div_ne_zero hnum.ne' hden.ne')).const_mul (1 / 2 : ℝ)
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [fourierPPrime, hα0]; field_simp [hden.ne', hnum.ne']
  · filter_upwards [eventually_ne_nhds hα0] with x hx
    simp [fourierP, hx]

noncomputable def fourierCotSin (n : ℕ) (α : ℝ) : ℝ :=
  if α = 0 then 0 else
    Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) / (1 - Real.cos α)

private theorem fourier_sin_recurrence (n : ℕ) (α : ℝ) :
    Real.sin α *
        (Real.sin (((n + 2 : ℕ) : ℝ) * α) -
          Real.sin (((n + 1 : ℕ) : ℝ) * α)) =
      (1 - Real.cos α) *
        (Real.cos (((n + 2 : ℕ) : ℝ) * α) +
          Real.cos (((n + 1 : ℕ) : ℝ) * α)) := by
  rw [show (((n + 2 : ℕ) : ℝ) * α) = (((n + 1 : ℕ) : ℝ) * α) + α by push_cast; ring,
    Real.sin_add, Real.cos_add]
  have hsq := Real.sin_sq_add_cos_sq α
  nlinarith [hsq, congrArg (fun y : ℝ => Real.cos (((n + 1 : ℕ) : ℝ) * α) * y) hsq]

private theorem fourierCotSin_succ_ae (n : ℕ) :
    (fun α => fourierCotSin (n + 1) α) =ᵐ[volume.restrict (uIoc (-π) π)]
      (fun α => fourierCotSin n α +
        Real.cos (((n + 2 : ℕ) : ℝ) * α) +
        Real.cos (((n + 1 : ℕ) : ℝ) * α)) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
  have hαio : α ∈ Ioc (-π) π := by
    simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
  have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
  have hden : 0 < 1 - Real.cos α :=
    lt_of_lt_of_le (by positivity) (fourier_one_sub_cos_lower (Ioc_subset_Icc_self hαio))
  have hrec := fourier_sin_recurrence n α
  simp [fourierCotSin, hα0]
  push_cast at hrec ⊢
  rw [show (↑n + 1 + 1) * α = (↑n + 2) * α by ring]
  rw [← show α * (↑n + 1) = (↑n + 1) * α by ring] at hrec
  field_simp [hden.ne']
  nlinarith [hrec]

private theorem fourierCotSin_integrable_integral (n : ℕ) :
    IntervalIntegrable (fun α => fourierCotSin n α) volume (-π) π ∧
      ∫ α in (-π)..π, fourierCotSin n α = 2 * π := by
  induction n with
  | zero =>
      have hEq : (fun α => fourierCotSin 0 α) =ᵐ[volume.restrict (uIoc (-π) π)]
          (fun α => 1 + Real.cos α) := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc,
          ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
        have hαio : α ∈ Ioc (-π) π := by
          simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
        have hαsq : 0 < α ^ 2 := sq_pos_of_ne_zero hα0
        have hden : 0 < 1 - Real.cos α :=
          lt_of_lt_of_le (by positivity) (fourier_one_sub_cos_lower (Ioc_subset_Icc_self hαio))
        simp [fourierCotSin, hα0]
        field_simp [hden.ne']
        nlinarith [Real.sin_sq_add_cos_sq α]
      have hcosInt : IntervalIntegrable (fun α : ℝ => 1 + Real.cos α) volume (-π) π :=
        (by fun_prop : Continuous fun α : ℝ => 1 + Real.cos α).intervalIntegrable _ _
      refine ⟨(intervalIntegrable_congr_ae hEq).mpr hcosInt, ?_⟩
      rw [intervalIntegral.integral_congr_ae_restrict hEq,
        intervalIntegral.integral_add intervalIntegrable_const
          (Real.continuous_cos.intervalIntegrable _ _),
        intervalIntegral.integral_const]
      simp; ring
  | succ n ih =>
      have hEq := fourierCotSin_succ_ae n
      have hcosInt1 : IntervalIntegrable
          (fun α : ℝ => Real.cos (((n + 2 : ℕ) : ℝ) * α)) volume (-π) π :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      have hcosInt2 : IntervalIntegrable
          (fun α : ℝ => Real.cos (((n + 1 : ℕ) : ℝ) * α)) volume (-π) π :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      refine ⟨((ih.1.add hcosInt1).add hcosInt2).congr_ae hEq.symm, ?_⟩
      rw [intervalIntegral.integral_congr_ae_restrict hEq,
        intervalIntegral.integral_add (ih.1.add hcosInt1) hcosInt2,
        intervalIntegral.integral_add ih.1 hcosInt1, ih.2,
        Bethe.integral_cos_nat_mul (by omega), Bethe.integral_cos_nat_mul (by omega)]
      ring

private theorem fourierXi_cosCoeff {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    Bethe.cosCoeff (Bethe.Xi μ) n = 2 * π * Real.exp (-μ) ^ n := by
  have ha := Bethe.summable_two_mul_exp_pow hμ
  cases n with
  | zero =>
      rw [Bethe.Xi_eq_trigSeries hμ, Bethe.cosCoeff_trigSeries_zero ha summable_zero 1]
      simp
  | succ n =>
      rw [Bethe.Xi_eq_trigSeries hμ, Bethe.cosCoeff_trigSeries_succ ha summable_zero 1 n]
      ring

private theorem fourier_sin_product_cos_identity (n : ℕ) (α : ℝ) :
    Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
      (Real.cos ((n : ℝ) * α) - Real.cos (((n + 2 : ℕ) : ℝ) * α)) / 2 := by
  rw [← show (((n + 1 : ℕ) : ℝ) * α) - α = (n : ℝ) * α by push_cast; ring,
    ← show (((n + 1 : ℕ) : ℝ) * α) + α = ((n + 2 : ℕ) : ℝ) * α by push_cast; ring,
    Real.cos_sub, Real.cos_add]
  ring

private theorem fourier_sin_kernel_integral {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    ∫ α in (-π)..π,
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α) =
      2 * π * Real.exp (-μ) ^ (n + 1) := by
  let r : ℝ := Real.exp (-μ)
  have hcos0 : ∫ α in (-π)..π, Bethe.Xi μ α * Real.cos ((n : ℝ) * α) = 2 * π * r ^ n := by
    simpa [Bethe.cosCoeff, r] using fourierXi_cosCoeff hμ n
  have hcos2 : ∫ α in (-π)..π, Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α) =
      2 * π * r ^ (n + 2) := by
    simpa [Bethe.cosCoeff, r] using fourierXi_cosCoeff hμ (n + 2)
  have hprod : (fun α : ℝ => Bethe.Xi μ α * Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α)) =
      (fun α => (1 / 2 : ℝ) * (Bethe.Xi μ α * Real.cos ((n : ℝ) * α)) -
        (1 / 2 : ℝ) * (Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α))) := by
    funext α; rw [mul_assoc, fourier_sin_product_cos_identity]; ring
  have hXiCont := Bethe.continuous_Xi hμ
  have hInt0 : IntervalIntegrable
      (fun α : ℝ => (1 / 2 : ℝ) * (Bethe.Xi μ α * Real.cos ((n : ℝ) * α))) volume (-π) π :=
    ((hXiCont.mul (by fun_prop)).intervalIntegrable _ _).const_mul _
  have hInt2 : IntervalIntegrable
      (fun α : ℝ => (1 / 2 : ℝ) * (Bethe.Xi μ α * Real.cos (((n + 2 : ℕ) : ℝ) * α))) volume (-π) π :=
    ((hXiCont.mul (by fun_prop)).intervalIntegrable _ _).const_mul _
  have hprodInt :
      ∫ α in (-π)..π, Bethe.Xi μ α * Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) =
        π * (r ^ n - r ^ (n + 2)) := by
    rw [hprod, intervalIntegral.integral_sub hInt0 hInt2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcos0, hcos2]
    ring
  have hsinh : 1 - r ^ 2 = 2 * r * Real.sinh μ := by
    dsimp [r]; rw [Real.sinh_eq, Real.exp_neg]; field_simp [Real.exp_ne_zero]
  have hsinhPos : 0 < Real.sinh μ := Real.sinh_pos_iff.mpr hμ
  have hfun : (fun α : ℝ => Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α)) =
      (fun α => (Real.sinh μ)⁻¹ *
        (Bethe.Xi μ α * Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α))) := by
    funext α
    have hdenPos : 0 < Real.cosh μ - Real.cos α := by
      linarith [Real.one_lt_cosh.mpr hμ.ne', Real.cos_le_one α]
    rw [Bethe.Xi]; field_simp [hsinhPos.ne', hdenPos.ne']
  rw [hfun, intervalIntegral.integral_const_mul, hprodInt,
    show r ^ n - r ^ (n + 2) = r ^ n * (1 - r ^ 2) by rw [pow_add]; ring, hsinh, pow_succ]
  field_simp [hsinhPos.ne']; ring

theorem fourierP_prime_sine_integral {lam : ℝ} (hlam : 0 < lam)
    (m : ℕ) (hm : 0 < m) :
    (1 / π) * ∫ α in (-π)..π,
      fourierPPrime lam α * Real.sin ((m : ℝ) * α) =
      Real.exp (-2 * lam * (m : ℝ)) - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let μ : ℝ := 2 * lam
  have hμ : 0 < μ := by positivity
  have hfirst := fourier_sin_kernel_integral hμ n
  have hcot := fourierCotSin_integrable_integral n
  have hdenPos (α : ℝ) : 0 < Real.cosh μ - Real.cos α := by
    linarith [Real.one_lt_cosh.mpr hμ.ne', Real.cos_le_one α]
  have hratioInt : IntervalIntegrable (fun α : ℝ =>
      Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
        (Real.cosh μ - Real.cos α)) volume (-π) π :=
    (Continuous.div (by fun_prop) (by fun_prop) fun α => (hdenPos α).ne').intervalIntegrable _ _
  have hEq :
      (fun α => fourierPPrime lam α *
        Real.sin (((n + 1 : ℕ) : ℝ) * α)) =ᵐ[volume.restrict (uIoc (-π) π)]
      (fun α => (1 / 2 : ℝ) *
        (Real.sin α * Real.sin (((n + 1 : ℕ) : ℝ) * α) /
            (Real.cosh μ - Real.cos α) - fourierCotSin n α)) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα0
    simp [fourierPPrime, fourierCotSin, μ, hα0]; ring
  rw [intervalIntegral.integral_congr_ae_restrict hEq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hratioInt hcot.1, hfirst, hcot.2]
  have hExp : Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) = Real.exp (-μ) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]; congr 1; dsimp [μ]; push_cast; ring
  rw [hExp]
  field_simp [Real.pi_ne_zero]

noncomputable def logCoshExpRangeTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
    (Real.exp (-2 * lam * ((n : ℝ) + 1)) - 1)

noncomputable def logCoshExpRangePartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, logCoshExpRangeTerm lam n

noncomputable def logCoshExpRatio (lam : ℝ) : ℝ := Real.exp (-2 * lam)

private theorem alternating_geom_partial (N : ℕ) (x : ℝ) (hx : 1 + x ≠ 0) :
    (∑ n ∈ Finset.range N, (-x) ^ n) = (1 - (-x) ^ N) / (1 + x) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; field_simp; ring

private theorem logCoshExpRangeTerm_eq_integral (lam : ℝ) (n : ℕ) :
    logCoshExpRangeTerm lam n =
      ∫ x in logCoshExpRatio lam..1, (-x) ^ n := by
  unfold logCoshExpRangeTerm logCoshExpRatio
  rw [show (fun x : ℝ => (-x) ^ n) = fun x => (-1 : ℝ) ^ n * x ^ n by funext x; rw [neg_pow],
    intervalIntegral.integral_const_mul, integral_pow]
  have hexp : Real.exp (-2 * lam * ((n : ℝ) + 1)) = Real.exp (-2 * lam) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hexp, pow_succ]; ring

private theorem logCoshExpRangePartial_eq_integral {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    logCoshExpRangePartial lam N =
      ∫ x in logCoshExpRatio lam..1, (1 - (-x) ^ N) / (1 + x) := by
  unfold logCoshExpRangePartial
  calc
    ∑ n ∈ Finset.range N, logCoshExpRangeTerm lam n =
        ∑ n ∈ Finset.range N, ∫ x in logCoshExpRatio lam..1, (-x) ^ n :=
          Finset.sum_congr rfl fun n _ => logCoshExpRangeTerm_eq_integral lam n
    _ = ∫ x in logCoshExpRatio lam..1, ∑ n ∈ Finset.range N, (-x) ^ n :=
          (intervalIntegral.integral_finsetSum fun n _ =>
            (continuous_id.neg.pow n).intervalIntegrable _ _).symm
    _ = ∫ x in logCoshExpRatio lam..1, (1 - (-x) ^ N) / (1 + x) := by
          apply intervalIntegral.integral_congr fun x hx => ?_
          have hq : 0 < logCoshExpRatio lam := Real.exp_pos _
          have hq1 : logCoshExpRatio lam < 1 := by
            unfold logCoshExpRatio; rw [Real.exp_lt_one_iff]; linarith
          have hmem : x ∈ Icc (logCoshExpRatio lam) 1 := by simpa [uIcc_of_le hq1.le] using hx
          exact alternating_geom_partial N x (by linarith [hmem.1])

private theorem logCoshExpTarget_eq_integral {lam : ℝ} :
    ∫ x in logCoshExpRatio lam..1, (1 + x)⁻¹ =
      Real.log 2 - Real.log (1 + logCoshExpRatio lam) := by
  have hratio : 0 < logCoshExpRatio lam := Real.exp_pos _
  calc
    ∫ x in logCoshExpRatio lam..1, (1 + x)⁻¹ =
        ∫ x in logCoshExpRatio lam..1, (x + 1)⁻¹ := by congr 1; funext x; ring
    _ = ∫ x in logCoshExpRatio lam + 1..1 + 1, x⁻¹ := by
        rw [intervalIntegral.integral_comp_add_right]
    _ = Real.log (2 / (1 + logCoshExpRatio lam)) := by
        rw [integral_inv_of_pos (by linarith) (by norm_num)]; congr 1; ring
    _ = Real.log 2 - Real.log (1 + logCoshExpRatio lam) :=
        Real.log_div (by norm_num) (by positivity)

private theorem logCoshExpRemainder_bound {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    |logCoshExpRangePartial lam N -
        (Real.log 2 - Real.log (1 + logCoshExpRatio lam))| ≤ 1 / ((N : ℝ) + 1) := by
  let q := logCoshExpRatio lam
  have hq : 0 < q := Real.exp_pos _
  have hqle : q ≤ 1 := by
    dsimp [q, logCoshExpRatio]; rw [Real.exp_le_one_iff]; linarith
  have hdom : ∀ x ∈ uIcc q 1, 1 + x ≠ 0 := fun x hx => by
    have hx' : x ∈ Icc q 1 := by simpa [uIcc_of_le hqle] using hx
    linarith [hx'.1]
  have hJint : IntervalIntegrable (fun x : ℝ => x ^ N / (1 + x)) volume q 1 :=
    ((continuousOn_id.pow N).div (continuousOn_const.add continuousOn_id) hdom).intervalIntegrable
  have hInvInt : IntervalIntegrable (fun x : ℝ => (1 + x)⁻¹) volume q 1 :=
    ((continuousOn_const.add continuousOn_id).inv₀ hdom).intervalIntegrable
  have hKernelInt :
      IntervalIntegrable (fun x : ℝ => (1 - (-x) ^ N) / (1 + x)) volume q 1 :=
    ((continuousOn_const.sub (continuousOn_id.neg.pow N)).div
      (continuousOn_const.add continuousOn_id) hdom).intervalIntegrable
  have hJnonneg : 0 ≤ ∫ x in q..1, x ^ N / (1 + x) :=
    intervalIntegral.integral_nonneg hqle fun x hx =>
      div_nonneg (pow_nonneg (hq.le.trans hx.1) _) (by linarith [hx.1])
  have hJbound : ∫ x in q..1, x ^ N / (1 + x) ≤ 1 / ((N : ℝ) + 1) := by
    calc
      ∫ x in q..1, x ^ N / (1 + x) ≤ ∫ x in q..1, x ^ N :=
        intervalIntegral.integral_mono_on hqle hJint
          ((continuous_id.pow N).intervalIntegrable _ _) fun x hx =>
          div_le_self (pow_nonneg (hq.le.trans hx.1) _) (by linarith [hx.1])
      _ = (1 - q ^ (N + 1)) / ((N : ℝ) + 1) := by rw [integral_pow]; simp
      _ ≤ 1 / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hq.le (N + 1)]) (by positivity)
  have herror :
      logCoshExpRangePartial lam N - (Real.log 2 - Real.log (1 + q)) =
        -((-1 : ℝ) ^ N) * (∫ x in q..1, x ^ N / (1 + x)) := by
    rw [logCoshExpRangePartial_eq_integral hlam N,
      show Real.log 2 - Real.log (1 + q) = ∫ x in q..1, (1 + x)⁻¹ from
        logCoshExpTarget_eq_integral.symm,
      ← intervalIntegral.integral_sub hKernelInt hInvInt]
    have hfun : (fun x : ℝ => (1 - (-x) ^ N) / (1 + x) - (1 + x)⁻¹) =
        fun x => -((-1 : ℝ) ^ N) * (x ^ N / (1 + x)) := by
      funext x; rw [neg_pow]; field_simp; ring
    rw [hfun, intervalIntegral.integral_const_mul]
  rw [herror, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hJnonneg]
  exact hJbound

private theorem tendsto_logCoshExpRangePartial {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (logCoshExpRangePartial lam) atTop
      (𝓝 (lam - Real.log (Real.cosh lam))) := by
  have htarget : Real.log 2 - Real.log (1 + logCoshExpRatio lam) =
      lam - Real.log (Real.cosh lam) := by
    have hfactor : Real.cosh lam = Real.exp lam * ((1 + logCoshExpRatio lam) / 2) := by
      rw [Real.cosh_eq, show Real.exp (-lam) = Real.exp lam * logCoshExpRatio lam by
        unfold logCoshExpRatio; rw [← Real.exp_add]; congr 1; ring]
      ring
    rw [hfactor, Real.log_mul (Real.exp_ne_zero _) (by unfold logCoshExpRatio; positivity),
      Real.log_exp, Real.log_div (by unfold logCoshExpRatio; positivity) two_ne_zero]
    ring
  rw [← htarget, tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using
    squeeze_zero (fun _ => abs_nonneg _) (logCoshExpRemainder_bound hlam)
      (by simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

noncomputable def altTanhPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam)

noncomputable def logCoshTauCorrectionPartial (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (-1 : ℝ) ^ m / (m : ℝ) * Real.tanh ((m : ℝ) * lam) *
      (Real.exp (-2 * lam * m) - 1)

private theorem tanh_exp_identity (x : ℝ) :
    (1 + Real.tanh x) * (Real.exp (-2 * x) - 1) = -2 * Real.tanh x := by
  rw [Real.tanh_eq, show Real.exp (-2 * x) = Real.exp (-x) / Real.exp x by
    rw [← Real.exp_sub]; congr 1; ring]
  have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have he' : Real.exp (-x) ≠ 0 := (Real.exp_pos (-x)).ne'
  field_simp [he, he']; ring

private theorem finite_logCosh_tanh_identity (lam : ℝ) (N : ℕ) :
    logCoshExpRangePartial lam N + logCoshTauCorrectionPartial lam N =
      -2 * altTanhPartial lam N := by
  unfold logCoshExpRangePartial logCoshTauCorrectionPartial altTanhPartial
  rw [sum_Icc_one_eq_sum_range, sum_Icc_one_eq_sum_range, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold logCoshExpRangeTerm
  push_cast
  have h := tanh_exp_identity (((n : ℝ) + 1) * lam)
  rw [show -2 * lam * ((n : ℝ) + 1) = -2 * (((n : ℝ) + 1) * lam) by ring]
  linear_combination ((-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)) * h

theorem identity43 (lam : ℝ) (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (fun N => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N)
        atTop (𝓝 (lam + 2 * S)) := by
  obtain ⟨S, _T, hS, _hT, _hpos, _hval⟩ := identity44 lam hlam
  have hS' : Tendsto (altTanhPartial lam) atTop (𝓝 S) := hS
  refine ⟨S, hS', ?_⟩
  have h1 := ((tendsto_const_nhds (x := Real.log (Real.cosh lam))).add
    (tendsto_logCoshExpRangePartial hlam)).add (hS'.const_mul 2)
  rw [show Real.log (Real.cosh lam) + (lam - Real.log (Real.cosh lam)) + 2 * S =
      lam + 2 * S by ring] at h1
  refine h1.congr' (Filter.Eventually.of_forall fun N => ?_)
  linarith [finite_logCosh_tanh_identity lam N]

end PottsDiscontinuity
