module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Bethe.Prop21Coeff
public import PottsDiscontinuity.Bethe.RatioProducts

/-!
# Section 4 logarithmic series and identity (4.3)

This module proves the ordered partial-sum expansion of `log (cosh λ)` and then derives
equation (4.3) using the previously proved `identity44`.  The expansion is handled as an ordered
series throughout; no absolute convergence is claimed for its limiting series.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

/-- The real logarithmic profile in (4.2), with its value at the single singular point
chosen as an `L¹` representative.  Every theorem identifying it with the source profile is
stated away from `α = 0`; its value there does not encode a finite value for the logarithmic
singularity. -/
noncomputable def fourierP (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2) * Real.log
      ((Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α))

/-- The Möbius expression for `e^{ik(α)}` in unit-circle coordinates. -/
private theorem exp_I_mul_kMap_fraction {lam α : ℝ} (hlam : 0 < lam) :
    Complex.exp (I * (Bethe.kMap lam α)) =
      (Complex.exp (I * α) * (Real.exp lam) - 1) /
        ((Real.exp lam) - Complex.exp (I * α)) := by
  grind [Bethe.exp_I_mul_kMap_aux hlam α, Complex.exp_ne_zero, Complex.exp_neg]

section
variable {lam c α : ℝ} (hlam : 0 < lam) (hc : c ^ 2 = 2 + 2 * Real.cosh lam)
    (hcos : Real.cos α < 1)
include hlam hc hcos

/-- With `c² = 2 - 2Δ = 2 + 2 cosh λ`, the Bethe factor satisfies the source modulus formula.
This is the explicit algebraic step omitted in the source's phrase “some elementary algebraic
manipulations.” -/
theorem normSq_M_kMap_eq_ratio :
    Complex.normSq (BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α)))) =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
  let E := (Real.exp lam : ℂ)
  let w := Complex.exp (I * α)
  have hEreal : 1 < Real.exp lam := by simpa using hlam
  have hwNorm : ‖w‖ = 1 := by simp [w]
  have hEw : E - w ≠ 0 := by
    apply Bethe.ofReal_sub_ne_zero hEreal
    assumption
  have h1w : 1 - w ≠ 0 := by
    intro h
    have hw1 : w = 1 := by linear_combination -h
    have hre := congrArg Complex.re hw1
    have : Real.cos α = 1 := by
      change (Complex.exp (I * (α : ℂ))).re = 1 at hre
      rw [Bethe.exp_I_mul_ofReal] at hre
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
      linarith
    linarith
  have hEpos := (Real.exp_pos lam).ne'
  have hcsq : (c : ℂ) ^ 2 = (E + 1) ^ 2 / E := by
    have hreal : c ^ 2 = (Real.exp lam + 1) ^ 2 / Real.exp lam := by
      rw [hc, Real.cosh_eq]
      grind [Real.exp_neg]
    have hrealC := congrArg (fun x : ℝ => (x : ℂ)) hreal
    simpa [E] using hrealC
  have hz : Complex.exp (I * (Bethe.kMap lam α : ℂ)) = (w * E - 1) / (E - w) := by
    simpa [w, E, mul_comm, mul_left_comm, mul_assoc] using
      exp_I_mul_kMap_fraction hlam
  have hden : 1 - Complex.exp (I * (Bethe.kMap lam α : ℂ)) =
      (E + 1) * (1 - w) / (E - w) := by
    grind
  have hM : BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α))) =
      (w - E ^ 2) / (E * (1 - w)) := by
    rw [BetheAnsatz.M, hden, hcsq]
    have hEc : E ≠ 0 := by
      change (Real.exp lam : ℂ) ≠ 0
      exact_mod_cast hEpos
    field_simp [hEw, h1w, hEc]
    ring
  rw [hM]
  have hESq : Complex.normSq E = Real.exp lam ^ 2 := by
    grind [Complex.normSq_ofReal]
  have hwform : w = (Real.cos α) + (Real.sin α) * I := by
    exact Bethe.exp_I_mul_ofReal α
  have hwRe : w.re = Real.cos α := by
    rw [hwform]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hwIm : w.im = Real.sin α := by
    rw [hwform]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero]
    simp
  have hE2re : (E ^ 2).re = Real.exp lam ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hE2im : (E ^ 2).im = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hnum : Complex.normSq (w - E ^ 2) =
      Real.exp lam ^ 4 - 2 * Real.exp lam ^ 2 * Real.cos α + 1 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm, hE2re, hE2im]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h1wSq : Complex.normSq (1 - w) = 2 - 2 * Real.cos α := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hwRe, hwIm]
    simp
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hdenSq : Complex.normSq (E * (1 - w)) =
      Real.exp lam ^ 2 * (2 - 2 * Real.cos α) := by
    grind
  rw [Complex.normSq_div, hnum, hdenSq]
  have hcosh : Real.cosh (2 * lam) =
      (Real.exp lam ^ 2 + (Real.exp lam ^ 2)⁻¹) / 2 := by
    rw [Real.cosh_eq]
    have hplus : Real.exp (2 * lam) = Real.exp lam ^ 2 := by
      rw [show 2 * lam = lam + lam by ring, Real.exp_add]
      ring
    have hminus : Real.exp (-(2 * lam)) = (Real.exp lam ^ 2)⁻¹ := by
      rw [Real.exp_neg, hplus]
    grind
  grind

/-- On the punctured circle, the real profile is exactly the logarithm of the modulus of the
Bethe factor `M(e^{ik(α)})`. -/
theorem fourierP_eq_log_norm :
    fourierP lam α = Real.log
      ‖BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α)))‖ := by
  let z := BetheAnsatz.M c (Complex.exp (I * (Bethe.kMap lam α)))
  have hnormSq : ‖z‖ ^ 2 =
      (Real.cosh (2 * lam) - Real.cos α) / (1 - Real.cos α) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_M_kMap_eq_ratio hlam hc hcos
  unfold fourierP
  rw [ite_eq_right (by grind [Real.cos_zero])]
  grind [Real.log_pow]

end

/-- Jordan's sine inequality gives a quadratic lower bound for the denominator of `P` on the
fundamental interval. -/
theorem fourier_one_sub_cos_lower {α : ℝ} (hα : α ∈ Icc (-π) π) :
    2 * α ^ 2 / π ^ 2 ≤ 1 - Real.cos α := by
  have hx : |α / 2| ≤ π / 2 := by
    grind
  have hjSq :=
    (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 (Real.mul_abs_le_abs_sin hx)
  have habshalf : |α / 2| = |α| / 2 := by
    simp [abs_div]
  rw [habshalf] at hjSq
  have hsimpl : (2 / π * (|α| / 2)) ^ 2 = α ^ 2 / π ^ 2 := by
    grind
  rw [hsimpl, sq_abs] at hjSq
  grind [Real.sin_sq_eq_half_sub]

/-- The punctured derivative of the logarithmic profile, assigned an irrelevant finite value at
the singular point so that it can be used as an interval-integral representative. -/
noncomputable def fourierPPrime (lam α : ℝ) : ℝ :=
  if α = 0 then 0 else
    (1 / 2) *
      (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
        Real.sin α / (1 - Real.cos α))

/-- Away from zero, `fourierPPrime` is the classical derivative of `P`. -/
theorem fourierP_hasDerivAt {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Ioo (-π) π) (hα0 : α ≠ 0) :
    HasDerivAt (fourierP lam) (fourierPPrime lam α) α := by
  have hcosLower := fourier_one_sub_cos_lower (Ioo_subset_Icc_self hα)
  have hden : 0 < 1 - Real.cos α := by
    have hbound : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
    grind
  have hcosh : 1 < Real.cosh (2 * lam) :=
    Real.one_lt_cosh.mpr (by positivity)
  have hnum : 0 < Real.cosh (2 * lam) - Real.cos α := by
    linarith
  let u := fun x => Real.cosh (2 * lam) - Real.cos x
  let v := fun x => 1 - Real.cos x
  have hu : HasDerivAt u (Real.sin α) α := by
    simpa using (Real.hasDerivAt_cos α).const_sub (Real.cosh (2 * lam))
  have hraw := (hu.div (by simpa using (Real.hasDerivAt_cos α).const_sub (1 : ℝ)) hden.ne').log (div_ne_zero hnum.ne' hden.ne')
  have hderiv :
      (1 / 2) *
          (((Real.sin α * v α - u α * Real.sin α) / v α ^ 2) / ((u / v) α)) =
        fourierPPrime lam α := by
    simp [fourierPPrime, hα0, u, v]
    field_simp [hden.ne', hnum.ne']
  have hraw'' := (hraw.const_mul (1 / 2 : ℝ)).congr_deriv hderiv
  apply hraw''.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hα0] with x hx
  simp [fourierP, u, v, hx]

section
variable {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (α : ℝ)

include n α in
/-- The product `sin α · sin((n+1)α)/(1-cos α)`, with its removable singularity assigned
the value zero at the origin. -/
noncomputable def fourierCotSin : ℝ :=
  if α = 0 then 0 else
    Real.sin α * Real.sin ((n + 1 : ℕ) * α) / (1 - Real.cos α)

private theorem fourier_sin_recurrence :
    Real.sin α *
        (Real.sin ((n + 2 : ℕ) * α) -
          Real.sin ((n + 1 : ℕ) * α)) =
      (1 - Real.cos α) *
        (Real.cos ((n + 2 : ℕ) * α) +
          Real.cos ((n + 1 : ℕ) * α)) := by
  have hcast : ((n + 2 : ℕ) * α) = ((n + 1 : ℕ) * α) + α := by
    push_cast
    ring
  rw [hcast, Real.sin_add, Real.cos_add]
  have hsq := Real.sin_sq_add_cos_sq α
  grind

private theorem fourierCotSin_succ_ae :
    (fun α => fourierCotSin (n + 1) α) =ᵐ[volume.restrict (uIoc (-π) π)]
      (fun α => fourierCotSin n α +
        Real.cos ((n + 2 : ℕ) * α) +
        Real.cos ((n + 1 : ℕ) * α)) := by
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
  have hαcc := Ioc_subset_Icc_self (by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα)
  have hdenLower := fourier_one_sub_cos_lower hαcc
  have hden : 0 < 1 - Real.cos α := by
    have hpos : 0 < 2 * α ^ 2 / π ^ 2 := by positivity
    grind
  have hrec := fourier_sin_recurrence n α
  simp [fourierCotSin, hα0]
  grind

private theorem fourierCotSin_integrable_integral :
    IntervalIntegrable (fun α => fourierCotSin n α) volume (-π) π ∧
      ∫ α in (-π)..π, fourierCotSin n α = 2 * π := by
  induction n with
  | zero =>
      have hEq : (fun α => fourierCotSin 0 α) =ᵐ[volume.restrict (uIoc (-π) π)]
          (fun α => 1 + Real.cos α) := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc,
          ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα hα0
        have hαcc := Ioc_subset_Icc_self (by simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα)
        have hden := lt_of_lt_of_le (by positivity) (fourier_one_sub_cos_lower hαcc)
        simp [fourierCotSin, hα0]
        field_simp [hden.ne']
        nlinarith [Real.sin_sq_add_cos_sq α]
      have hcosCont : Continuous (fun α : ℝ => 1 + Real.cos α) := by fun_prop
      refine ⟨(intervalIntegrable_congr_ae hEq).mpr (hcosCont.intervalIntegrable _ _), ?_⟩
      calc
        _ =
            ∫ α in (-π)..π, 1 + Real.cos α :=
              intervalIntegral.integral_congr_ae_restrict hEq
        _ = _ := by
          rw [intervalIntegral.integral_add intervalIntegrable_const
            (Real.continuous_cos.intervalIntegrable _ _)]
          have hcoszero : ∫ α in (-π)..π, Real.cos α = 0 := by
            simp
          rw [intervalIntegral.integral_const, hcoszero]
          ring
  | succ n ih =>
      have hEq := fourierCotSin_succ_ae n
      have hcos1 : Continuous (fun α : ℝ => Real.cos ((n + 2 : ℕ) * α)) := by
        fun_prop
      have hcos2 : Continuous (fun α : ℝ => Real.cos ((n + 1 : ℕ) * α)) := by
        fun_prop
      have hcosInt1 : IntervalIntegrable
          (fun α : ℝ => Real.cos ((n + 2 : ℕ) * α)) volume (-π) π :=
        hcos1.intervalIntegrable _ _
      have hcosInt2 : IntervalIntegrable
          (fun α : ℝ => Real.cos ((n + 1 : ℕ) * α)) volume (-π) π :=
        hcos2.intervalIntegrable _ _
      have hnextInt := ((ih.1.add hcosInt1).add hcosInt2).congr_ae hEq.symm
      refine ⟨hnextInt, ?_⟩
      calc
        _ =
            ∫ α in (-π)..π,
              fourierCotSin n α + Real.cos ((n + 2 : ℕ) * α) +
                Real.cos ((n + 1 : ℕ) * α) :=
                  intervalIntegral.integral_congr_ae_restrict hEq
        _ = (∫ α in (-π)..π, fourierCotSin n α) +
              (∫ α in (-π)..π, Real.cos ((n + 2 : ℕ) * α)) +
              (∫ α in (-π)..π, Real.cos ((n + 1 : ℕ) * α)) := by
          simp_all
        _ = _ := by
          rw [ih.2, Bethe.integral_cos_nat_mul (by omega),
            Bethe.integral_cos_nat_mul (by omega)]
          ring

include hμ in
private theorem fourierXi_cosCoeff :
    Bethe.cosCoeff (Bethe.Xi μ) n = 2 * π * Real.exp (-μ) ^ n := by
  have ha := Bethe.summable_two_mul_exp_pow hμ
  have hb : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  cases n with
  | zero =>
      simp [Bethe.Xi_eq_trigSeries hμ, Bethe.cosCoeff_trigSeries_zero ha hb 1]
  | succ n =>
      rw [Bethe.Xi_eq_trigSeries hμ,
        Bethe.cosCoeff_trigSeries_succ ha hb 1 n]
      ring

private theorem fourier_sin_product_cos_identity :
    Real.sin α * Real.sin ((n + 1 : ℕ) * α) =
      (Real.cos (n * α) - Real.cos ((n + 2 : ℕ) * α)) / 2 := by
  have hminus : ((n + 1 : ℕ) * α) - α = n * α := by
    push_cast
    ring
  have hplus : ((n + 1 : ℕ) * α) + α = (n + 2 : ℕ) * α := by
    push_cast
    ring
  grind [Real.cos_sub, Real.cos_add]

include hμ in
private theorem fourier_sin_kernel_integral :
    ∫ α in (-π)..π,
      Real.sin α * Real.sin ((n + 1 : ℕ) * α) /
        (Real.cosh μ - Real.cos α) =
      2 * π * Real.exp (-μ) ^ (n + 1) := by
  let r := Real.exp (-μ)
  have hcosCoeff0 := fourierXi_cosCoeff hμ n
  have hcosCoeff2 := fourierXi_cosCoeff hμ (n + 2)
  have hcos0 :
      ∫ α in (-π)..π, Bethe.Xi μ α * Real.cos (n * α) =
        2 * π * r ^ n := by
    assumption
  have hcos2 :
      ∫ α in (-π)..π,
        Bethe.Xi μ α * Real.cos ((n + 2 : ℕ) * α) =
          2 * π * r ^ (n + 2) := by
    assumption
  have hprod : (fun α : ℝ => Bethe.Xi μ α * Real.sin α *
      Real.sin ((n + 1 : ℕ) * α)) =
      (fun α => (1 / 2) *
          (Bethe.Xi μ α * Real.cos (n * α)) -
        (1 / 2) *
          (Bethe.Xi μ α * Real.cos ((n + 2 : ℕ) * α))) := by
    grind [mul_assoc, fourier_sin_product_cos_identity]
  have hXiCont := Bethe.continuous_Xi hμ
  have hcosCont0 : Continuous (fun α : ℝ => Real.cos (n * α)) := by fun_prop
  have hcosCont2 : Continuous
      (fun α : ℝ => Real.cos ((n + 2 : ℕ) * α)) := by fun_prop
  have hXiCosInt0 : IntervalIntegrable
      (fun α : ℝ => Bethe.Xi μ α * Real.cos (n * α)) volume (-π) π :=
    (hXiCont.mul hcosCont0).intervalIntegrable _ _
  have hXiCosInt2 : IntervalIntegrable
      (fun α : ℝ => Bethe.Xi μ α * Real.cos ((n + 2 : ℕ) * α)) volume (-π) π :=
    (hXiCont.mul hcosCont2).intervalIntegrable _ _
  have hprodInt :
      ∫ α in (-π)..π, Bethe.Xi μ α * Real.sin α *
          Real.sin ((n + 1 : ℕ) * α) =
        π * (r ^ n - r ^ (n + 2)) := by
    calc
      _ =
          ∫ α in (-π)..π, (1 / 2) *
            (Bethe.Xi μ α * Real.cos (n * α)) -
              (1 / 2) *
                (Bethe.Xi μ α * Real.cos ((n + 2 : ℕ) * α)) := by grind
      _ = (∫ α in (-π)..π, (1 / 2) *
              (Bethe.Xi μ α * Real.cos (n * α))) -
            ∫ α in (-π)..π, (1 / 2) *
              (Bethe.Xi μ α * Real.cos ((n + 2 : ℕ) * α)) :=
          intervalIntegral.integral_sub (by simp_all) (by simp_all)
      _ = (1 / 2) * (2 * π * r ^ n) - (1 / 2) * (2 * π * r ^ (n + 2)) := by
          simp_all
      _ = _ := by ring
  have hsinh : 1 - r ^ 2 = 2 * r * Real.sinh μ := by
    dsimp [r]
    rw [Real.sinh_eq, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have hkernel : ∀ α : ℝ,
      Real.sin α * Real.sin ((n + 1 : ℕ) * α) /
        (Real.cosh μ - Real.cos α) =
      (Real.sinh μ)⁻¹ *
        (Bethe.Xi μ α * Real.sin α * Real.sin ((n + 1 : ℕ) * α)) := by
    grind [Bethe.Xi, Real.sinh_pos_iff]
  have hfun :
      (fun α : ℝ => Real.sin α * Real.sin ((n + 1 : ℕ) * α) /
        (Real.cosh μ - Real.cos α)) =
      (fun α => (Real.sinh μ)⁻¹ *
        (Bethe.Xi μ α * Real.sin α * Real.sin ((n + 1 : ℕ) * α))) := by
    grind
  rw [hfun, intervalIntegral.integral_const_mul, hprodInt]
  have hsinhNe := (Real.sinh_pos_iff.mpr hμ).ne'
  grind

/-- The sine coefficient of the classical derivative of `P`, including the harmless value at
the singular point, is the value used in §4. -/
theorem fourierP_prime_sine_integral {lam : ℝ} (hlam : 0 < lam)
    {m : ℕ} (hm : 0 < m) :
    (1 / π) * ∫ α in (-π)..π,
      fourierPPrime lam α * Real.sin (m * α) =
      Real.exp (-2 * lam * m) - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let μ := 2 * lam
  have hμ : 0 < μ := by linarith
  have hfirst := fourier_sin_kernel_integral hμ n
  have hcot := fourierCotSin_integrable_integral n
  have hdenPos (α : ℝ) : 0 < Real.cosh μ - Real.cos α := by
    have hcosh := Real.one_lt_cosh.mpr hμ.ne'
    linarith [Real.cos_le_one α]
  have hdenCont : Continuous (fun α : ℝ => Real.cosh μ - Real.cos α) := by fun_prop
  have hnumCont : Continuous (fun α : ℝ => Real.sin α *
      Real.sin ((n + 1 : ℕ) * α)) := by fun_prop
  have hratioCont :=
    hnumCont.div hdenCont (by grind)
  have hratioInt : IntervalIntegrable (fun α : ℝ =>
      Real.sin α * Real.sin ((n + 1 : ℕ) * α) /
        (Real.cosh μ - Real.cos α)) volume (-π) π :=
    hratioCont.intervalIntegrable _ _
  have hEq :
      (fun α => fourierPPrime lam α *
        Real.sin ((n + 1 : ℕ) * α)) =ᵐ[volume.restrict (uIoc (-π) π)]
      (fun α => (1 / 2) *
        (Real.sin α * Real.sin ((n + 1 : ℕ) * α) /
            (Real.cosh μ - Real.cos α) - fourierCotSin n α)) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume 0)] with α hα0
    simp [fourierPPrime, fourierCotSin, μ, hα0]
    ring
  have hprimeIntegral :
      ∫ α in (-π)..π, fourierPPrime lam α *
          Real.sin ((n + 1 : ℕ) * α) =
        (1 / 2) * (2 * π * Real.exp (-μ) ^ (n + 1) - 2 * π) := by
    calc
      _ =
          ∫ α in (-π)..π, (1 / 2) *
            (Real.sin α * Real.sin ((n + 1 : ℕ) * α) /
                (Real.cosh μ - Real.cos α) - fourierCotSin n α) :=
          intervalIntegral.integral_congr_ae_restrict hEq
      _ = (1 / 2) *
            ((∫ α in (-π)..π,
                Real.sin α * Real.sin ((n + 1 : ℕ) * α) /
                  (Real.cosh μ - Real.cos α)) -
              ∫ α in (-π)..π, fourierCotSin n α) := by
          simp_all
      _ = _ := by
          grind
  have hExp : Real.exp (-2 * lam * (n + 1 : ℕ)) =
      Real.exp (-μ) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    grind
  grind [Real.pi_ne_zero]

end

section
variable (lam : ℝ)
include lam

/-- The `m`-th summand in the expansion of `log (cosh λ)`, with `m ≥ 1`. -/
noncomputable def logCoshExpTerm (m : ℕ) : ℝ :=
  (-1) ^ m / m * (Real.exp (-2 * lam * m) - 1)

/-- The ordered partial sum of the expansion of `log (cosh λ)`, indexed from `m = 1`. -/
noncomputable def logCoshExpPartial (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, logCoshExpTerm lam m

/-- The `n`-th summand after reindexing `m = n + 1`. -/
noncomputable def logCoshExpRangeTerm (n : ℕ) : ℝ :=
  (-1) ^ (n + 1) / (n + 1) *
    (Real.exp (-2 * lam * (n + 1)) - 1)

/-- The same ordered partial sums, expressed as a range starting at zero. -/
noncomputable def logCoshExpRangePartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, logCoshExpRangeTerm lam n

/-- The exponential ratio used in the integral representation of the partial sums. -/
noncomputable def logCoshExpRatio : ℝ := Real.exp (-2 * lam)

end

section
variable {lam : ℝ} (hlam : 0 < lam) (N : ℕ)

private theorem alternating_geom_partial (x : ℝ) (hx : 1 + x ≠ 0) :
    (∑ n ∈ Finset.range N, (-x) ^ n) = (1 - (-x) ^ N) / (1 + x) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring

private theorem logCoshExpRangeTerm_eq_integral (lam : ℝ) (n : ℕ) :
    logCoshExpRangeTerm lam n =
      ∫ x in logCoshExpRatio lam..1, (-x) ^ n := by
  unfold logCoshExpRangeTerm logCoshExpRatio
  rw [show (fun x : ℝ => (-x) ^ n) = fun x => (-1 : ℝ) ^ n * x ^ n by grind [neg_pow], intervalIntegral.integral_const_mul, integral_pow]
  have hexp : Real.exp (-2 * lam * (n + 1)) =
      Real.exp (-2 * lam) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    grind
  rw [hexp]
  ring

include hlam in
private theorem logCoshExpRangePartial_eq_integral :
    logCoshExpRangePartial lam N =
      ∫ x in logCoshExpRatio lam..1, (1 - (-x) ^ N) / (1 + x) := by
  have hsum :
      (∫ x in logCoshExpRatio lam..1, ∑ n ∈ Finset.range N, (-x) ^ n) =
        ∑ n ∈ Finset.range N, ∫ x in logCoshExpRatio lam..1, (-x) ^ n := by
    rw [intervalIntegral.integral_finsetSum]
    intro n hn
    exact (continuous_id.neg.pow n).intervalIntegrable _ _
  calc
    _ =
        ∑ n ∈ Finset.range N, ∫ x in logCoshExpRatio lam..1, (-x) ^ n := Finset.sum_congr rfl fun n hn => logCoshExpRangeTerm_eq_integral lam n
    _ = ∫ x in logCoshExpRatio lam..1, ∑ n ∈ Finset.range N, (-x) ^ n := hsum.symm
    _ = _ := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hratio : 0 < logCoshExpRatio lam := Real.exp_pos _
          have hratio_lt_one : logCoshExpRatio lam < 1 := by
            grind [Real.exp_lt_one_iff, logCoshExpRatio]
          have hmem : x ∈ Icc (logCoshExpRatio lam) 1 := by
            simpa [uIcc_of_le hratio_lt_one.le] using hx
          grind [alternating_geom_partial]

private theorem logCoshExpTarget_eq_integral :
    ∫ x in logCoshExpRatio lam..1, (1 + x)⁻¹ =
      Real.log 2 - Real.log (1 + logCoshExpRatio lam) := by
  have hratio : 0 < logCoshExpRatio lam := Real.exp_pos _
  calc
    _ =
        ∫ x in logCoshExpRatio lam..1, (x + 1)⁻¹ := by ring
    _ = ∫ x in logCoshExpRatio lam + 1..1 + 1, x⁻¹ := by
        simp
    _ = Real.log (2 / (1 + logCoshExpRatio lam)) := by
        rw [integral_inv_of_pos (by linarith) (by norm_num)]
        ring
    _ = _ := by
        rw [Real.log_div (by norm_num) (by positivity)]

include hlam in
private theorem logCoshExpRemainder_bound :
    |logCoshExpRangePartial lam N -
        (Real.log 2 - Real.log (1 + logCoshExpRatio lam))| ≤ 1 / (N + 1) := by
  let q := logCoshExpRatio lam
  have hq : 0 < q := by simp [q, logCoshExpRatio, Real.exp_pos]
  have hq1 : q < 1 := by
    simp_all [q, logCoshExpRatio, Real.exp_lt_one_iff]
  have hqle := hq1.le
  have hxmem (x : ℝ) (hx : x ∈ uIcc q 1) : x ∈ Icc q 1 := by
    simp_all
  have hdom : ∀ x ∈ Icc q 1, 0 < 1 + x := by
    grind
  have hInvInt : IntervalIntegrable (fun x : ℝ => (1 + x)⁻¹) volume q 1 := ContinuousOn.intervalIntegrable (ContinuousOn.inv₀ (ContinuousOn.add continuousOn_const continuousOn_id) fun x hx => LT.lt.ne' (hdom x (hxmem x hx)))
  have hJnonneg : 0 ≤ ∫ x in q..1, x ^ N / (1 + x) :=
    intervalIntegral.integral_nonneg hqle fun x hx => by
      have hx0 := le_trans hq.le hx.1
      positivity
  let ratio := 1 / ((N : ℝ) + 1)
  have hJbound : ∫ x in q..1, x ^ N / (1 + x) ≤ ratio := by
    calc
      _ ≤ ∫ x in q..1, x ^ N := by
        apply intervalIntegral.integral_mono_on hqle (by
          apply ContinuousOn.intervalIntegrable
          refine (continuousOn_id.pow N).div (continuousOn_const.add continuousOn_id) ?_
          grind) ((continuous_id.pow N).intervalIntegrable _ _)
        intro x hx
        have hx0 := le_trans hq.le hx.1
        exact div_le_self (pow_nonneg hx0 _) (by linarith)
      _ = (1 - q ^ (N + 1)) / (N + 1) := by
        simp
      _ ≤ ratio := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [pow_nonneg hq.le (N + 1)]
  let diff := Real.log 2 - Real.log (1 + q)
  have herror :
      logCoshExpRangePartial lam N -
          (diff) =
        -((-1) ^ N) * (∫ x in q..1, x ^ N / (1 + x)) := by
    rw [logCoshExpRangePartial_eq_integral hlam N]
    have htarget : diff = ∫ x in q..1, (1 + x)⁻¹ := by
      exact (logCoshExpTarget_eq_integral).symm
    rw [htarget]
    rw [← intervalIntegral.integral_sub (by
      apply ContinuousOn.intervalIntegrable
      refine (continuousOn_const.sub (continuousOn_id.neg.pow N)).div
        (continuousOn_const.add continuousOn_id) ?_
      grind) hInvInt]
    have hfun : (fun x : ℝ => (1 - (-x) ^ N) / (1 + x) - (1 + x)⁻¹) =
        fun x => -((-1) ^ N) * (x ^ N / (1 + x)) := by
      ring
    simp [*]
  calc
    |logCoshExpRangePartial lam N -
        (diff)| =
        ∫ x in q..1, x ^ N / (1 + x) := by
          simp [*]
    _ ≤ ratio := hJbound

include hlam in
private theorem tendsto_logCoshExpRangePartial :
    Tendsto (logCoshExpRangePartial lam) atTop
      (𝓝 (Real.log 2 - Real.log (1 + logCoshExpRatio lam))) := by
  have habs :=
    squeeze_zero (fun N => abs_nonneg _) (fun N => logCoshExpRemainder_bound hlam N) (by simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simp_all [tendsto_iff_norm_sub_tendsto_zero]

private theorem logCoshExpTarget_eq_lambda_sub_log_cosh :
    Real.log 2 - Real.log (1 + logCoshExpRatio lam) =
      lam - Real.log (Real.cosh lam) := by
  have hq : 0 < logCoshExpRatio lam := Real.exp_pos _
  have hfactor : Real.cosh lam = Real.exp lam * ((1 + logCoshExpRatio lam) / 2) := by
    rw [Real.cosh_eq]
    have hExp : Real.exp (-lam) = Real.exp lam * logCoshExpRatio lam := by
      unfold logCoshExpRatio
      rw [← Real.exp_add]
      congr 1
      ring
    grind
  have hlogfactor : Real.log (Real.cosh lam) =
      lam + Real.log ((1 + logCoshExpRatio lam) / 2) := by
    rw [hfactor, Real.log_mul (Real.exp_ne_zero _) (by positivity)]
    simp
  have hlogdiv : Real.log ((1 + logCoshExpRatio lam) / 2) =
      Real.log (1 + logCoshExpRatio lam) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  simp_all

include hlam in
/-- The ordered partial sums in the paper's logarithmic expansion converge to
`λ - log (cosh λ)`, so `log (cosh λ) = λ - ∑_{m>0} (-1)^m (e^{-2λm}-1)/m`. -/
theorem tendsto_logCoshExpPartial :
    Tendsto (logCoshExpPartial lam) atTop (𝓝 (lam - Real.log (Real.cosh lam))) := by
  have hEq : ∀ N : ℕ, logCoshExpPartial lam N = logCoshExpRangePartial lam N := by
    simp [sum_Icc_one_eq_sum_range, logCoshExpTerm, logCoshExpRangeTerm, logCoshExpPartial, logCoshExpRangePartial]
  rw [show lam - Real.log (Real.cosh lam) =
      Real.log 2 - Real.log (1 + logCoshExpRatio lam) from
        (logCoshExpTarget_eq_lambda_sub_log_cosh).symm]
  exact (tendsto_logCoshExpRangePartial hlam).congr'
    (Filter.Eventually.of_forall fun N => (hEq N).symm)

end

/-! ### The algebra of (4.3) and its ordered partial sums -/

variable (lam : ℝ) (N : ℕ)

include lam N in
/-- The ordered partial sums of `∑ (-1)^m tanh(λm)/m`. -/
noncomputable def altTanhPartial : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, (-1) ^ m / m * Real.tanh (m * lam)

include lam N in
/-- The ordered partial sums of the correction term in (4.3). -/
noncomputable def logCoshTauCorrectionPartial : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (-1) ^ m / m * Real.tanh (m * lam) *
      (Real.exp (-2 * lam * m) - 1)

private theorem tanh_exp_identity (x : ℝ) :
    (1 + Real.tanh x) * (Real.exp (-2 * x) - 1) = -2 * Real.tanh x := by
  rw [Real.tanh_eq]
  have hexp : Real.exp (-2 * x) = Real.exp (-x) / Real.exp x := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp]
  field_simp [((Real.exp_pos x).ne'), ((Real.exp_pos (-x)).ne')]
  ring

private theorem logCosh_tanh_term_identity (m : ℕ) :
    logCoshExpTerm lam m +
        (-1) ^ m / m * Real.tanh (m * lam) *
          (Real.exp (-2 * lam * m) - 1) =
      -2 * ((-1) ^ m / m * Real.tanh (m * lam)) := by
  grind [logCoshExpTerm, tanh_exp_identity]

private theorem finite_logCosh_tanh_identity :
    logCoshExpPartial lam N + logCoshTauCorrectionPartial lam N =
      -2 * altTanhPartial lam N := by
  calc
    (∑ m ∈ Finset.Icc 1 N, logCoshExpTerm lam m) +
        ∑ m ∈ Finset.Icc 1 N,
          (-1) ^ m / m * Real.tanh (m * lam) *
            (Real.exp (-2 * lam * m) - 1) =
      ∑ m ∈ Finset.Icc 1 N,
        (logCoshExpTerm lam m +
          (-1) ^ m / m * Real.tanh (m * lam) *
            (Real.exp (-2 * lam * m) - 1)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ m ∈ Finset.Icc 1 N,
        (-2 * ((-1) ^ m / m * Real.tanh (m * lam))) := by
          grind [logCosh_tanh_term_identity]
    _ = -2 * ∑ m ∈ Finset.Icc 1 N,
        ((-1) ^ m / m * Real.tanh (m * lam)) := by rw [Finset.mul_sum]

/-- **Equation (4.3)** in ordered-partial-sum form. The left series converges as a consequence
of the identity with the convergent expansion of `log(cosh λ)` and the convergence in `identity44`.
The right-hand convergence and the value relation are included. -/
theorem identity43 (hlam : 0 < lam) :
    ∃ S,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (fun N => Real.log (Real.cosh lam) - logCoshTauCorrectionPartial lam N)
        atTop (𝓝 (lam + 2 * S)) := by
  obtain ⟨S, _T, hS, _hT, _hpos, _hval⟩ := identity44 hlam
  have hS' : Tendsto (altTanhPartial lam) atTop (𝓝 S) := hS
  let logValue := Real.log (Real.cosh lam)
  have hConst : Tendsto (fun _ : ℕ => logValue) atTop
      (𝓝 (logValue)) := tendsto_const_nhds
  have hTwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have h1 :=
    hConst.add (tendsto_logCoshExpPartial hlam)
  have h2 := hTwo.mul hS'
  have hsum : Tendsto (fun N : ℕ =>
      logValue + logCoshExpPartial lam N + 2 * altTanhPartial lam N)
      atTop (𝓝 (logValue + (lam - logValue) + 2 * S)) := by
    exact h1.add h2
  have hpoint (N : ℕ) :
      logValue - logCoshTauCorrectionPartial lam N =
        logValue + logCoshExpPartial lam N + 2 * altTanhPartial lam N := by
    grind [finite_logCosh_tanh_identity]
  refine ⟨S, hS', ?_⟩
  grind

end PottsDiscontinuity

