module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.CorrectedKernel
public import RequestProject.PlanarNotation

/-!
# The kernel of `2D^{-1}` (Lemma 6.6)

On the cut square `[0, L]²` the periodic operator `2D^{-1}` (with the constant mode set to zero,
`D = -i d/dθ`) has the sawtooth kernel `σ(θ, s) = i sgn(θ - s) - i (θ - s)/π`: for
`θ ∈ [0, 2π]`,

* `∫₀^{2π} σ(θ, s) e^{ins} ds = (2/n) e^{inθ}` for `n ≠ 0` (`integral_sawtoothKernel_mul_exp`);
* `∫₀^{2π} σ(θ, s) ds = 0` (`integral_sawtoothKernel`).

This is the first identity in the proof of Lemma 6.6; subtracting `σ` from the kernel
`i sgn(θ - s) w_E(θ, s) + ⟨e₀, W(θ) B_E W(s)^* e₀⟩` of `i(T_E - T_E^*) + O_E B_E O_E^*` gives the
corrected kernel `r_E` of `CorrectedKernel.lean`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Interval

/-- The sawtooth kernel `σ(θ, s) = i sgn(θ - s) - i (θ - s)/π` of `2D^{-1}` on the cut square. -/
def sawtoothKernel (θ s : ℝ) : ℂ := Complex.I * Real.sign (θ - s) - Complex.I * ((θ - s) / π)

lemma intervalIntegrable_sign (θ a b : ℝ) :
    IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ)) volume a b := by
  refine (MeasureTheory.IntegrableOn.intervalIntegrable ?_)
  refine Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_real_sign.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_real_sign_le _


/-- Splitting `∫₀^L sgn(θ - s) F(s) ds = ∫₀^θ F - ∫_θ^L F` for an integrable `F`. -/
lemma sign_split {F : ℝ → ℂ} {θ : ℝ} (hθ : θ ∈ angleInterval)
    (h1 : IntervalIntegrable F volume 0 θ) (h2 : IntervalIntegrable F volume θ anglePeriod) :
    IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * F s) volume 0 anglePeriod ∧
    ∫ₚ s, (Real.sign (θ - s) : ℂ) * F s =
      (∫ s in (0 : ℝ)..θ, F s) - ∫ s in θ..anglePeriod, F s := by
  have e1 : ∀ᵐ s ∂(volume.restrict (Ι (0 : ℝ) θ)), (Real.sign (θ - s) : ℂ) * F s = F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [volume.ae_ne θ] with s hs hmem
    rw [Set.uIoc_of_le hθ.1] at hmem
    rw [Real.sign_of_pos (by have := lt_of_le_of_ne hmem.2 hs; linarith)]
    simp
  have e2 : ∀ᵐ s ∂(volume.restrict (Ι θ anglePeriod)),
      (Real.sign (θ - s) : ℂ) * F s = -F s := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with s hmem
    rw [Set.uIoc_of_le hθ.2] at hmem
    rw [Real.sign_of_neg (by linarith [hmem.1])]
    simp
  have i1  :=
    h1.congr_ae (Filter.EventuallyEq.symm e1)
  have i2  :=
    h2.neg.congr_ae (Filter.EventuallyEq.symm e2)
  refine ⟨i1.trans i2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_ae_restrict e1,
    intervalIntegral.integral_congr_ae_restrict e2, intervalIntegral.integral_neg]
  ring

/-- `∫₀^{2π} σ(θ, s) e^{ins} ds = (2/n) e^{inθ}` for `n ≠ 0` and `θ ∈ [0, 2π]`. -/
theorem integral_sawtoothKernel_mul_exp {θ : ℝ} (hθ : θ ∈ angleInterval) {n : ℤ}
    (hn : n ≠ 0) :
    ∫ₚ s, sawtoothKernel θ s * Complex.exp (n * Complex.I * s) =
      2 / n * Complex.exp (n * Complex.I * θ) := by
  set c : ℂ := n * Complex.I with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
  
  
  have hexp2π : Complex.exp (c * (anglePeriod : ℝ)) = 1 := by
    rw [hc, show n * Complex.I * ((anglePeriod : ℝ) : ℂ) = n * (anglePeriod * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have hcont : Continuous fun s : ℝ => Complex.exp (c * s) := by fun_prop
  -- integrals of the exponential
  have hE1 : ∫ s in (0 : ℝ)..θ, Complex.exp (c * s) = (Complex.exp (c * θ) - 1) / c := by
    rw [integral_exp_mul_complex hc0]; simp
  have hE2 : ∫ s in θ..anglePeriod, Complex.exp (c * s) = (1 - Complex.exp (c * θ)) / c := by
    rw [integral_exp_mul_complex hc0, hexp2π]
  have hE3 : ∫ₚ s, Complex.exp (c * s) = 0 := by
    rw [integral_exp_mul_complex hc0, hexp2π]; simp
  -- `∫ s e^{cs} = 2π / c`
  have hE4 : ∫ₚ s, (s : ℂ) * Complex.exp (c * s) = anglePeriod / c := by
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) anglePeriod,
        HasDerivAt (fun s : ℝ => Complex.exp (c * s) / c) (Complex.exp (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
      grind [(h1.cexp).div_const c]
    have hu : ∀ x ∈ Set.uIcc (0 : ℝ) anglePeriod, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x :=
      fun x _ => (hasDerivAt_id x).ofReal_comp
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hd
      intervalIntegrable_const (hcont.intervalIntegrable _ _)]
    simp only [one_mul]
    rw [intervalIntegral.integral_div, hE3, hexp2π]
    simp [zero_div] <;> ring
  -- assemble
  have hsplit : ∫ₚ s, sawtoothKernel θ s * Complex.exp (c * s) =
      (Complex.I * ∫ₚ s, (Real.sign (θ - s) : ℂ) * Complex.exp (c * s)) -
      Complex.I / π * ((θ * ∫ₚ s, Complex.exp (c * s)) -
        ∫ₚ s, (s : ℂ) * Complex.exp (c * s)) := by
    have hi1 : IntervalIntegrable (fun s : ℝ => Complex.I *
        ((Real.sign (θ - s) : ℂ) * Complex.exp (c * s))) volume 0 anglePeriod :=
      ((intervalIntegrable_sign θ 0 anglePeriod).mul_continuousOn hcont.continuousOn).const_mul _
    have hi2 : IntervalIntegrable (fun s : ℝ => Complex.I / π *
        ((θ : ℂ) * Complex.exp (c * s) - (s : ℂ) * Complex.exp (c * s))) volume 0 anglePeriod := by
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    have e : (fun s => sawtoothKernel θ s * Complex.exp (c * s)) = fun s =>
        Complex.I * ((Real.sign (θ - s) : ℂ) * Complex.exp (c * s)) -
        Complex.I / π * ((θ : ℂ) * Complex.exp (c * s) - (s : ℂ) * Complex.exp (c * s)) := by
      funext s
      simp only [sawtoothKernel]
      field_simp
    
    
    rw [e, intervalIntegral.integral_sub (((intervalIntegrable_sign θ 0 anglePeriod).mul_continuousOn hcont.continuousOn).const_mul _) (by
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul]
  have hfun : (fun s : ℝ => sawtoothKernel θ s * Complex.exp (n * Complex.I * s)) =
      fun s => sawtoothKernel θ s * Complex.exp (c * s) := rfl
  rw [hfun, hsplit, (sign_split hθ (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).2, hE1, hE2, hE3, hE4]
  rw [hc]
  field_simp
  ring

/-- `∫₀^{2π} σ(θ, s) ds = 0` for `θ ∈ [0, 2π]`: `2D^{-1}` kills the constant mode. -/
theorem integral_sawtoothKernel {θ : ℝ} (hθ : θ ∈ angleInterval) :
    ∫ₚ s, sawtoothKernel θ s = 0 := by
  
  have h1 := (sign_split (F := fun _ => (1 : ℂ)) hθ intervalIntegrable_const intervalIntegrable_const).2
  simp only [mul_one] at h1
  have e : (sawtoothKernel θ) = fun s =>
      Complex.I * (Real.sign (θ - s) : ℂ) - Complex.I / π * ((θ : ℂ) - (s : ℂ)) := by
    funext s
    simp only [sawtoothKernel]
    field_simp
  
  rw [e, intervalIntegral.integral_sub ((intervalIntegrable_sign θ 0 anglePeriod).const_mul _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1,
    intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hid : ∫ₚ x, (x : ℂ) = (anglePeriod ^ 2 / 2 : ℝ) := by
    rw [intervalIntegral.integral_ofReal, integral_id]; norm_num
  rw [hid]
  simp only [intervalIntegral.integral_const, Complex.real_smul, mul_one]
  push_cast
  field_simp
  ring

end PolyaNeumann
