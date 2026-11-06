module

public import RequestProject.CorrectedKernel

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

open Real MeasureTheory

/-- The sawtooth kernel `σ(θ, s) = i sgn(θ - s) - i (θ - s)/π` of `2D^{-1}` on the cut square. -/
def sawtoothKernel (θ s : ℝ) : ℂ := Complex.I * Real.sign (θ - s) - Complex.I * ((θ - s) / π)

lemma intervalIntegrable_sign θ a b :
    IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ)) volume a b := by
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  refine Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_real_sign.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_real_sign_le _

lemma intervalIntegral_sign_mul  (hf : Continuous f) 
    (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    ∫ s in 0..(2 * π), (Real.sign (θ - s) : ℂ) * f s =
      (∫ s in 0..θ, f s) - ∫ s in θ..(2 * π), f s := by
  have h1 : ∫ s in 0..θ, Real.sign (θ - s) * f s = ∫ s in 0..θ, f s := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [show ∀ᵐ s ∂volume, s ≠ θ by
      simp [ae_iff]] with s hs hmem
    rw [Set.uIoc_of_le hθ.1] at hmem
    rw [Real.sign_of_pos (by have := lt_of_le_of_ne hmem.2 hs; linarith)]
    simp
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => Real.sign (θ - s) * f s) volume a b :=
    fun a b => (intervalIntegrable_sign θ a b).mul_continuousOn hf.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 θ) (hint θ (2 * π)), h1, show ∫ s in θ..(2 * π), Real.sign (θ - s) * f s = -∫ s in θ..(2 * π), f s by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with s hmem
    rw [Set.uIoc_of_le hθ.2] at hmem
    rw [Real.sign_of_neg (by linarith [hmem.1])]
    simp]
  ring

/-- `∫₀^{2π} σ(θ, s) e^{ins} ds = (2/n) e^{inθ}` for `n ≠ 0` and `θ ∈ [0, 2π]`. -/
theorem integral_sawtoothKernel_mul_exp  (hθ : θ ∈ Set.Icc 0 (2 * π)) {n : ℤ}
    (hn : n ≠ 0) :
    ∫ s in 0..(2 * π), sawtoothKernel θ s * Complex.exp (n * Complex.I * s) =
      2 / n * Complex.exp (n * Complex.I * θ) := by
  set c := n * Complex.I with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
  have hpi : π ≠ 0 := by exact_mod_cast pi_ne_zero
  have hn' : n ≠ 0 := by exact_mod_cast hn
  have hexp2π : Complex.exp (c * (2 * π : ℝ)) = 1 := by
    rw [hc, show n * Complex.I * ((2 * π : ℝ) : ℂ) = n * (2 * π * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have hcont : Continuous fun s : ℝ => Complex.exp (c * s) := by fun_prop
  -- integrals of the exponential
  have hE3 : ∫ s in (0 : ℝ)..(2 * π), Complex.exp (c * s) = 0 := by
    rw [integral_exp_mul_complex hc0, hexp2π]; simp
  -- `∫ s e^{cs} = 2π / c`
  -- assemble
  rw [(rfl : (fun s => sawtoothKernel θ s * Complex.exp (n * Complex.I * s)) = fun s => sawtoothKernel θ s * Complex.exp (c * s)), show ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * Complex.exp (c * s) = (Complex.I * ∫ s in (0 : ℝ)..(2 * π), (Real.sign (θ - s) : ℂ) * Complex.exp (c * s)) - Complex.I / π * ((θ * ∫ s in (0 : ℝ)..(2 * π), Complex.exp (c * s)) - ∫ s in (0 : ℝ)..(2 * π), s * Complex.exp (c * s)) by
    have hi2 : IntervalIntegrable (fun s : ℝ => Complex.I / π *
        (θ * Complex.exp (c * s) - s * Complex.exp (c * s))) volume 0 (2 * π) := by
      exact Continuous.intervalIntegrable (by fun_prop) _ _
    have e : (fun s => sawtoothKernel θ s * Complex.exp (c * s)) = fun s =>
        Complex.I * ((Real.sign (θ - s) : ℂ) * Complex.exp (c * s)) -
        Complex.I / π * (θ * Complex.exp (c * s) - s * Complex.exp (c * s)) := by
      funext s
      simp [sawtoothKernel]
      field_simp
    rw [e, intervalIntegral.integral_sub (((intervalIntegrable_sign θ 0 (2 * π)).mul_continuousOn hcont.continuousOn).const_mul _) hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul], intervalIntegral_sign_mul hcont hθ, show ∫ s in (0 : ℝ)..θ, Complex.exp (c * s) = (Complex.exp (c * θ) - 1) / c by
    rw [integral_exp_mul_complex hc0]; simp, show ∫ s in θ..(2 * π), Complex.exp (c * s) = (1 - Complex.exp (c * θ)) / c by
    rw [integral_exp_mul_complex hc0, hexp2π], hE3, show ∫ s in (0 : ℝ)..(2 * π), (s : ℂ) * Complex.exp (c * s) = 2 * π / c by
    have hu : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x :=
      fun x _ => by simpa using (hasDerivAt_id x).ofReal_comp
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
      convert (h1.cexp.div_const c) using 1
      field_simp)
      intervalIntegrable_const (hcont.intervalIntegrable _ _)]
    simp only [one_mul]
    rw [intervalIntegral.integral_div, hE3, hexp2π]
    push_cast
    simp
    ring]
  rw [hc]
  field_simp
  ring

/-- `∫₀^{2π} σ(θ, s) ds = 0` for `θ ∈ [0, 2π]`: `2D^{-1}` kills the constant mode. -/
theorem integral_sawtoothKernel  (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    ∫ s in 0..(2 * π), sawtoothKernel θ s = 0 := by
  have hpi : π ≠ 0 := by exact_mod_cast pi_ne_zero
  have h1 := intervalIntegral_sign_mul (f := fun _ => 1) continuous_const hθ
  simp at h1
  rw [show (sawtoothKernel θ) = fun s => Complex.I * Real.sign (θ - s) - Complex.I / π * (θ - s) by
    funext s
    simp [sawtoothKernel]
    field_simp, intervalIntegral.integral_sub ((intervalIntegrable_sign θ 0 (2 * π)).const_mul _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1,
    intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [show ∫ x in (0 : ℝ)..(2 * π), (x : ℂ) = ((2 * π) ^ 2 / 2) by
    rw [intervalIntegral.integral_ofReal, integral_id]; norm_num]
  simp
  field_simp
  ring

end PolyaNeumann
