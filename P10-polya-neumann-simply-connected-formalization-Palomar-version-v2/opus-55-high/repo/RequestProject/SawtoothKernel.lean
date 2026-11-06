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

variable {θ : ℝ}

lemma intervalIntegrable_sign (θ a b : ℝ) :
    IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ)) volume a b := by
  refine (MeasureTheory.IntegrableOn.intervalIntegrable ?_)
  refine Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_real_sign.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    rw [Complex.norm_real]
    exact abs_real_sign_le _

lemma intervalIntegral_sign_mul {f : ℝ → ℂ} (hf : Continuous f) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    ∫ s in 0..(2 * π), Real.sign (θ - s) * f s =
      (∫ s in 0..θ, f s) - ∫ s in θ..(2 * π), f s := by
  have hnull : ∀ᵐ s ∂volume, s ≠ θ := by
    simp [ae_iff]
  have h1 : ∫ s in 0..θ, Real.sign (θ - s) * f s = ∫ s in 0..θ, f s := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hnull] with s hs hmem
    rw [Real.sign_of_pos (by grind)]
    simp
  have h2 : ∫ s in θ..(2 * π), Real.sign (θ - s) * f s = -∫ s in θ..(2 * π), f s := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with s hmem
    rw [Real.sign_of_neg (by simp_all)]
    simp
  have hint  :=
    fun a b => (intervalIntegrable_sign θ a b).mul_continuousOn hf.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 θ) (hint θ (2 * π)), h1, h2]
  ring

/-- `∫₀^{2π} σ(θ, s) e^{ins} ds = (2/n) e^{inθ}` for `n ≠ 0` and `θ ∈ [0, 2π]`. -/
theorem integral_sawtoothKernel_mul_exp {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π)) {n : ℤ}
    (hn : n ≠ 0) :
    ∫ s in 0..(2 * π), sawtoothKernel θ s * Complex.exp (n * Complex.I * s) =
      2 / n * Complex.exp (n * Complex.I * θ) := by
  set c : ℂ := n * Complex.I with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by positivity) Complex.I_ne_zero
  have hexp2π : Complex.exp (c * (2 * π : ℝ)) = 1 := by
    rw [show n * Complex.I * (2 * π : ℝ) = n * (2 * π * Complex.I) by
      push_cast; ring]
    norm_num
  have hcont : Continuous fun s : ℝ => Complex.exp (c * s) := by fun_prop
  -- integrals of the exponential
  have hE1 : ∫ s in 0..θ, Complex.exp (c * s) = (Complex.exp (c * θ) - 1) / c := by
    simp [integral_exp_mul_complex hc0]
  have hE2 : ∫ s in θ..(2 * π), Complex.exp (c * s) = (1 - Complex.exp (c * θ)) / c := by
    rw [integral_exp_mul_complex hc0, hexp2π]
  have hE3 : ∫ s in 0..(2 * π), Complex.exp (c * s) = 0 := by
    rw [integral_exp_mul_complex hc0, hexp2π]; simp
  -- `∫ s e^{cs} = 2π / c`
  have hE4 : ∫ s in 0..(2 * π), s * Complex.exp (c * s) = 2 * π / c := by
    have hd : ∀ x ∈ Set.uIcc 0 (2 * π),
        HasDerivAt (fun s : ℝ => Complex.exp (c * s) / c) (Complex.exp (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => c * s) c x := by
        simpa using (Complex.ofRealCLM.hasDerivAt ).const_mul c
      have := (h1.cexp).div_const c
      simp_all
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => by simpa using (hasDerivAt_id x).ofReal_comp) hd
      (intervalIntegrable_const) (hcont.intervalIntegrable _ _)]
    simp only [one_mul]
    rw [intervalIntegral.integral_div, hE3, hexp2π]
    push_cast
    ring
  -- assemble
  have hsplit : ∫ s in 0..(2 * π), sawtoothKernel θ s * Complex.exp (c * s) =
      (Complex.I * ∫ s in 0..(2 * π), Real.sign (θ - s) * Complex.exp (c * s)) -
      Complex.I / π * ((θ * ∫ s in 0..(2 * π), Complex.exp (c * s)) -
        ∫ s in 0..(2 * π), s * Complex.exp (c * s)) := by
    have hi1 : IntervalIntegrable (fun s  => Complex.I *
        (Real.sign (θ - s) * Complex.exp (c * s))) volume 0 (2 * π) :=
      ((intervalIntegrable_sign θ 0 (2 * π)).mul_continuousOn hcont.continuousOn).const_mul _
    have hi2 : IntervalIntegrable (fun s  => Complex.I / π *
        (θ * Complex.exp (c * s) - s * Complex.exp (c * s))) volume 0 (2 * π) := (Continuous.intervalIntegrable (by fun_prop) _ _)
    have e : (fun s => sawtoothKernel θ s * Complex.exp (c * s)) = fun s =>
        Complex.I * (Real.sign (θ - s) * Complex.exp (c * s)) -
        Complex.I / π * (θ * Complex.exp (c * s) - s * Complex.exp (c * s)) := by
      funext s
      simp only [sawtoothKernel]
      field_simp
    have h3 : IntervalIntegrable (fun s  => θ * Complex.exp (c * s)) volume 0 (2 * π) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have h4 : IntervalIntegrable (fun s  => s * Complex.exp (c * s)) volume 0 (2 * π) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    simp_all
  rw [hsplit, intervalIntegral_sign_mul hcont hθ, hE1, hE2, hE3, hE4]
  field_simp
  ring

/-- `∫₀^{2π} σ(θ, s) ds = 0` for `θ ∈ [0, 2π]`: `2D^{-1}` kills the constant mode. -/
theorem integral_sawtoothKernel (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    ∫ s in 0..(2 * π), sawtoothKernel θ s = 0 := by
  have h1 := intervalIntegral_sign_mul (f := fun _ => 1) continuous_const hθ
  simp  at h1
  have e : (sawtoothKernel θ) = fun s =>
      Complex.I * Real.sign (θ - s) - Complex.I / π * (θ - s) := by
    funext s
    simp only [sawtoothKernel]
    field_simp
  rw [e, intervalIntegral.integral_sub ((intervalIntegrable_sign θ 0 (2 * π)).const_mul _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1,
    intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hid : ∫ x in 0..(2 * π), (x : ℂ) = (2 * π) ^ 2 / 2 := by
    rw [intervalIntegral.integral_ofReal]; norm_num
  rw [hid]
  simp 
  field_simp
  ring

end PolyaNeumann
