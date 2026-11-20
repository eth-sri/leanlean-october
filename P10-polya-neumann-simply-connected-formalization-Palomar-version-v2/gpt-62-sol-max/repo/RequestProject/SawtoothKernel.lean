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

/-- Splitting at the sign discontinuity gives both integrability and the signed integral. -/
lemma sign_mul_intervalIntegral {f : ℝ → ℂ} {a t b : ℝ} (ha : a ≤ t) (hb : t ≤ b)
    (h₁ : IntervalIntegrable f volume a t) (h₂ : IntervalIntegrable f volume t b) :
    IntervalIntegrable (fun s => (Real.sign (t - s) : ℂ) * f s) volume a b ∧
      (∫ s in a..b, (Real.sign (t - s) : ℂ) * f s) =
        (∫ s in a..t, f s) - ∫ s in t..b, f s := by
  have hn : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by simp [ae_iff]
  have e₁ : ∀ᵐ s ∂volume.restrict (Set.uIoc a t), (Real.sign (t - s) : ℂ) * f s = f s := by
    rw [ae_restrict_iff' measurableSet_uIoc, Set.uIoc_of_le ha]
    filter_upwards [hn] with s hs hm
    simp [Real.sign_of_pos (sub_pos.mpr (lt_of_le_of_ne hm.2 hs))]
  have e₂ : ∀ᵐ s ∂volume.restrict (Set.uIoc t b), (Real.sign (t - s) : ℂ) * f s = -f s := by
    rw [ae_restrict_iff' measurableSet_uIoc, Set.uIoc_of_le hb]
    exact .of_forall fun s hs => by simp [Real.sign_of_neg (sub_neg.mpr hs.1)]
  have i₁ := h₁.congr_ae (Filter.EventuallyEq.symm e₁)
  have i₂ := h₂.neg.congr_ae (Filter.EventuallyEq.symm e₂)
  refine ⟨i₁.trans i₂, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals i₁ i₂,
    intervalIntegral.integral_congr_ae_restrict e₁,
    intervalIntegral.integral_congr_ae_restrict e₂, intervalIntegral.integral_neg, sub_eq_add_neg]

section

variable {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π))
include θ hθ

/-- `∫₀^{2π} σ(θ, s) e^{ins} ds = (2/n) e^{inθ}` for `n ≠ 0` and `θ ∈ [0, 2π]`. -/
theorem integral_sawtoothKernel_mul_exp  {n : ℤ}
    (hn : n ≠ 0) :
    ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * Complex.exp (n * Complex.I * s) =
      2 / n * Complex.exp (n * Complex.I * θ) := by
  set c : ℂ := n * Complex.I with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by positivity) Complex.I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by simp
  have hn' : (n : ℂ) ≠ 0 := by positivity
  have hexp2π : Complex.exp (c * (2 * π : ℝ)) = 1 := by
    rw [show (n : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ) = n * (2 * π * Complex.I) by
      push_cast; ring]
    simp
  have hcont : Continuous fun s : ℝ => Complex.exp (c * s) := by fun_prop
  obtain ⟨his, hs⟩ := sign_mul_intervalIntegral hθ.1 hθ.2
    (hcont.intervalIntegrable 0 θ) (hcont.intervalIntegrable θ (2 * π))
  -- integrals of the exponential
  have hE1 : ∫ s in (0 : ℝ)..θ, Complex.exp (c * s) = (Complex.exp (c * θ) - 1) / c := by
    rw [integral_exp_mul_complex hc0]; simp
  have hE2 : ∫ s in θ..(2 * π), Complex.exp (c * s) = (1 - Complex.exp (c * θ)) / c := by
    rw [integral_exp_mul_complex hc0, hexp2π]
  have hE3 : ∫ s in (0 : ℝ)..(2 * π), Complex.exp (c * s) = 0 := by
    rw [integral_exp_mul_complex hc0, hexp2π]; simp
  -- `∫ s e^{cs} = 2π / c`
  have hE4 : ∫ s in (0 : ℝ)..(2 * π), (s : ℂ) * Complex.exp (c * s) = 2 * π / c := by
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * π),
        HasDerivAt (fun s : ℝ => Complex.exp (c * s) / c) (Complex.exp (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c x := by
        simpa using HasDerivAt.const_mul c (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM)
      have := (h1.cexp).div_const c
      simp_all
    have hu : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x :=
      fun x _ => HasDerivAt.ofReal_comp (hasDerivAt_id x)
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hd
      (intervalIntegrable_const) (hcont.intervalIntegrable _ _)]
    simp only [one_mul]
    rw [intervalIntegral.integral_div, hE3, hexp2π]
    push_cast
    ring
  -- assemble
  have hsplit : ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * Complex.exp (c * s) =
      (Complex.I * ∫ s in (0 : ℝ)..(2 * π), (Real.sign (θ - s) : ℂ) * Complex.exp (c * s)) -
      Complex.I / π * ((θ * ∫ s in (0 : ℝ)..(2 * π), Complex.exp (c * s)) -
        ∫ s in (0 : ℝ)..(2 * π), (s : ℂ) * Complex.exp (c * s)) := by
    have hi1 : IntervalIntegrable (fun s : ℝ => Complex.I *
        ((Real.sign (θ - s) : ℂ) * Complex.exp (c * s))) volume 0 (2 * π) :=
      his.const_mul _
    have hi2 : IntervalIntegrable (fun s : ℝ => Complex.I / π *
        ((θ : ℂ) * Complex.exp (c * s) - (s : ℂ) * Complex.exp (c * s))) volume 0 (2 * π) := by
      exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    have e : (fun s => sawtoothKernel θ s * Complex.exp (c * s)) = fun s =>
        Complex.I * ((Real.sign (θ - s) : ℂ) * Complex.exp (c * s)) -
        Complex.I / π * ((θ : ℂ) * Complex.exp (c * s) - (s : ℂ) * Complex.exp (c * s)) := by
      funext s
      simp  [sawtoothKernel]
      field_simp
    have h3 : IntervalIntegrable (fun s : ℝ => (θ : ℂ) * Complex.exp (c * s)) volume 0 (2 * π) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have h4 : IntervalIntegrable (fun s : ℝ => (s : ℂ) * Complex.exp (c * s)) volume 0 (2 * π) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    rw [e, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub h3 h4,
      intervalIntegral.integral_const_mul]
  rw [hsplit, hs, hE1, hE2, hE3, hE4]
  rw [hc]
  field_simp
  ring

/-- `∫₀^{2π} σ(θ, s) ds = 0` for `θ ∈ [0, 2π]`: `2D^{-1}` kills the constant mode. -/
theorem integral_sawtoothKernel  :
    ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s = 0 := by
  have hpi : (π : ℂ) ≠ 0 := by simp
  obtain ⟨hi, h1⟩ := sign_mul_intervalIntegral (f := fun _ => (1 : ℂ)) hθ.1 hθ.2
    intervalIntegrable_const intervalIntegrable_const
  simp only [mul_one] at hi h1
  have e : (fun s => sawtoothKernel θ s) = fun s =>
      Complex.I * (Real.sign (θ - s) : ℂ) - Complex.I / π * ((θ : ℂ) - (s : ℂ)) := by
    grind [sawtoothKernel]
  have hi1 : IntervalIntegrable (fun s : ℝ => Complex.I * (Real.sign (θ - s) : ℂ))
      volume 0 (2 * π) := hi.const_mul _
  rw [e, intervalIntegral.integral_sub hi1 (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1,
    intervalIntegral.integral_sub intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hid : ∫ x in (0 : ℝ)..(2 * π), (x : ℂ) = ((2 * π) ^ 2 / 2 : ℝ) := by
    rw [intervalIntegral.integral_ofReal, integral_id]; norm_num
  rw [hid]
  simp only [intervalIntegral.integral_const, Complex.real_smul, mul_one]
  push_cast
  field_simp
  ring

end

end PolyaNeumann
