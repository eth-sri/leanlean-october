module

public import Mathlib

/-!
# The hyperbolic secant: Fourier transform and Poisson summation

Source: arXiv:1611.09877v2, §4 (Fourier computations), the identity
`1 / cosh(λ m) = (1 / (2 λ)) ∫_ℝ e^{-i m α} / cosh(π α / (2 λ)) dα` and the periodisation
`R(α) = (π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh(π (2 π j + α) / (2 λ))` of `\hat R(m) = 1 / (2 cosh(λ m))`.

The paper obtains the sech transform from the residue theorem.  Here it is obtained from the Beta
integral: for `s = (1 - i ω) / 2`, `B(s, 1 - s) = Γ(s) Γ(1 - s) = π / sin (π s) = π / cosh (π ω / 2)`
(Mathlib: `Complex.Gamma_mul_Gamma_eq_betaIntegral`, `Complex.Gamma_mul_Gamma_one_sub`), and the
substitution `x = 1 / (1 + e^{-2 t})` turns the Beta integral into `∫_ℝ e^{-i ω t} / cosh t dt`.

* `integral_cexp_div_cosh`, `integral_cos_div_cosh`: `∫_ℝ cos(ω t) / cosh t dt = π / cosh(π ω / 2)`;
* `summable_sech_periodic`;
* `periodic_sech_eq_cos_series`: Poisson summation (Mathlib's
  `Real.tsum_eq_tsum_fourier_of_rpow_decay`) gives
  `(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`.
-/

public section

open Real MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.Bethe

section
variable (t : ℝ)
theorem cosh_ge_quarter  : (1 + t ^ 2) / 4 ≤ Real.cosh t := by
  have h1 : Real.cosh t = Real.cosh |t| := by simp
  have h2 := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
  have h3 : 0 < Real.exp (-|t|) := Real.exp_pos _
  have h4 : Real.cosh |t| = (Real.exp |t| + Real.exp (-|t|)) / 2 := Real.cosh_eq _
  have h5 := sq_abs t
  grind

/-- The logistic map `σ(t) = 1 / (1 + e^{-2t})`, a smooth increasing bijection `ℝ → (0,1)`. -/
noncomputable def logistic2  : ℝ := (1 + Real.exp (-2 * t))⁻¹

theorem logistic2_pos  : 0 < logistic2 t := by
  unfold logistic2; positivity

theorem logistic2_lt_one  : logistic2 t < 1 := by
  unfold logistic2
  have := Real.exp_pos (-2 * t)
  rw [inv_lt_one₀ (by positivity)]
  linarith

theorem hasDerivAt_logistic2  :
    HasDerivAt logistic2 (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2) t :=
  ((((hasDerivAt_id' t).const_mul (-2)).exp.const_add 1).inv (by positivity)).congr_deriv (by ring)
end

theorem strictMono_logistic2 : StrictMono logistic2 :=
  strictMono_of_hasDerivAt_pos hasDerivAt_logistic2 fun t => by positivity

theorem image_logistic2 : logistic2 '' (univ : Set ℝ) = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    simp [logistic2_pos, logistic2_lt_one]
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log ((1 - x) / x) / (-2), mem_univ _, ?_⟩
    unfold logistic2
    have : -2 * (Real.log ((1 - x) / x) / (-2)) = Real.log ((1 - x) / x) := by field_simp
    rw [this, Real.exp_log (by positivity)]
    grind

theorem cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (y : ℂ) :
    ((x : ℂ)) ^ y = Complex.exp (Real.log x * y) := by
  rw [Complex.cpow_def_of_ne_zero (by aesop), Complex.ofReal_log hx.le]

theorem logistic2_integrand (ω t : ℝ) :
    ((2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ) : ℂ) *
      (((logistic2 t : ℝ) : ℂ) ^ ((1 - Complex.I * ω) / 2 - 1) *
        (1 - ((logistic2 t : ℝ) : ℂ)) ^ ((1 - (1 - Complex.I * ω) / 2) - 1)) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set a : ℝ := 1 + Real.exp (-2 * t) with ha
  have ha0 : 0 < a := by positivity
  have hea : 0 < Real.exp (-2 * t) := Real.exp_pos _
  have hσ : logistic2 t = a⁻¹ := rfl
  have h1σ : 1 - logistic2 t = Real.exp (-2 * t) * a⁻¹ := by
    grind
  have e1 : (1 - ((logistic2 t : ℝ) : ℂ)) = (((1 - logistic2 t : ℝ)) : ℂ) := by simp
  rw [e1, cpow_ofReal_pos (logistic2_pos t), cpow_ofReal_pos (by simp_all), ← Complex.exp_add]
  have hl1 : Real.log (logistic2 t) = -Real.log a := by simp_all
  have hl2 : Real.log (1 - logistic2 t) = -2 * t - Real.log a := by
    rw [h1σ, Real.log_mul hea.ne' (inv_ne_zero ha0.ne'), Real.log_exp, Real.log_inv]; ring
  have hexp : Complex.exp (((-Real.log a : ℝ) : ℂ) * (s - 1) + ((-2 * t - Real.log a : ℝ) : ℂ) *
      (1 - s - 1)) = (a : ℂ) * Complex.exp (2 * t * s) := by
    have : ((-Real.log a : ℝ) : ℂ) * (s - 1) + ((-2 * t - Real.log a : ℝ) : ℂ) * (1 - s - 1) =
        (Real.log a : ℂ) + 2 * t * s := by push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha0]
  have hX := Complex.exp_ne_zero t
  have e2' : Complex.exp (-2 * (t : ℂ)) = (Complex.exp t)⁻¹ ^ 2 := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    simp
  have e3 : Complex.exp (2 * t * s) = Complex.exp t * Complex.exp (-(Complex.I * ω * t)) := by
    rw [← Complex.exp_add]; grind
  have e4 : (Real.cosh t : ℂ) = (Complex.exp t + (Complex.exp t)⁻¹) / 2 := by
    rw [Complex.ofReal_cosh, Complex.cosh, Complex.exp_neg]
  have e5 : (a : ℂ) = 1 + (Complex.exp t)⁻¹ ^ 2 := by simp_all
  have e6 : (((2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ)) : ℂ) =
      2 * (Complex.exp t)⁻¹ ^ 2 / (1 + (Complex.exp t)⁻¹ ^ 2) ^ 2 := by
    simp_all
  grind

section
variable (ω : ℝ)
theorem betaIntegral_eq_integral_cexp_div_cosh  :
    Complex.betaIntegral ((1 - Complex.I * ω) / 2) (1 - (1 - Complex.I * ω) / 2) =
      ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((1 - s) - 1) with hg
  have h1 : ∫ x in (0:ℝ)..1, g x = ∫ x in Ioo (0:ℝ) 1, g x := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have h2 :=
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (hasDerivAt_logistic2 t).hasDerivWithinAt)
      strictMono_logistic2.injective.injOn g
  rw [image_logistic2] at h2
  have h3 : ∀ t : ℝ, |2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2| • g (logistic2 t) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
    intro t
    rw [abs_of_pos (by positivity), Complex.real_smul, hg]
    exact logistic2_integrand ω t
  simp_all [Complex.betaIntegral]

theorem integral_cexp_div_cosh  :
    ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) =
      ((π / Real.cosh (π * ω / 2) : ℝ) : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  have hsre : 0 < s.re := by simp_all
  have hs1re : 0 < (1 - s).re := by simp [hs]; norm_num
  rw [← betaIntegral_eq_integral_cexp_div_cosh]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hsre hs1re
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul,
    Complex.Gamma_mul_Gamma_one_sub] at h
  have hsin : Complex.sin (π * s) = (Real.cosh (π * ω / 2) : ℂ) := by
    have : (π : ℂ) * s = (π : ℂ) / 2 - ((π * ω / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.sin_pi_div_two_sub, Complex.cos_mul_I, Complex.ofReal_cosh]
  simp_all
end

/-! ### Fourier transform of a rescaled secant -/

open scoped FourierTransform

/-- The (unitary, `e^{-2πi x ξ}`) Fourier transform of `y ↦ c / cosh (b y)` is
`ξ ↦ (c / b) · π / cosh (π² ξ / b)`. -/
theorem fourier_sech (b : ℝ) (hb : 0 < b) (c ξ : ℝ) :
    𝓕 (fun y : ℝ => ((c / Real.cosh (b * y) : ℝ) : ℂ)) ξ =
      (((c / b) * (π / Real.cosh (π ^ 2 * ξ / b)) : ℝ) : ℂ) := by
  rw [fourier_real_eq_integral_exp_smul]
  set ω : ℝ := 2 * π * ξ / b with hω
  have h1 : ∀ v : ℝ, Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) •
      ((c / Real.cosh (b * v) : ℝ) : ℂ) =
      (c : ℂ) * (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) (b * v) := by
    intro v
    have : (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) = -(Complex.I * ω * ((b * v : ℝ) : ℂ)) := by
      have hb' : (b : ℂ) ≠ 0 := by aesop
      rw [hω]; push_cast; field_simp
    rw [this]; push_cast; ring
  simp_rw [h1]
  have key := Measure.integral_comp_mul_left
    (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) b
  rw [integral_const_mul, key, integral_cexp_div_cosh ω]
  have hπ : π * ω / 2 = π ^ 2 * ξ / b := by ring
  rw [hπ, abs_of_pos (inv_pos.mpr hb), Complex.real_smul]
  push_cast
  ring

/-! ### Decay -/

section
variable {k : ℝ} (hk : 0 < k) (C : ℝ)
include hk
theorem isBigO_cocompact_sech  :
    (fun y : ℝ => ((C / Real.cosh (k * y) : ℝ) : ℂ)) =O[cocompact ℝ]
      (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (4 * |C| / k ^ 2) ?_
  filter_upwards [(tendsto_norm_cocompact_atTop).eventually_gt_atTop 0] with y hy
  have hy0 : 0 < |y| := by omega
  have hyne := abs_pos.mp hy0
  have hy2 : 0 < y ^ 2 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hy0.le, Real.rpow_two, sq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy2), abs_div,
    abs_of_pos (Real.cosh_pos _)]
  calc |C| / Real.cosh (k * y) ≤ |C| / (k ^ 2 * y ^ 2 / 4) := by
        gcongr; nlinarith [cosh_ge_quarter (k * y)]
    _ = 4 * |C| / k ^ 2 * (y ^ 2)⁻¹ := by field_simp

end

/-- The terms `1 / cosh (π (2 π j + α) / (2 λ))` are summable over `j ∈ ℤ`. -/
theorem summable_sech_periodic {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Summable (fun j : ℤ => 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
  have hk : 0 < π ^ 2 / lam := by positivity
  set a : ℝ := α / (2 * π) with ha
  have hb := Complex.isBigO_ofReal_left.mp (isBigO_cocompact_sech hk 1)
  have hT : Tendsto (fun n : ℤ => a + (n : ℝ)) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft a).isClosedEmbedding.tendsto_cocompact.comp Int.tendsto_coe_cofinite
  exact summable_of_isBigO (((Real.summable_one_div_int_add_rpow a 2).2 one_lt_two).congr fun n => by
    simp [Real.rpow_neg (abs_nonneg _), add_comm]) ((hb.comp_tendsto hT).congr_left fun n => by grind)

/-! ### Poisson summation -/

section
variable {lam : ℝ} (hlam : 0 < lam)
include hlam
theorem summable_inv_cosh_int (C : ℝ) :
    Summable (fun n : ℤ => C / Real.cosh (lam * (n : ℝ))) := by
  have hb := Complex.isBigO_ofReal_left.mp (isBigO_cocompact_sech hlam C)
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (hb.comp_tendsto Int.tendsto_coe_cofinite)

/-- Poisson summation for the hyperbolic secant:
`(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`. -/
theorem periodic_sech_eq_cos_series (α : ℝ) :
    HasSum (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * α) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)))
      ((π / (2 * lam)) * (∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) - 1 / 2) := by
  have hb : 0 < π ^ 2 / lam := by positivity
  set b : ℝ := π ^ 2 / lam with hbdef
  set c : ℝ := π / (2 * lam) with hcdef
  set f : ℝ → ℂ := fun y => ((c / Real.cosh (b * y) : ℝ) : ℂ) with hfdef
  have hc : Continuous f := by fun_prop (disch := intros; positivity)
  have hf := isBigO_cocompact_sech hb c
  have hF : 𝓕 f = fun ξ => (((1 / 2) / Real.cosh (lam * ξ) : ℝ) : ℂ) := funext fun ξ => by
    rw [fourier_sech b hb, hbdef, hcdef]
    field_simp
  have hFf := hF ▸ isBigO_cocompact_sech hlam (1 / 2)
  set x : ℝ := α / (2 * π) with hx
  have hL : ∑' n : ℤ, f (x + n) =
      ((c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    grind
  -- right side: real parts
  have hterm : ∀ n : ℤ, (𝓕 f n * fourier n (x : UnitAddCircle)).re =
      (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α) := by
    intro n
    rw [congrFun hF (n : ℝ)]
    have : fourier n (x : UnitAddCircle) = Complex.exp (((n * α : ℝ) : ℂ) * Complex.I) := by
      simp
      rw [hx]; push_cast
      field_simp
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hsumC : Summable (fun n : ℤ => 𝓕 f n * fourier n (x : UnitAddCircle)) := by
    refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
    rw [norm_mul, congrFun hF, Complex.norm_real, Real.norm_eq_abs, show ‖fourier n (x : UnitAddCircle)‖ = 1 from Circle.norm_coe _, mul_one, abs_of_pos (by positivity)]
  have hHas : HasSum (fun n : ℤ => (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α)) (c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
    have := Complex.hasSum_re hsumC.hasSum
    rwa [← Real.tsum_eq_tsum_fourier_of_rpow_decay hc one_lt_two hf hFf x, hL, Complex.ofReal_re, funext hterm] at this
  convert (hasSum_nat_add_iff' 1).mpr hHas.nat_add_neg using 1
  · funext n
    push_cast
    rw [mul_neg, Real.cosh_neg, neg_mul, Real.cos_neg]
    ring
  · simp
end

end PottsDiscontinuity.Bethe
