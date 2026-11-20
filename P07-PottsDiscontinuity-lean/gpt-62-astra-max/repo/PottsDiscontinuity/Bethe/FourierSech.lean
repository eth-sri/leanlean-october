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

@[expose] public section

open Real MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.Bethe

section
variable (t : ℝ)
include t

theorem cosh_ge_quarter : (1 + t ^ 2) / 4 ≤ Real.cosh t := by
  have h1 := (Real.cosh_abs t).symm
  grind [Real.quadratic_le_exp_of_nonneg, Real.exp_pos, Real.cosh_eq, sq_abs]

theorem one_div_cosh_le : 1 / Real.cosh t ≤ 4 * (1 + t ^ 2)⁻¹ := by
  calc _ ≤ 1 / ((1 + t ^ 2) / 4) := one_div_le_one_div_of_le (by positivity) (cosh_ge_quarter t)
    _ = _ := by field_simp

/-- The logistic map `σ(t) = 1 / (1 + e^{-2t})`, a smooth increasing bijection `ℝ → (0,1)`. -/
noncomputable def logistic2 : ℝ := (1 + Real.exp (-2 * t))⁻¹

theorem logistic2_pos : 0 < logistic2 t := by
  unfold logistic2; positivity

theorem logistic2_lt_one : logistic2 t < 1 := by
  unfold logistic2
  have := Real.exp_pos (-2 * t)
  rw [inv_lt_one₀ (by positivity)]
  linarith

theorem hasDerivAt_logistic2 :
    HasDerivAt logistic2 (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => -2 * t) (-2) t := by
    simpa using (hasDerivAt_id t).const_mul (-2)
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := by
    exact h1.exp.const_add 1
  exact (h2.inv (by positivity)).congr_deriv (by ring)

end

theorem strictMono_logistic2 : StrictMono logistic2 := by
  refine strictMono_of_hasDerivAt_pos hasDerivAt_logistic2 fun t => ?_
  positivity

theorem image_logistic2 : logistic2 '' univ = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨logistic2_pos t, logistic2_lt_one t⟩
  let logValue := Real.log ((1 - x) / x)
  · rintro ⟨h0, h1⟩
    refine ⟨logValue / (-2), mem_univ _, ?_⟩
    unfold logistic2
    have : -2 * (logValue / (-2)) = logValue := by field_simp
    rw [this, Real.exp_log (div_pos (by linarith) h0)]
    field_simp
    ring

theorem cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (y : ℂ) :
    x ^ y = Complex.exp (Real.log x * y) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

theorem logistic2_integrand (ω t : ℝ) :
    (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ) *
      ((logistic2 t) ^ ((1 - Complex.I * ω) / 2 - 1) *
        (1 - (logistic2 t)) ^ ((1 - (1 - Complex.I * ω) / 2) - 1)) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set a : ℝ := 1 + Real.exp (-2 * t) with ha
  have ha0 : 0 < a := by positivity
  have hea : 0 < Real.exp (-2 * t) := Real.exp_pos _
  have hσ : logistic2 t = a⁻¹ := rfl
  have h1σ : 1 - logistic2 t = Real.exp (-2 * t) * a⁻¹ := by
    grind
  have e1 : (1 - (logistic2 t)) = (↑(1 - logistic2 t) : ℂ) := by push_cast; ring
  rw [e1, cpow_ofReal_pos (logistic2_pos t), cpow_ofReal_pos (by nlinarith), ← Complex.exp_add]
  have hl1 : Real.log (logistic2 t) = -Real.log a := by simp_all
  have hl2 : Real.log (1 - logistic2 t) = -2 * t - Real.log a := by
    rw [h1σ, Real.log_mul hea.ne' (inv_ne_zero ha0.ne'), Real.log_exp, Real.log_inv]; ring
  have hexp : Complex.exp ((-Real.log a : ℝ) * (s - 1) + ↑(-2 * t - Real.log a) *
      (1 - s - 1)) = a * Complex.exp (2 * t * s) := by
    have : (-Real.log a : ℝ) * (s - 1) + ↑(-2 * t - Real.log a) * (1 - s - 1) =
        (Real.log a) + 2 * t * s := by push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha0]
  have hX := Complex.exp_ne_zero t
  have e2' : Complex.exp (-2 * t) = (Complex.exp t)⁻¹ ^ 2 := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    ring
  have e3 : Complex.exp (2 * t * s) = Complex.exp t * Complex.exp (-(Complex.I * ω * t)) := by
    rw [← Complex.exp_add]; grind
  have e4 : (Real.cosh t) = (Complex.exp t + (Complex.exp t)⁻¹) / 2 := by
    rw [Complex.ofReal_cosh, Complex.cosh, Complex.exp_neg]
  have e5 : a = 1 + (Complex.exp t)⁻¹ ^ 2 := by simp_all
  have e6 : (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ) =
      2 * (Complex.exp t)⁻¹ ^ 2 / (1 + (Complex.exp t)⁻¹ ^ 2) ^ 2 := by
    push_cast; grind
  grind

section
variable (ω : ℝ)

theorem betaIntegral_eq_integral_cexp_div_cosh :
    Complex.betaIntegral ((1 - Complex.I * ω) / 2) (1 - (1 - Complex.I * ω) / 2) =
      ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set g : ℝ → ℂ := fun x => x ^ (s - 1) * (1 - x) ^ ((1 - s) - 1) with hg
  have h1 : ∫ x in 0..1, g x = ∫ x in Ioo 0 1, g x := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have h2 :=
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (hasDerivAt_logistic2 t).hasDerivWithinAt)
      strictMono_logistic2.injective.injOn g
  rw [image_logistic2] at h2
  have h3 : ∀ t : ℝ, |2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2| • g (logistic2 t) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t) := by
    intro t
    rw [abs_of_pos (by positivity), Complex.real_smul, hg]
    exact logistic2_integrand ω t
  simp_all [h3, h1, h2, setIntegral_univ, Complex.betaIntegral]

theorem integral_cexp_div_cosh :
    ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t) =
      ↑(π / Real.cosh (π * ω / 2)) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  have hsre : 0 < s.re := by simp_all
  have hs1re : 0 < (1 - s).re := by simp [hs]; norm_num
  rw [← betaIntegral_eq_integral_cexp_div_cosh]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hsre hs1re
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul,
    Complex.Gamma_mul_Gamma_one_sub] at h
  have hsin : Complex.sin (π * s) = (Real.cosh (π * ω / 2)) := by
    have : (π) * s = (π) / 2 - ↑(π * ω / 2) * Complex.I := by
      push_cast; ring
    rw [this, Complex.sin_pi_div_two_sub, Complex.cos_mul_I, Complex.ofReal_cosh]
  simp_all

end

/-! ### Fourier transform of a rescaled secant -/

open scoped FourierTransform

/-- The (unitary, `e^{-2πi x ξ}`) Fourier transform of `y ↦ c / cosh (b y)` is
`ξ ↦ (c / b) · π / cosh (π² ξ / b)`. -/
theorem fourier_sech (b : ℝ) (hb : 0 < b) (c ξ : ℝ) :
    𝓕 (fun y : ℝ => (↑(c / Real.cosh (b * y)) : ℂ)) ξ =
      ↑((c / b) * (π / Real.cosh (π ^ 2 * ξ / b))) := by
  rw [fourier_real_eq_integral_exp_smul]
  set ω : ℝ := 2 * π * ξ / b with hω
  have h1 : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) •
      ↑(c / Real.cosh (b * v)) =
      c * (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t)) (b * v) := by
    intro v
    have : (↑(-2 * π * v * ξ) * Complex.I) = -(Complex.I * ω * (b * v)) := by
      have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
      rw [hω]; push_cast; field_simp
    rw [this]; push_cast; ring
  simp_rw [h1]
  have key := Measure.integral_comp_mul_left
    (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t)) b
  beta_reduce at key
  rw [integral_const_mul, key, integral_cexp_div_cosh ω]
  have hπ : π * ω / 2 = π ^ 2 * ξ / b := by grind
  rw [hπ, abs_of_pos (inv_pos.mpr hb), Complex.real_smul]
  push_cast
  ring

/-! ### Decay -/

section
variable {k : ℝ} (hk : 0 < k) (C : ℝ)
include hk

theorem isBigO_cocompact_sech :
    (fun y : ℝ => (↑(C / Real.cosh (k * y)) : ℂ)) =O[cocompact ℝ]
      (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (4 * |C| / k ^ 2) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop 0] with y hy
  have hy0 : 0 < |y| := hy
  have hyne := abs_pos.mp hy0
  have hy2 : 0 < y ^ 2 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hy0.le, Real.rpow_two, sq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy2), abs_div,
    abs_of_pos (Real.cosh_pos _)]
  have h1 := one_div_cosh_le (k * y)
  have h2 : (1 + (k * y) ^ 2)⁻¹ ≤ (k ^ 2 * y ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    linarith
  calc _ = |C| * (1 / Real.cosh (k * y)) := by ring
    _ ≤ |C| * (4 * (k ^ 2 * y ^ 2)⁻¹) := by
        gcongr
        grind
    _ = _ := by field_simp

theorem isBigO_cocompact_sech_real :
    (fun y : ℝ => C / Real.cosh (k * y)) =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := Complex.isBigO_ofReal_left.mp (isBigO_cocompact_sech hk C)

end

/-- The terms `1 / cosh (π (2 π j + α) / (2 λ))` are summable over `j ∈ ℤ`. -/
theorem summable_sech_periodic {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Summable (fun j : ℤ => 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
  have hk : 0 < π ^ 2 / lam := by positivity
  set a : ℝ := α / (2 * π) with ha
  have hT : Tendsto (fun n : ℤ => a + n) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft a).isClosedEmbedding.tendsto_cocompact.comp Int.tendsto_coe_cofinite
  have hg : Summable (fun n : ℤ => |a + n| ^ (-(2 : ℝ))) := by
    have := (Real.summable_one_div_int_add_rpow a 2).2 one_lt_two
    simp_all [add_comm, one_div]
  refine summable_of_isBigO hg ?_
  have := (isBigO_cocompact_sech_real hk 1).comp_tendsto hT
  refine this.congr_left fun n => ?_
  grind

/-! ### Poisson summation -/

variable {lam : ℝ} (hlam : 0 < lam)
include hlam

theorem summable_inv_cosh_int (C : ℝ) :
    Summable (fun n : ℤ => C / Real.cosh (lam * n)) := summable_of_isBigO (summable_abs_int_rpow one_lt_two) (Asymptotics.IsBigO.comp_tendsto (isBigO_cocompact_sech_real hlam C) Int.tendsto_coe_cofinite)

theorem fourier_sech_periodic_aux (ξ : ℝ) :
    𝓕 (fun y : ℝ => (↑(π / (2 * lam) / Real.cosh (π ^ 2 / lam * y)) : ℂ)) ξ =
      ↑((1 / 2) / Real.cosh (lam * ξ)) := by
  rw [fourier_sech _ (by positivity)]
  field_simp

/-- Poisson summation for the hyperbolic secant:
`(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`. -/
theorem periodic_sech_eq_cos_series (α : ℝ) :
    HasSum (fun n : ℕ => Real.cos (↑(n + 1) * α) / Real.cosh (lam * ↑(n + 1)))
      ((π / (2 * lam)) * (∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) - 1 / 2) := by
  have hb : 0 < π ^ 2 / lam := by positivity
  set b : ℝ := π ^ 2 / lam with hbdef
  set c : ℝ := π / (2 * lam) with hcdef
  set f : ℝ → ℂ := fun y => ↑(c / Real.cosh (b * y)) with hfdef
  have hF : 𝓕 f = fun ξ => ↑((1 / 2) / Real.cosh (lam * ξ)) := by
    funext ξ
    exact fourier_sech_periodic_aux hlam ξ
  set x : ℝ := α / (2 * π) with hx
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay (by
    exact Complex.continuous_ofReal.comp (continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      fun y => (Real.cosh_pos _).ne')) one_lt_two (isBigO_cocompact_sech hb c) (by rw [hF]; solve_by_elim [isBigO_cocompact_sech]) x
  -- left side
  have hL : ∑' n : ℤ, f (x + n) =
      ↑(c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    grind
  -- right side: real parts
  have hterm : ∀ n : ℤ, (𝓕 f n * fourier n (x : UnitAddCircle)).re =
      (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α) := by
    intro n
    rw [congrFun hF _]
    have : fourier n (x : UnitAddCircle) = Complex.exp (↑(n * α) * Complex.I) := by
      rw [fourier_coe_apply]
      congr 1
      rw [hx]; push_cast
      field_simp
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  set F : ℤ → ℝ := fun n => (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α) with hFdef
  have hsumF : Summable F := by
    refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
    rw [hFdef]
    simp only [norm_mul, Real.norm_eq_abs]
    rw [(abs_of_pos (by positivity))]
    calc _
        ≤ (1 / 2) / Real.cosh (lam * n) * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  have hsumC : Summable (fun n : ℤ => 𝓕 f n * fourier n (x : UnitAddCircle)) := by
    refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
    rw [norm_mul, congrFun hF _, Complex.norm_real, Real.norm_eq_abs]
    have : ‖fourier n (x : UnitAddCircle)‖ = 1 := Circle.norm_coe _
    rw [this, mul_one, abs_of_pos (by positivity)]
  have hRe := congrArg Complex.re hP
  rw [hL, Complex.ofReal_re, Complex.re_tsum hsumC] at hRe
  simp_rw [hterm] at hRe
  have hHas : HasSum F (c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
    rw [hRe]; exact hsumF.hasSum
  convert ((hasSum_nat_add_iff' 1).mpr hHas.nat_add_neg) using 1
  · funext n
    simp only [hFdef]
    push_cast
    rw [mul_neg, Real.cosh_neg, neg_mul, Real.cos_neg]
    ring
  · simp [hFdef]

end PottsDiscontinuity.Bethe
