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

theorem cosh_ge_quarter : (1 + t ^ 2) / 4 ≤ Real.cosh t := by
  have h1 : Real.cosh t = Real.cosh |t| := (Real.cosh_abs t).symm
  have h2 := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
  have h3 : 0 < Real.exp (-|t|) := Real.exp_pos _
  have h4 : Real.cosh |t| = (Real.exp |t| + Real.exp (-|t|)) / 2 := Real.cosh_eq _
  grind [sq_abs]

/-- The logistic substitution, written using the denominator shared by both tails. -/
noncomputable def logistic2 : ℝ := Real.exp t / (2 * Real.cosh t)

private theorem logistic2_compl : 1 - logistic2 t = Real.exp (-t) / (2 * Real.cosh t) := by
  rw [logistic2, Real.cosh_eq]
  field_simp
  ring

private theorem logistic2_eq_inv : logistic2 t = (1 + Real.exp (-2 * t))⁻¹ := by
  rw [logistic2, Real.cosh_eq, show -2 * t = -t + -t by ring, Real.exp_add, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

theorem hasDerivAt_logistic2 : HasDerivAt logistic2 (1 / (2 * Real.cosh t ^ 2)) t := by
  have h := (Real.hasDerivAt_exp t).div ((Real.hasDerivAt_cosh t).const_mul 2) (by positivity)
  refine h.congr_deriv ?_
  rw [show Real.exp t * (2 * Real.cosh t) - Real.exp t * (2 * Real.sinh t) =
    2 * (Real.exp t * (Real.cosh t - Real.sinh t)) by ring, Real.cosh_sub_sinh, ← Real.exp_add]
  simp
  ring

end

private theorem image_logistic2 : logistic2 '' (univ : Set ℝ) = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    refine ⟨by unfold logistic2; positivity, sub_pos.mp ?_⟩
    rw [logistic2_compl]
    positivity
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log ((1 - x) / x) / (-2), mem_univ _, ?_⟩
    rw [logistic2_eq_inv, show (-2 : ℝ) * (Real.log ((1 - x) / x) / -2) = _ by ring,
      Real.exp_log (by positivity)]
    field_simp
    ring

theorem cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (y : ℂ) :
    ((x : ℂ)) ^ y = Complex.exp (Real.log x * y) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

private theorem logistic2_integrand (ω t : ℝ) :
    (↑(1 / (2 * Real.cosh t ^ 2) : ℝ) : ℂ) *
      ((logistic2 t : ℂ) ^ ((1 - Complex.I * ω) / 2 - 1) *
        (1 - (logistic2 t : ℂ)) ^ ((1 - (1 - Complex.I * ω) / 2) - 1)) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  let a := 2 * Real.cosh t
  have ha : 0 < a := by positivity
  have hc : (Real.cosh t : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos t).ne'
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, logistic2_compl,
    show logistic2 t = Real.exp t / a from rfl,
    show 2 * Real.cosh t = a from rfl,
    cpow_ofReal_pos (by positivity), cpow_ofReal_pos (by positivity),
    Real.log_div (Real.exp_ne_zero _) ha.ne', Real.log_div (Real.exp_ne_zero _) ha.ne',
    Real.log_exp, Real.log_exp, ← Complex.exp_add]
  simp only [Complex.ofReal_one]
  have he : ((t - Real.log a : ℝ) : ℂ) * ((1 - Complex.I * ω) / 2 - 1) +
      ((-t - Real.log a : ℝ) : ℂ) * (1 - (1 - Complex.I * ω) / 2 - 1) =
      (Real.log a : ℂ) + -(Complex.I * ω * t) := by push_cast; ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha]
  dsimp [a]
  push_cast
  field_simp

theorem betaIntegral_eq_integral_cexp_div_cosh (ω : ℝ) :
    Complex.betaIntegral ((1 - Complex.I * ω) / 2) (1 - (1 - Complex.I * ω) / 2) =
      ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← image_logistic2, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (hasDerivAt_logistic2 t).hasDerivWithinAt)
      (strictMono_of_hasDerivAt_pos hasDerivAt_logistic2 fun t => by positivity).injective.injOn,
    setIntegral_univ]
  refine integral_congr_ae (.of_forall fun t => ?_)
  dsimp only
  rw [abs_of_pos (by positivity), Complex.real_smul, logistic2_integrand]

theorem integral_cexp_div_cosh (ω : ℝ) :
    ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) =
      ((π / Real.cosh (π * ω / 2) : ℝ) : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  have hsre : 0 < s.re := by simp_all
  have hs1re : 0 < (1 - s).re := by simp [hs]; norm_num
  rw [← betaIntegral_eq_integral_cexp_div_cosh]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hsre hs1re
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul,
    Complex.Gamma_mul_Gamma_one_sub] at h
  rw [← h]
  have hsin : Complex.sin (π * s) = (Real.cosh (π * ω / 2) : ℂ) := by
    have : (π : ℂ) * s = (π : ℂ) / 2 - ((π * ω / 2 : ℝ) : ℂ) * Complex.I := by
      simp; ring
    simp [this, Complex.sin_pi_div_two_sub, Complex.cos_mul_I]
  rw [hsin]
  push_cast
  ring

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
    simp only [smul_eq_mul]
    have : (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) = -(Complex.I * ω * ((b * v : ℝ) : ℂ)) := by
      have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
      rw [hω]; push_cast; field_simp
    rw [this]; push_cast; ring
  simp_rw [h1]
  have key := Measure.integral_comp_mul_left
    (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) b
  beta_reduce at key
  rw [integral_const_mul, key, integral_cexp_div_cosh ω]
  have hπ : π * ω / 2 = π ^ 2 * ξ / b := by rw [hω]; field_simp
  rw [hπ]
  simp [abs_of_pos (inv_pos.mpr hb)]
  ring

/-! ### Decay -/

theorem isBigO_cocompact_sech {k : ℝ} (hk : 0 < k) (C : ℝ) :
    (fun y : ℝ => ((C / Real.cosh (k * y) : ℝ) : ℂ)) =O[cocompact ℝ]
      (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (4 * |C| / k ^ 2) ?_
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_gt_atTop 0] with y hy
  have hy0 : 0 < |y| := by simpa using hy
  have hyne : y ≠ 0 := abs_pos.mp hy0
  have hy2 : 0 < y ^ 2 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hy0.le, Real.rpow_two, sq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy2), abs_div,
    abs_of_pos (Real.cosh_pos _)]
  have hden : 0 < (k * y) ^ 2 / 4 := by positivity
  calc
    _ ≤ |C| / ((k * y) ^ 2 / 4) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hden (by linarith [cosh_ge_quarter (k * y)])
    _ = _ := by field_simp

theorem isBigO_cocompact_sech_real {k : ℝ} (hk : 0 < k) (C : ℝ) :
    (fun y : ℝ => C / Real.cosh (k * y)) =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
  have := isBigO_cocompact_sech hk C
  exact Complex.isBigO_ofReal_left.mp this

/-- The terms `1 / cosh (π (2 π j + α) / (2 λ))` are summable over `j ∈ ℤ`. -/
theorem summable_sech_periodic {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Summable (fun j : ℤ => 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
  have hk : 0 < π ^ 2 / lam := by positivity
  set a : ℝ := α / (2 * π) with ha
  have hpi := Real.pi_pos
  have hb := isBigO_cocompact_sech_real hk 1
  have hT : Tendsto (fun n : ℤ => a + (n : ℝ)) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft a).isClosedEmbedding.tendsto_cocompact.comp Int.tendsto_coe_cofinite
  have hg : Summable (fun n : ℤ => |a + (n : ℝ)| ^ (-(2 : ℝ))) := by
    have := (Real.summable_one_div_int_add_rpow a 2).2 one_lt_two
    refine this.congr fun n => ?_
    simp [add_comm]
  refine summable_of_isBigO hg ?_
  have := hb.comp_tendsto hT
  refine this.congr_left fun n => ?_
  simp only [Function.comp_apply]
  congr 2
  rw [ha]
  field_simp
  ring

/-! ### Poisson summation -/

theorem summable_inv_cosh_int {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    Summable (fun n : ℤ => C / Real.cosh (lam * (n : ℝ))) := by
  have hb := isBigO_cocompact_sech_real hlam C
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (hb.comp_tendsto Int.tendsto_coe_cofinite)

theorem fourier_sech_periodic_aux {lam : ℝ} (hlam : 0 < lam) (ξ : ℝ) :
    𝓕 (fun y : ℝ => ((π / (2 * lam) / Real.cosh (π ^ 2 / lam * y) : ℝ) : ℂ)) ξ =
      (((1 / 2) / Real.cosh (lam * ξ) : ℝ) : ℂ) := by
  rw [fourier_sech (π ^ 2 / lam) (by positivity)]
  congr 1
  have : π ^ 2 * ξ / (π ^ 2 / lam) = lam * ξ := by field_simp
  rw [this]
  field_simp

/-- Poisson summation for the hyperbolic secant:
`(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`. -/
theorem periodic_sech_eq_cos_series {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    HasSum (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * α) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)))
      ((π / (2 * lam)) * (∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) - 1 / 2) := by
  have hpi := Real.pi_pos
  have hb : 0 < π ^ 2 / lam := by positivity
  set b : ℝ := π ^ 2 / lam with hbdef
  set c : ℝ := π / (2 * lam) with hcdef
  set f : ℝ → ℂ := fun y => ((c / Real.cosh (b * y) : ℝ) : ℂ) with hfdef
  have hc : Continuous f := by
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      fun y => (Real.cosh_pos _).ne'
  have hf := isBigO_cocompact_sech hb c
  have hF : 𝓕 f = fun ξ => (((1 / 2) / Real.cosh (lam * ξ) : ℝ) : ℂ) := by
    funext ξ
    exact fourier_sech_periodic_aux hlam ξ
  have hFf : 𝓕 f =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
    simpa [hF] using isBigO_cocompact_sech hlam (1 / 2)
  set x : ℝ := α / (2 * π) with hx
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hc one_lt_two hf hFf x
  -- left side
  have hL : ∑' n : ℤ, f (x + n) =
      ((c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [hfdef]
    have : b * (x + (n : ℝ)) = π * (2 * π * n + α) / (2 * lam) := by
      rw [hbdef, hx]; field_simp; ring
    rw [this, mul_one_div]
  -- right side: real parts
  have hterm : ∀ n : ℤ, (𝓕 f n * fourier n (x : UnitAddCircle)).re =
      (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α) := by
    intro n
    rw [congrFun hF (n : ℝ)]
    have : fourier n (x : UnitAddCircle) = Complex.exp (((n * α : ℝ) : ℂ) * Complex.I) := by
      rw [fourier_coe_apply]
      congr 1
      rw [hx]; push_cast
      field_simp
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  set F : ℤ → ℝ := fun n => (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α) with hFdef
  have hsumC : Summable (fun n : ℤ => 𝓕 f n * fourier n (x : UnitAddCircle)) := by
    refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
    rw [norm_mul, congrFun hF (n : ℝ), Complex.norm_real, Real.norm_eq_abs]
    have : ‖fourier n (x : UnitAddCircle)‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    rw [this, mul_one, abs_of_pos (by positivity)]
  have hC := hsumC.hasSum
  rw [← hP, hL] at hC
  have hHas : HasSum F (c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
    simpa only [hterm, Complex.ofReal_re] using Complex.hasSum_re hC
  have h1 := hHas.nat_add_neg
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  convert h2 using 1
  · funext n
    simp only [hFdef]
    push_cast
    rw [mul_neg, Real.cosh_neg, neg_mul, Real.cos_neg]
    ring
  · simp [hFdef]

end PottsDiscontinuity.Bethe
