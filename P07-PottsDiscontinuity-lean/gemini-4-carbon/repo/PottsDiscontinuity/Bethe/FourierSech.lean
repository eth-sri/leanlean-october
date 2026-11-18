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
open scoped FourierTransform

namespace PottsDiscontinuity.Bethe

private noncomputable def logistic2 (t : ℝ) : ℝ := (1 + Real.exp (-2 * t))⁻¹

private theorem hasDerivAt_logistic2 (t : ℝ) :
    HasDerivAt logistic2 (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2) t := by
  have h : HasDerivAt (fun t : ℝ => 1 + Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := by
    simpa using (((hasDerivAt_id t).const_mul (-2 : ℝ)).exp).const_add 1
  exact (h.inv (by positivity)).congr_deriv (by ring)

private theorem integral_cexp_div_cosh (ω : ℝ) :
    ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) =
      ((π / Real.cosh (π * ω / 2) : ℝ) : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * (1 - (x : ℂ)) ^ ((1 - s) - 1) with hg
  have hlt1 (t : ℝ) : logistic2 t < 1 := (inv_lt_one₀ (by positivity)).2 (by linarith [Real.exp_pos (-2 * t)])
  have hmono : StrictMono logistic2 := strictMono_of_hasDerivAt_pos hasDerivAt_logistic2 fun _ => by positivity
  have himg : logistic2 '' (univ : Set ℝ) = Ioo 0 1 := by
    ext x; refine ⟨fun ⟨t, _, hx⟩ => hx ▸ ⟨by unfold logistic2; positivity, hlt1 t⟩, fun ⟨h0, h1⟩ => ?_⟩
    have hq : 0 < (1 - x) / x := div_pos (by linarith) h0
    refine ⟨Real.log ((1 - x) / x) / (-2), mem_univ _, ?_⟩
    unfold logistic2; rw [show -2 * (Real.log ((1 - x) / x) / (-2)) = Real.log ((1 - x) / x) by field_simp, Real.exp_log hq]
    field_simp; ring
  have hint (t : ℝ) : |2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2| • g (logistic2 t) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
    rw [abs_of_pos (by positivity), Complex.real_smul]; dsimp only [g]
    set a : ℝ := 1 + Real.exp (-2 * t)
    have ha0 : 0 < a := by positivity
    have hpos1 : 0 < logistic2 t := inv_pos.mpr ha0
    have hpos2 : 0 < 1 - logistic2 t := sub_pos.mpr (hlt1 t)
    have hcp {x : ℝ} (hx : 0 < x) (y : ℂ) : (x : ℂ) ^ y = Complex.exp (Real.log x * y) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]
    rw [show (1 - ((logistic2 t : ℝ) : ℂ)) = ((1 - logistic2 t : ℝ) : ℂ) by push_cast; ring,
      hcp hpos1, hcp hpos2, ← Complex.exp_add]
    have hl1 : Real.log (logistic2 t) = -Real.log a := Real.log_inv a
    have hl2 : Real.log (1 - logistic2 t) = -2 * t - Real.log a := by
      rw [show 1 - logistic2 t = Real.exp (-2 * t) * a⁻¹ by dsimp [logistic2, a]; field_simp; ring,
        Real.log_mul (Real.exp_pos _).ne' (inv_ne_zero ha0.ne'), Real.log_exp, Real.log_inv]; ring
    rw [hl1, hl2, show ((-Real.log a : ℝ) : ℂ) * (s - 1) + ((-2 * t - Real.log a : ℝ) : ℂ) * (1 - s - 1) =
      (Real.log a : ℂ) + ((t : ℂ) + -(Complex.I * ω * t)) by rw [hs]; push_cast; ring,
      Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha0, ← Complex.ofReal_exp]
    have hreal : 2 * Real.exp (-2 * t) / a ^ 2 * (a * Real.exp t) = (Real.cosh t)⁻¹ := by
      have he2 : Real.exp (-2 * t) = (Real.exp t)⁻¹ ^ 2 := by
        rw [show -2 * t = -(2 * t) by ring, Real.exp_neg, show 2 * t = (2 : ℕ) * t by norm_num, Real.exp_nat_mul]; field_simp
      have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
      dsimp [a]; rw [he2, Real.cosh_eq, Real.exp_neg]; field_simp [ha0.ne']
    calc ((2 * Real.exp (-2 * t) / a ^ 2 : ℝ) : ℂ) * ((a : ℂ) * ((Real.exp t : ℂ) * Complex.exp (-(Complex.I * ω * t))))
        = ((2 * Real.exp (-2 * t) / a ^ 2 * (a * Real.exp t) : ℝ) : ℂ) * Complex.exp (-(Complex.I * ω * t)) := by push_cast; ring
      _ = (((Real.cosh t)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ω * t)) := by rw [hreal]
      _ = Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by push_cast; ring
  have hsub := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_logistic2 t).hasDerivWithinAt) hmono.injective.injOn g
  rw [himg, setIntegral_univ] at hsub; simp_rw [hint] at hsub
  have hbeta : Complex.betaIntegral s (1 - s) = ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
    unfold Complex.betaIntegral; rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, hsub]
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := s) (t := 1 - s) (by simp [hs]) (by simp [hs]; norm_num)
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul, Complex.Gamma_mul_Gamma_one_sub] at hG
  rw [← hbeta, ← hG, show (π : ℂ) * s = (π : ℂ) / 2 - ((π * ω / 2 : ℝ) : ℂ) * Complex.I by rw [hs]; push_cast; ring,
    Complex.sin_pi_div_two_sub, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  push_cast; ring

private theorem isBigO_cocompact_sech {k : ℝ} (hk : 0 < k) (C : ℝ) :
    (fun y : ℝ => ((C / Real.cosh (k * y) : ℝ) : ℂ)) =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (4 * |C| / k ^ 2) ?_
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_gt_atTop 0] with y hy
  have hy0 : 0 < |y| := by simpa using hy
  have hy2 : 0 < y ^ 2 := by rw [← sq_abs]; positivity
  rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hy0.le, Real.rpow_two, sq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy2), abs_div, abs_of_pos (Real.cosh_pos _)]
  have hc : (1 + (k * y) ^ 2) / 4 ≤ Real.cosh (k * y) := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    nlinarith [Real.quadratic_le_exp_of_nonneg (abs_nonneg (k * y)), Real.exp_pos (-|k * y|),
      sq_abs (k * y), abs_nonneg (k * y), sq_nonneg (|k * y| - 1)]
  have h1 : 1 / Real.cosh (k * y) ≤ 4 * (k ^ 2 * y ^ 2)⁻¹ :=
    (one_div_le_one_div_of_le (by positivity) hc).trans <| by
      rw [show 1 / ((1 + (k * y) ^ 2) / 4) = 4 * (1 + (k * y) ^ 2)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by nlinarith)) (by norm_num)
  calc |C| / Real.cosh (k * y) = |C| * (1 / Real.cosh (k * y)) := by ring
    _ ≤ |C| * (4 * (k ^ 2 * y ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = 4 * |C| / k ^ 2 * (y ^ 2)⁻¹ := by field_simp

/-- The terms `1 / cosh (π (2 π j + α) / (2 λ))` are summable over `j ∈ ℤ`. -/
theorem summable_sech_periodic {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Summable (fun j : ℤ => 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
  set a : ℝ := α / (2 * π)
  have hb := Complex.isBigO_ofReal_left.mp (isBigO_cocompact_sech (k := π ^ 2 / lam) (by positivity) 1)
  have hT : Tendsto (fun n : ℤ => a + (n : ℝ)) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft a).isClosedEmbedding.tendsto_cocompact.comp Int.tendsto_coe_cofinite
  have hg : Summable (fun n : ℤ => |a + (n : ℝ)| ^ (-(2 : ℝ))) :=
    ((Real.summable_one_div_int_add_rpow a 2).2 one_lt_two).congr fun n => by
      rw [Real.rpow_neg (abs_nonneg _), add_comm, one_div]
  exact summable_of_isBigO hg ((hb.comp_tendsto hT).congr_left fun n => by
    simp only [Function.comp_apply]; congr 2; dsimp [a]; field_simp [Real.pi_ne_zero]; ring)

/-- Poisson summation for the hyperbolic secant:
`(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`. -/
theorem periodic_sech_eq_cos_series {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    HasSum (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * α) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)))
      ((π / (2 * lam)) * (∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) - 1 / 2) := by
  have hpi := Real.pi_pos
  set b : ℝ := π ^ 2 / lam; set c : ℝ := π / (2 * lam); set x : ℝ := α / (2 * π)
  have hb : 0 < b := by dsimp [b]; positivity
  set f : ℝ → ℂ := fun y => ((c / Real.cosh (b * y) : ℝ) : ℂ)
  have hc : Continuous f := Complex.continuous_ofReal.comp
    (continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id)) fun _ => (Real.cosh_pos _).ne')
  have hF : 𝓕 f = fun ξ => (((1 / 2) / Real.cosh (lam * ξ) : ℝ) : ℂ) := funext fun ξ => by
    rw [fourier_real_eq_integral_exp_smul]
    set ω : ℝ := 2 * π * ξ / b
    have h1 (v : ℝ) : Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) • f v =
        (c : ℂ) * (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) (b * v) := by
      simp only [f, smul_eq_mul, show (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) = -(Complex.I * ω * ((b * v : ℝ) : ℂ)) by
        have : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
        dsimp [ω]; push_cast; field_simp]
      push_cast; ring
    simp_rw [h1]
    have key := Measure.integral_comp_mul_left (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ)) b
    beta_reduce at key
    rw [integral_const_mul, key, integral_cexp_div_cosh ω, abs_of_pos (inv_pos.mpr hb), Complex.real_smul,
      show π * ω / 2 = lam * ξ by dsimp [ω, b]; field_simp]
    have hlC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have hpC : (π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    dsimp [b, c]; push_cast; field_simp [hlC, hpC]
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hc one_lt_two (isBigO_cocompact_sech hb c)
    (hF ▸ isBigO_cocompact_sech hlam (1 / 2)) x
  have hL : ∑' n : ℤ, f (x + n) = ((c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) : ℝ) : ℂ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    simp only [f]; rw [show b * (x + (n : ℝ)) = π * (2 * π * n + α) / (2 * lam) by dsimp [b, x]; field_simp; ring, mul_one_div]
  have hsinv : Summable (fun n : ℤ => (1 / 2 : ℝ) / Real.cosh (lam * (n : ℝ))) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((Complex.isBigO_ofReal_left.mp (isBigO_cocompact_sech hlam (1 / 2))).comp_tendsto Int.tendsto_coe_cofinite)
  set F : ℤ → ℝ := fun n => (1 / 2) / Real.cosh (lam * n) * Real.cos (n * α)
  have hsumF : Summable F := Summable.of_norm_bounded hsinv fun n => by
    simp only [F, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / 2 : ℝ) / Real.cosh (lam * n))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have hsumC : Summable (fun n : ℤ => 𝓕 f n * fourier n (x : UnitAddCircle)) := Summable.of_norm_bounded hsinv fun n => by
    rw [norm_mul, congrFun hF (n : ℝ), Complex.norm_real, Real.norm_eq_abs, fourier_apply, Circle.norm_coe,
      mul_one, abs_of_pos (by positivity)]
  have hRe := congrArg Complex.re hP
  rw [hL, Complex.ofReal_re, Complex.re_tsum hsumC] at hRe
  have hterm (n : ℤ) : (𝓕 f n * fourier n (x : UnitAddCircle)).re = F n := by
    rw [congrFun hF (n : ℝ), show fourier n (x : UnitAddCircle) = Complex.exp (((n * α : ℝ) : ℂ) * Complex.I) by
      rw [fourier_coe_apply]; congr 1; dsimp [x]; push_cast; field_simp [show (π : ℂ) ≠ 0 by exact_mod_cast hpi.ne'],
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp_rw [hterm] at hRe
  have hHas : HasSum F (c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := hRe ▸ hsumF.hasSum
  convert (hasSum_nat_add_iff' 1).mpr hHas.nat_add_neg using 1
  · funext n; simp only [F]; push_cast; rw [mul_neg, Real.cosh_neg, neg_mul, Real.cos_neg]; ring
  · simp [F]

end PottsDiscontinuity.Bethe
