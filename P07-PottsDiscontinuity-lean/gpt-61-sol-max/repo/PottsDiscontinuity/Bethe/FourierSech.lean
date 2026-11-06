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

theorem cosh_ge_quarter (t : ℝ) : (1 + t ^ 2) / 4 ≤ Real.cosh t := by
  
  have h2 := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
  have h3 : 0 < Real.exp (-|t|) := Real.exp_pos _
  
  rw [ (Real.cosh_abs t).symm ,  Real.cosh_eq _ ]
  have h5  := sq_abs t
  nlinarith [abs_nonneg t]

theorem one_div_cosh_le (t : ℝ) : 1 / Real.cosh t ≤ 4 * (1 + t ^ 2)⁻¹ := by
  
  
  calc 1 / Real.cosh t ≤ 1 / ((1 + t ^ 2) / 4) := one_div_le_one_div_of_le (by positivity) (cosh_ge_quarter t)
    _ = 4 * (1 + t ^ 2)⁻¹ := by field_simp

/-- The logistic map `σ(t) = 1 / (1 + e^{-2t})`, a smooth increasing bijection `ℝ → (0,1)`. -/
noncomputable def logistic2 (t : ℝ) : ℝ := (1 + Real.exp (-2 * t))⁻¹

theorem logistic2_pos (t : ℝ) : 0 < logistic2 t := by
  unfold logistic2; positivity

theorem logistic2_lt_one (t : ℝ) : logistic2 t < 1 := by
  unfold logistic2
  have := Real.exp_pos (-2 * t)
  rw [inv_lt_one₀ (by positivity)]
  linarith

theorem hasDerivAt_logistic2 (t : ℝ) :
    HasDerivAt logistic2 (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2) t := by
  have h1 : HasDerivAt (fun t  => -2 * t) (-2) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 )
  
  have h3 := (by
                simpa using (h1.exp).const_add 1 : HasDerivAt (fun t  => 1 + Real.exp (-2 * t)) (Real.exp (-2 * t) *  -2 ) t).inv (by positivity)
  
  
  exact h3.congr_deriv (by ring)

theorem strictMono_logistic2 : StrictMono logistic2 := by
  refine strictMono_of_hasDerivAt_pos hasDerivAt_logistic2 fun t => ?_
  positivity

theorem image_logistic2 : logistic2 '' (univ : Set ℝ) = Ioo 0 1 := by
  ext x
  constructor
  · grind [logistic2_pos, logistic2_lt_one]
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log ((1 - x) / x) /  -2 , mem_univ _, ?_⟩
    unfold logistic2
    
    have : -2 * (Real.log ((1 - x) / x) /  -2 ) = Real.log ((1 - x) / x) := by field_simp
    rw [this, Real.exp_log (div_pos (by linarith) h0)]
    field_simp
    ring

theorem cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (y : ℂ) :
     (x : ℂ)  ^ y = Complex.exp (Real.log x * y) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

theorem logistic2_integrand (ω t : ℝ) :
    ((2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ) : ℂ) *
      (((logistic2 t : ℝ) : ℂ) ^ ((1 - Complex.I * ω) / 2 - 1) *
        (1 - ((logistic2 t : ℝ) : ℂ)) ^ ( 1 - (1 - Complex.I * ω) / 2  - 1)) =
      Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set a : ℝ := 1 + Real.exp (-2 * t) with ha
  have ha0 : 0 < a := by positivity
  
  have hσ : logistic2 t = a⁻¹ := rfl
  
  
  
  have e1 :  1 -   logistic2 t    = ( (1 - logistic2 t : ℝ)  : ℂ) := by push_cast; ring
  rw [e1, cpow_ofReal_pos (logistic2_pos t), cpow_ofReal_pos (by have := logistic2_lt_one t; linarith), ← Complex.exp_add]
  have hl1 : Real.log (logistic2 t) = -Real.log a := by rw [hσ, Real.log_inv]
  have hl2 : Real.log (1 - logistic2 t) = -2 * t - Real.log a := by
    rw [(by
           grind : 1 - logistic2 t = Real.exp (-2 * t) * a⁻¹), Real.log_mul (Real.exp_pos _).ne' (inv_ne_zero ha0.ne'), Real.log_exp, Real.log_inv]; ring
  
  have hexp : Complex.exp ( (-Real.log a : ℝ)  * (s - 1) +  (-2 * t - Real.log a : ℝ)  *
      (1 - s - 1)) =  a  * Complex.exp (2 * t * s) := by
    have :  (-Real.log a : ℝ)  * (s - 1) +  (-2 * t - Real.log a : ℝ)  * (1 - s - 1) =
         Real.log a  + 2 * t * s := by push_cast; ring
    rw [this, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ha0]
  
  have hX  := Complex.exp_ne_zero t
  
  have e2' : Complex.exp (-2 *  t ) = (Complex.exp t)⁻¹ ^ 2 := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    simp_all
  have e3 : Complex.exp (2 * t * s) = Complex.exp t * Complex.exp (-(Complex.I * ω * t)) := by
    rw [← Complex.exp_add]; congr 1;  ring
  have e4 :  Real.cosh t  = (Complex.exp t + (Complex.exp t)⁻¹) / 2 := by
    rw [Complex.ofReal_cosh, Complex.cosh, Complex.exp_neg]
  have e5 :  a  = 1 + (Complex.exp t)⁻¹ ^ 2 := by simp_all
  have e6 :  (2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2 : ℝ)  =
      2 * (Complex.exp t)⁻¹ ^ 2 / (1 + (Complex.exp t)⁻¹ ^ 2) ^ 2 := by
    push_cast; rw [e2']
  grind

theorem betaIntegral_eq_integral_cexp_div_cosh (ω : ℝ) :
    Complex.betaIntegral ((1 - Complex.I * ω) / 2) (1 - (1 - Complex.I * ω) / 2) =
      ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  set g : ℝ → ℂ := fun x =>  x  ^ (s - 1) * (1 -  x ) ^ ( 1 - s  - 1) with hg
  
  have h2  :=
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (hasDerivAt_logistic2 t).hasDerivWithinAt)
      strictMono_logistic2.injective.injOn g
  rw [image_logistic2] at h2
  have h3 : ∀ t , |2 * Real.exp (-2 * t) / (1 + Real.exp (-2 * t)) ^ 2| • g (logistic2 t) =
      Complex.exp (-(Complex.I * ω * t)) /  Real.cosh t  := by
    intro t
    rw [abs_of_pos (by positivity)]
    exact logistic2_integrand ω t
  simp_rw [h3] at h2
  unfold Complex.betaIntegral
  rw [(by
         rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] : ∫ x in (0)..1, g x = ∫ x in Ioo (0) 1, g x), h2, setIntegral_univ]

theorem integral_cexp_div_cosh (ω : ℝ) :
    ∫ t : ℝ, Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t : ℂ) =
      ((π / Real.cosh (π * ω / 2) : ℝ) : ℂ) := by
  set s : ℂ := (1 - Complex.I * ω) / 2 with hs
  have hsre : 0 < s.re := by simp [hs]
  have hs1re : 0 < (1 - s).re := by simp [hs]; norm_num
  rw [← betaIntegral_eq_integral_cexp_div_cosh]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hsre hs1re
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul,
    Complex.Gamma_mul_Gamma_one_sub] at h
  rw [← h]
  have hsin : Complex.sin (π * s) =  Real.cosh (π * ω / 2)  := by
    have :  π  * s =  π  / 2 -  (π * ω / 2 : ℝ)  * Complex.I := by
       push_cast; ring
    rw [this, Complex.sin_pi_div_two_sub, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hsin]
  push_cast
  ring

/-! ### Fourier transform of a rescaled secant -/

open scoped FourierTransform

/-- The (unitary, `e^{-2πi x ξ}`) Fourier transform of `y ↦ c / cosh (b y)` is
`ξ ↦ (c / b) · π / cosh (π² ξ / b)`. -/
theorem fourier_sech (b : ℝ) (hb : 0 < b) (c ξ : ℝ) :
    𝓕 (fun y : ℝ => ((c / Real.cosh (b * y) : ℝ) : ℂ)) ξ =
      (( c / b  * (π / Real.cosh (π ^ 2 * ξ / b)) : ℝ) : ℂ) := by
  rw [fourier_real_eq_integral_exp_smul]
  set ω : ℝ := 2 * π * ξ / b with hω
  have h1 : ∀ v , Complex.exp ( (-2 * π * v * ξ : ℝ)  * Complex.I) •
       (c / Real.cosh (b * v) : ℝ)  =
       c  * (fun t : ℝ => Complex.exp (-(Complex.I * ω * t)) /  Real.cosh t ) (b * v) := by
    intro v
    
    have :   (-2 * π * v * ξ : ℝ)  * Complex.I  = -(Complex.I * ω *  (b * v ) ) := by
      have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
      rw [hω]; push_cast; field_simp
    rw [this]; push_cast; ring
  simp_rw [h1]
  
  
  rw [integral_const_mul, (Measure.integral_comp_mul_left
                             (fun t  => Complex.exp (-(Complex.I * ω * t)) / (Real.cosh t )) b), integral_cexp_div_cosh ω]
  have hπ : π * ω / 2 = π ^ 2 * ξ / b := by rw [hω]; field_simp
  rw [hπ]
  rw [abs_of_pos (inv_pos.mpr hb), Complex.real_smul]
  push_cast
  ring

/-! ### Decay -/

section

variable {k : ℝ} (hk : 0 < k) (C : ℝ)
include hk C

theorem isBigO_cocompact_sech  :
    (fun y : ℝ => ((C / Real.cosh (k * y) : ℝ) : ℂ)) =O[cocompact ℝ]
       fun y : ℝ => |y| ^ (-(2 : ℝ))  := by
  refine Asymptotics.IsBigO.of_bound (4 * |C| / k ^ 2) ?_
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_gt_atTop 0] with y hy
  have hy0 : 0 < |y| := by simpa using hy
  have hyne  := abs_pos.mp hy0
  have hy2 : 0 < y ^ 2 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hy0.le, Real.rpow_two, sq_abs,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy2), abs_div,
    abs_of_pos (Real.cosh_pos _)]
  
  have h2 : (1 + (k * y) ^ 2)⁻¹ ≤ (k ^ 2 * y ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    grind
  calc |C| / Real.cosh (k * y) = |C| * (1 / Real.cosh (k * y)) := by ring
    _ ≤ |C| * (4 * (k ^ 2 * y ^ 2)⁻¹) := by
        gcongr
        exact (one_div_cosh_le (k * y)).trans (by gcongr)
    _ = 4 * |C| / k ^ 2 * (y ^ 2)⁻¹ := by field_simp

theorem isBigO_cocompact_sech_real  :
    (fun y : ℝ => C / Real.cosh (k * y)) =O[cocompact ℝ]  fun y : ℝ => |y| ^ (-(2 : ℝ))  := Complex.isBigO_ofReal_left.mp (isBigO_cocompact_sech hk C)

end

/-- The terms `1 / cosh (π (2 π j + α) / (2 λ))` are summable over `j ∈ ℤ`. -/
theorem summable_sech_periodic {lam : ℝ} (hlam : 0 < lam) (α : ℝ) :
    Summable  fun j : ℤ => 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))  := by
  
  set a : ℝ := α / (2 * π) with ha
  
  
  have hT : Tendsto (fun n : ℤ => a + (n )) cofinite (cocompact ℝ) :=
    (Homeomorph.addLeft a).isClosedEmbedding.tendsto_cocompact.comp Int.tendsto_coe_cofinite
  
  refine summable_of_isBigO (by
                               have := (Real.summable_one_div_int_add_rpow a 2).2 one_lt_two
                               refine this.congr fun n => ?_
                               rw [Real.rpow_neg (abs_nonneg _), add_comm, one_div] : Summable  fun n : ℤ => |a + (n )| ^ (-(2 : ℝ))) ?_
  have := (isBigO_cocompact_sech_real (by positivity : 0 < π ^ 2 / lam) 1).comp_tendsto hT
  refine this.congr_left fun n => ?_
  simp only [Function.comp_apply]
  
  rw [ha]
  field_simp
  ring

/-! ### Poisson summation -/

section

variable {lam : ℝ} (hlam : 0 < lam)
include hlam

theorem summable_inv_cosh_int  (C : ℝ) :
    Summable  fun n : ℤ => C / Real.cosh (lam * (n : ℝ))  := summable_of_isBigO (summable_abs_int_rpow one_lt_two)
                                                               (Asymptotics.IsBigO.comp_tendsto (isBigO_cocompact_sech_real hlam C) Int.tendsto_coe_cofinite)

theorem fourier_sech_periodic_aux  (ξ : ℝ) :
    𝓕 (fun y : ℝ => ((π / (2 * lam) / Real.cosh (π ^ 2 / lam * y) : ℝ) : ℂ)) ξ =
      (( 1 / 2  / Real.cosh (lam * ξ) : ℝ) : ℂ) := by
  
  rw [fourier_sech (π ^ 2 / lam) (by positivity)]
  
  
  
  field_simp

/-- Poisson summation for the hyperbolic secant:
`(π / (2 λ)) ∑_{j ∈ ℤ} 1 / cosh (π (2 π j + α) / (2 λ)) = 1 / 2 + ∑_{n ≥ 1} cos (n α) / cosh (λ n)`. -/
theorem periodic_sech_eq_cos_series  (α : ℝ) :
    HasSum (fun n : ℕ => Real.cos (((n + 1 : ℕ) : ℝ) * α) / Real.cosh (lam * ((n + 1 : ℕ) : ℝ)))
      ( π / (2 * lam)  *  ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))  - 1 / 2) := by
  have hpi := Real.pi_pos
  
  set b : ℝ := π ^ 2 / lam with hbdef
  set c : ℝ := π / (2 * lam) with hcdef
  set f : ℝ → ℂ := fun y =>  (c / Real.cosh (b * y) : ℝ)  with hfdef
  have hc : Continuous f := by
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      fun y => (Real.cosh_pos _).ne'
  
  have hF : 𝓕 f = fun ξ => (( 1 / 2  / Real.cosh (lam * ξ) : ℝ) : ℂ) := funext (fourier_sech_periodic_aux hlam)
  
  set x : ℝ := α / (2 * π) with hx
  
  -- left side
  
  -- right side: real parts
  have hterm : ∀ n : ℤ, (𝓕 f n * fourier n (x : UnitAddCircle)).re =
       1 / 2  / Real.cosh (lam * n) * Real.cos (n * α) := by
    intro n
    rw [congrFun hF  n ]
    have : fourier n (x : UnitAddCircle) = Complex.exp ( (n * α : ℝ)  * Complex.I) := by
      rw [fourier_coe_apply]
      
      rw [hx]; push_cast
      
      field_simp
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  set F : ℤ → ℝ := fun n =>  1 / 2  / Real.cosh (lam * n) * Real.cos (n * α) with hFdef
  
  
  have hRe := congrArg Complex.re (Real.tsum_eq_tsum_fourier_of_rpow_decay hc one_lt_two (isBigO_cocompact_sech (by positivity) c) (by
                                                                                                          rw [hF]; exact isBigO_cocompact_sech hlam (1 / 2)) x)
  rw [(by
         rw [← tsum_mul_left, Complex.ofReal_tsum]
         grind : ∑' n : ℤ, f (x + n) =
      ((c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam)) : ℝ) )), Complex.ofReal_re, Complex.re_tsum (by
                                                refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
                                                rw [norm_mul, congrFun hF  n , Complex.norm_real, Real.norm_eq_abs]
                                                
                                                rw [(by
                                                        exact Circle.norm_coe _ : ‖fourier n (x : UnitAddCircle)‖ = 1), mul_one, abs_of_pos (by  positivity)])] at hRe
  simp_rw [hterm] at hRe
  have hHas : HasSum F (c * ∑' j : ℤ, 1 / Real.cosh (π * (2 * π * j + α) / (2 * lam))) := by
    rw [hRe]; exact (by
                       refine Summable.of_norm_bounded (summable_inv_cosh_int hlam (1 / 2)) fun n => ?_
                       rw [hFdef]
                       simp only [norm_mul, Real.norm_eq_abs]
                       
                       rw [ abs_of_pos (by  positivity) ]
                       calc (1 / 2) / Real.cosh (lam * n) * |Real.cos (n * α)|
                           ≤  1 / 2  / Real.cosh (lam * n) * 1 := by
                             gcongr; exact Real.abs_cos_le_one _
                         _ = _ := mul_one _ : Summable F).hasSum
  have h1 := hHas.nat_add_neg
  
  convert  (hasSum_nat_add_iff' 1).mpr h1  using 1
  · funext n
    simp only [hFdef]
    push_cast
    rw [mul_neg, Real.cosh_neg, neg_mul, Real.cos_neg]
    ring
  · simp [hFdef]

end

end PottsDiscontinuity.Bethe
