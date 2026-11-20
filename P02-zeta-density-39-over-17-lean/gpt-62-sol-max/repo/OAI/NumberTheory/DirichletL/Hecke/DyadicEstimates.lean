module
public import OAI.NumberTheory.DirichletL.Hecke.DyadicContour

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem rapid_tail_bound (F : ℝ → ℂ) (C T : ℝ) (n : ℕ) (hC : 0≤C) (hT : 0≤T)
    (hF : ∀ t : ℝ, (1+|t|)^(n+2)*‖F t‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, F t‖ ≤ C/(1+T)^n*Real.pi := by
  have hen (t : ℝ) (ht : t ∈ (Icc (-T) T)ᶜ) :
      ‖F t‖≤(C/(1+T)^n)*(1+t^2)⁻¹ := by
    have ht' : T≤|t| := by
      by_contra h
      have hab : |t|<T := lt_of_not_ge h
      exact ht ⟨(abs_lt.mp hab).1.le, (abs_lt.mp hab).2.le⟩
    have hp : (1+T)^n*(1+t^2)≤(1+|t|)^(n+2) := by
      rw [pow_add]
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by linarith) (by linarith) n
      · nlinarith [sq_abs t, abs_nonneg t]
      · positivity
      · positivity
    have hh : ‖F t‖*((1+T)^n*(1+t^2))≤C :=
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa [mul_comm] using hF t)
    have hb := (le_div_iff₀ (by positivity : 0<(1+T)^n*(1+t^2))).mpr hh
    simpa [div_mul_eq_div_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb
  have hint := (integrable_inv_one_add_sq.const_mul (C/(1+T)^n))
  calc
    _ ≤ ∫ t : ℝ in (Icc (-T) T)ᶜ, (C/(1+T)^n)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      exact hen t ht
    _ ≤ ∫ t : ℝ, (C/(1+T)^n)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem mellin_tail_bound (L : ℂ → ℂ) (W : ℝ → ℂ)
    (D r σ freq C T K : ℝ) (n : ℕ) (hD : 0<D) (hC : 0≤C) (hT : 0≤T)
    (hs : ∀ t : ℝ, ‖L ((r : ℂ)+t*I+shift σ freq)‖≤K)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, mellinIntegrand L W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*K)/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      ((norm_nonneg _).trans (hs 0))
  · exact hT
  · intro t
    rw [mellinIntegrand_norm L W D σ freq hD]
    simp only [mellin_vertical_re]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖L ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        (hs t) (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

/-- An interval integral bounded by a Cauchy majorant. -/
theorem cauchy_segment_bound (F : ℝ → ℂ) (C T : ℝ) (hC : 0≤C) (hT : 0≤T)
    (hF : ∀ t ∈ Icc (-T) T, (1+|t|)^2*‖F t‖≤C) :
    ‖∫ t : ℝ in -T..T, F t‖ ≤ C*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul C
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, C*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa [div_eq_mul_inv] using
        CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hF t ⟨ht.1.le,ht.2⟩)
    _ ≤ ∫ t : ℝ, C*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem mellin_central_bound (L : ℂ → ℂ) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖L ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, mellinIntegrand L W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  apply cauchy_segment_bound _ _ _ (by positivity) hT
  intro t ht
  rw [mellinIntegrand_norm L W D σ freq hD, mellin_vertical_re]
  calc
    _ = ((1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖)*D^(l+σ-1/2)*
        ‖L ((l : ℂ)+t*I+shift σ freq)‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
      (hs t ht) (norm_nonneg _) (by positivity)

theorem absolute_tail_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1<r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi :=
  mellin_tail_bound (series χ inverse) W D r σ freq C T _ n hD hC hT
    (fun t => series_norm_le χ inverse hr (by simp)) hm

end SevenEighths.HeckeDyadic

end

end OAI
