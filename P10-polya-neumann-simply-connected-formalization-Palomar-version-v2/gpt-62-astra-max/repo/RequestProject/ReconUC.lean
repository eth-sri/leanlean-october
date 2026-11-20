module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.ReconModes
public import RequestProject.PlanarNotation

/-!
# Unique continuation for the Helmholtz equation on discs

Fourier uniqueness on circles (`eq_zero_of_angModes`) and unique continuation for smooth
solutions of `(Δ + E) v = 0` from a small concentric disc (`eq_zero_on_ball_of_helmholtz`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real

noncomputable section

namespace PolyaNeumann

/-- A continuous `2π`-periodic function all of whose Fourier coefficients vanish is zero. -/
theorem eq_zero_of_angModes {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f anglePeriod)
    (h : ∀ n : ℤ, ∫ₚ θ, angChar n θ * f θ = 0) (θ : ℝ) : f θ = 0 := by
  let F : C(ParamCircle, ℂ) := ⟨hper.lift, by
    refine continuous_quot_lift _ hf⟩
  have hF : ∀ x : ℝ, F (x : ParamCircle) = f x := fun x => rfl
  have hc : ∀ n : ℤ, fourierCoeff F n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have : ∫ₚ x, (fourier (-n)) (x : ParamCircle) • F x =
        ∫ₚ θ, angChar n θ * f θ := by
      congr 1; funext x
      rw [hF, fourier_coe_apply, smul_eq_mul, angChar]
      congr 2
      have : (π : ℂ) ≠ 0 := by simp
      field_simp
      push_cast; ring
    rw [this, h n, smul_zero]
  have hs := has_pointwise_sum_fourier_series_of_summable (f := F)
    (by rw [show fourierCoeff (⇑F) = 0 from funext hc]; exact summable_zero) θ
  simp [hc, zero_smul] at hs
  exact (hasSum_zero.unique hs).symm

lemma norm_eI (θ : ℝ) : ‖eI θ‖ = 1 := by
  simp [eI]

lemma dist_circPt (x₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : dist (circPt x₀ r θ) x₀ = r := by
  simp [circPt, dist_eq_norm, norm_eI, abs_of_nonneg hr]

lemma eI_periodic : Function.Periodic eI anglePeriod := by
  simp [eI, add_mul, Complex.exp_add]

/-- Unique continuation for `C²` solutions of `(Δ + E) v = 0` on a disc, from a smaller
concentric disc. -/
theorem eq_zero_on_ball_of_helmholtz {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) {E : ℝ} {y : ℂ}
    {ρ δ : ℝ} (hδ : 0 < δ) (hhelm : ∀ z ∈ ball y ρ, lap v z + E * v z = 0)
    (h0 : ∀ z ∈ ball y δ, v z = 0) : ∀ z ∈ ball y ρ, v z = 0 := by
  intro z hz
  by_cases hzδ : z ∈ ball y δ
  · exact h0 z hzδ
  have hδρ : δ < ρ := lt_of_le_of_lt (not_lt.mp hzδ) (mem_ball.mp hz)
  set a := δ / 4
  have ha : 0 < a := by positivity
  -- vanishing of the modes on `(a, ρ)`
  have hmode : ∀ n : ℤ, ∀ r ∈ Ioo a ρ, angMode v y n r = 0 := by
    intro n
    have hloc : ∀ r ∈ Ioo a δ, angMode v y n r = 0 := by
      intro r hr
      simp [angMode]
      refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun θ _ => ?_)
      rw [h0, mul_zero]
      rw [mem_ball, dist_circPt y (by linarith [hr.1]) θ]; exact hr.2
    have hr₀ : δ / 2 ∈ Ioo a ρ := ⟨by simp only [a]; linarith, by linarith⟩
    refine ode2_unique (p := fun r => ((1 / r : ℝ) : ℂ))
      (q := fun r => ((E - (n : ℝ) ^ 2 / r ^ 2 : ℝ) : ℂ)) (P := 1 / a)
      (Q := |E| + (n : ℝ) ^ 2 / a ^ 2) ?_ ?_ (fun r _ => hasDerivAt_angMode hv y n r) ?_ hr₀
      (hloc _ ⟨by simp [a]; linarith, by linarith⟩) ?_
    · intro r hr
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (ha.trans hr.1))]
      exact one_div_le_one_div_of_le ha hr.1.le
    · intro r hr
      rw [Complex.norm_real, Real.norm_eq_abs]
      
      refine (abs_sub _ _).trans ?_
      gcongr
      rw [abs_of_nonneg (by positivity)]
      gcongr
      exact hr.1.le
    · intro r hr
      have hr0  := ha.trans hr.1
      
      convert hasDerivAt_angMode1 hv y n r using 1
      rw [(angMode_bessel hv y n (E := E) hr0.ne' (fun θ => hhelm _ (by
        rw [mem_ball, dist_circPt y hr0.le θ]; exact hr.2)))]
      push_cast
      ring
    · 
      refine (hasDerivAt_angMode hv y n (δ / 2)).unique
        ((hasDerivAt_const (δ / 2) (0 : ℂ)).congr_of_eventuallyEq ?_)
      filter_upwards [Ioo_mem_nhds (show a < δ / 2 by simp only [a]; linarith)
        (show δ / 2 < δ by linarith)] with r hr using hloc r hr
  -- Fourier uniqueness on the circle through `z`
  set r := ‖z - y‖
  have hr : r ∈ Ioo a ρ := by
    constructor
    · have : δ ≤ r := by
        have := not_lt.mp (mt mem_ball.mpr hzδ); rwa [dist_eq_norm] at this
      simp only [a]; linarith
    · have := mem_ball.mp hz; rwa [dist_eq_norm] at this
  have hf : Continuous fun θ => v (circPt y r θ) :=
    hv.continuous.comp ((continuous_circPt y).comp (Continuous.prodMk_right r))
  
  have := eq_zero_of_angModes hf (by
    intro θ; simp only [circPt, eI_periodic θ]) (fun n => hmode n r hr) (Complex.arg (z - y))
  have hz' : circPt y r (Complex.arg (z - y)) = z := by
    simp [circPt, eI, r, Complex.norm_mul_exp_arg_mul_I]
  rwa [hz'] at this

end PolyaNeumann
