module

public import RequestProject.ReconUC

/-!
# Vanishing of `L²` Helmholtz solutions outside a disc

A `C²` function in `L²(ℝ²)` solving `(Δ + E) v = 0` (`E > 0`) outside a disc vanishes there
(`eq_zero_outside_of_helmholtz`): each angular mode solves Bessel's equation and is square
integrable against `r dr` by polar coordinates, hence vanishes by `bessel_rellich`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ENNReal

noncomputable section

namespace PolyaNeumann

variable {v : ℂ → ℂ}

/-- Cauchy–Schwarz on an interval: `(∫ f)² ≤ (b - a) ∫ f²`. -/
lemma sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  set c := (∫ x in a..b, f x) / (b - a)
  have h0 : 0 ≤ ∫ x in a..b, (f x - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _
  have e : ∫ x in a..b, (f x - c) ^ 2 =
      (∫ x in a..b, f x ^ 2) - 2 * c * (∫ x in a..b, f x) + c ^ 2 * (b - a) := by
    have h1 : ∀ x, (f x - c) ^ 2 = (f x ^ 2 - 2 * c * f x) + c ^ 2 := fun x => by ring
    simp_rw [h1]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · ring
    all_goals first
      | exact (hf.pow 2).intervalIntegrable _ _
      | exact (continuous_const.mul hf).intervalIntegrable _ _
      | exact ((hf.pow 2).sub (continuous_const.mul hf)).intervalIntegrable _ _
      | norm_num
  have hc : (∫ x in a..b, f x) = c * (b - a) := by grind
  nlinarith

lemma norm_angChar (n : ℤ) (θ : ℝ) : ‖angChar n θ‖ = 1 := by
  simp [angChar, Complex.norm_exp]

/-- `|m_n(r)|² ≤ 2π ∫₀^{2π} |v(x₀ + r e^{iθ})|² dθ`. -/
lemma norm_angMode_sq_le (hv : Continuous v) (x₀ : ℂ) (n : ℤ) (r : ℝ) :
    ‖angMode v x₀ n r‖ ^ 2 ≤ 2 * π * ∫ θ in 0..2 * π, ‖v (circPt x₀ r θ)‖ ^ 2 := by
  have h2 := sq_intervalIntegral_le (hv.comp ((continuous_circPt x₀).comp (Continuous.prodMk_right r))).norm (show 0 < 2 * π by positivity)
  rw [sub_zero] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) (by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans (le_of_eq ?_)
    simp [norm_angChar]) 2).trans h2

lemma polarCoord_symm_eq_circPt (p : ℝ × ℝ) : Complex.polarCoord.symm p = circPt 0 p.1 p.2 := by
  simp [circPt, eI, Complex.exp_mul_I]

/-- The circle masses `r ∫₀^{2π} |v(r e^{iθ})|² dθ` of an `L²` function are integrable. -/
lemma integrableOn_circleMass (hv : Continuous v) (hL2 : MemLp v 2 volume) :
    IntegrableOn (fun r => r * ∫ θ in 0..2 * π, ‖v (circPt 0 r θ)‖ ^ 2) (Ioi 0) := by
  set g : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * ‖v (circPt 0 p.1 p.2)‖ₑ ^ 2 with hg
  have hgm : Measurable g :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul ((hv.comp (continuous_circPt 0)).measurable.enorm.pow_const 2)
  have hpolar := Complex.lintegral_comp_polarCoord_symm (fun z => ‖v z‖ₑ ^ 2)
  simp only [polarCoord_symm_eq_circPt, smul_eq_mul] at hpolar
  rw [polarCoord_target] at hpolar
  have hfin : ∫⁻ z, ‖v z‖ₑ ^ 2 < ∞ := by
    have := (hL2.integrable_norm_pow two_ne_zero).hasFiniteIntegral
    simp_all [HasFiniteIntegral]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hgm.aemeasurable] at hpolar
  set K : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Ioo (-π) π, g (r, θ) with hK
  have hKm : Measurable K := by
    fun_prop
  have hKi : IntegrableOn (fun r => (K r).toReal) (Ioi 0) :=
    integrable_toReal_of_lintegral_ne_top hKm.aemeasurable (by
      grind)
  refine hKi.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr0  := le_of_lt hr
  have e1 : K r = ENNReal.ofReal (∫ θ in Ioo (-π) π, r * ‖v (circPt 0 r θ)‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · simp_all
    · exact ((continuous_const.mul ((hv.comp ((continuous_circPt 0).comp
      (Continuous.prodMk_right r))).norm.pow 2)).integrableOn_Icc  ).mono_set Ioo_subset_Icc_self
    · exact Eventually.of_forall fun θ => by positivity
  have hper : Function.Periodic (fun θ => r * ‖v (circPt 0 r θ)‖ ^ 2) (2 * π) := by
    intro θ; simp [circPt, eI_periodic θ]
  have e2 : ∫ θ in Ioo (-π) π, r * ‖v (circPt 0 r θ)‖ ^ 2 =
      ∫ θ in 0..2 * π, r * ‖v (circPt 0 r θ)‖ ^ 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    have := hper.intervalIntegral_add_eq (-π) 0
    grind
  show (K r).toReal = _
  rw [e1, e2, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg (by positivity)
    fun θ _ => by positivity), intervalIntegral.integral_const_mul]

/-- An `L²` solution of `(Δ + E) v = 0` outside a disc vanishes there. -/
theorem eq_zero_outside_of_helmholtz (hv : ContDiff ℝ 2 v) (hL2 : MemLp v 2 volume)
    {E : ℝ} (hE : 0 < E) {R : ℝ} (hR : 0 < R)
    (hhelm : ∀ z : ℂ, R < ‖z‖ → lap v z + E * v z = 0) : ∀ z : ℂ, R < ‖z‖ → v z = 0 := by
  have hmode : ∀ n : ℤ, ∀ r ∈ Ioi R, angMode v 0 n r = 0 := by
    intro n
    have hmc  :=
      continuous_iff_continuousAt.2 fun r => (hasDerivAt_angMode hv 0 n r).continuousAt
    refine bessel_rellich (c := n ^ 2) hE hR (fun r _ => hasDerivAt_angMode hv 0 n r)
      ?_ ?_
    · intro r hr
      have hr0  := hR.trans hr
      rw [← angMode_bessel hv 0 n  hr0.ne' (fun θ => hhelm _ (by
        simp_all [← dist_zero_right, dist_circPt 0 hr0.le θ]))]
      exact hasDerivAt_angMode1 hv 0 n r
    · refine Integrable.mono' (((integrableOn_circleMass hv.continuous hL2).mono_set
        (Ioi_subset_Ioi hR.le)).const_mul (2 * π)) ?_ ?_
      · fun_prop
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
        have hr0  := (hR.trans hr).le
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := norm_angMode_sq_le hv.continuous 0 n r
        nlinarith
  intro z hz
  set r := ‖z‖
  have := eq_zero_of_angModes (hv.continuous.comp ((continuous_circPt 0).comp (Continuous.prodMk_right r))) (by
    intro θ; simp [circPt, eI_periodic θ]) (fun n => hmode n r hz) (Complex.arg z)
  simp_all [circPt, eI, r]

end PolyaNeumann
