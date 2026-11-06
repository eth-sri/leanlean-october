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

/-- Cauchy–Schwarz on an interval: `(∫ f)² ≤ (b - a) ∫ f²`. -/
lemma sq_intervalIntegral_le  (hf : Continuous f)  (hab : a < b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  set c := (∫ x in a..b, f x) / (b - a)
  have hba : 0 < b - a := by linarith
  have h0 : 0 ≤ ∫ x in a..b, (f x - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _
  rw [show ∫ x in a..b, (f x - c) ^ 2 = (∫ x in a..b, f x ^ 2) - 2 * c * (∫ x in a..b, f x) + c ^ 2 * (b - a) by
    have h1 : ∀ x, (f x - c) ^ 2 = f x ^ 2 - 2 * c * f x + c ^ 2 := fun x => by ring
    simp_rw [h1]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp; ring
    all_goals first
      | exact (hf.pow 2).intervalIntegrable _ _
      | exact (continuous_const.mul hf).intervalIntegrable _ _
      | exact ((hf.pow 2).sub (continuous_const.mul hf)).intervalIntegrable _ _
      | exact continuous_const.intervalIntegrable _ _] at h0
  rw [show (∫ x in a..b, f x) = c * (b - a) by simp [c]; field_simp] at h0 ⊢
  nlinarith

lemma norm_angChar n θ : ‖angChar n θ‖ = 1 := by
  rw [angChar, Complex.norm_exp]
  simp

local notation "Φ0" => circPt 0

lemma polarCoord_symm_eq_circPt p : Complex.polarCoord.symm p = Φ0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circPt, eI, Complex.exp_mul_I]
  push_cast
  ring

/-- An `L²` solution of `(Δ + E) v = 0` outside a disc vanishes there. -/
theorem eq_zero_outside_of_helmholtz {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (hL2 : MemLp v 2 volume)
    {E : ℝ} (hE : 0 < E)  (hR : 0 < R)
    (hhelm : ∀ z : ℂ, R < ‖z‖ → lap v z + E * v z = 0) : ∀ z : ℂ, R < ‖z‖ → v z = 0 := by
  intro z hz
  set r := ‖z‖
  have hf : Continuous fun θ => v (Φ0 r θ) :=
    hv.continuous.comp ((continuous_circPt 0).comp (Continuous.prodMk_right r))
  have := eq_zero_of_angModes hf (by
    intro θ; simp [circPt, eI_periodic θ]) (fun n => (show ∀ n : ℤ, ∀ r ∈ Ioi R, angMode v 0 n r = 0 by
    intro n
    refine bessel_rellich (c := n ^ 2) hE hR (fun r _ => hasDerivAt_angMode hv 0 n r)
      ?_ ?_
    · intro r hr
      have hr0 := hR.trans hr
      have hb := angMode_bessel hv 0 n (E := E) hr0.ne' (fun θ => hhelm _ (by
        rw [← dist_zero_right, dist_circPt 0 hr0.le θ]; exact hr))
      rw [← hb]
      exact hasDerivAt_angMode1 hv 0 n r
    · refine Integrable.mono' (((show IntegrableOn (fun r => r * ∫ θ in 0..2 * π, ‖v (Φ0 r θ)‖ ^ 2) (Ioi 0) by
      set g : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * ‖v (Φ0 p.1 p.2)‖ₑ ^ 2 with hg
      have hgm : Measurable g :=
        (ENNReal.measurable_ofReal.comp measurable_fst).mul ((hv.continuous.comp (continuous_circPt 0)).measurable.enorm.pow_const 2)
      have hpolar := Complex.lintegral_comp_polarCoord_symm (fun z => ‖v z‖ₑ ^ 2)
      simp only [polarCoord_symm_eq_circPt, smul_eq_mul] at hpolar
      rw [polarCoord_target] at hpolar
      have hfin : ∫⁻ z, ‖v z‖ₑ ^ 2 < ∞ := by
        simpa [HasFiniteIntegral] using (hL2.integrable_norm_pow two_ne_zero).hasFiniteIntegral
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hgm.aemeasurable] at hpolar
      set K : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Ioo (-π) π, g (r, θ) with hK
      have hKm : Measurable K := by
        exact Measurable.lintegral_prod_right' (ν := volume.restrict (Ioo (-π) π)) hgm
      have hKi : IntegrableOn (fun r => (K r).toReal) (Ioi 0) :=
        integrable_toReal_of_lintegral_ne_top hKm.aemeasurable (by
          change ∫⁻ r in Ioi 0, K r ≠ ⊤
          rw [hpolar]; exact hfin.ne)
      refine hKi.congr_fun (fun r hr => ?_) measurableSet_Ioi
      have hr0 := le_of_lt hr
      have e1 : K r = ENNReal.ofReal (∫ θ in Ioo (-π) π, r * ‖v (Φ0 r θ)‖ ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · refine lintegral_congr fun θ => ?_
          simp [g]
          rw [ENNReal.ofReal_mul hr0, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
        · exact ((continuous_const.mul ((hv.continuous.comp ((continuous_circPt 0).comp (Continuous.prodMk_right r))).norm.pow 2)).integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self
        · exact Eventually.of_forall fun θ => by positivity
      have hper : Function.Periodic (fun θ => r * ‖v (Φ0 r θ)‖ ^ 2) (2 * π) := by
        intro θ; simp [circPt, eI_periodic θ]
      have e2 : ∫ θ in Ioo (-π) π, r * ‖v (Φ0 r θ)‖ ^ 2 =
          ∫ θ in 0..2 * π, r * ‖v (Φ0 r θ)‖ ^ 2 := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
        have := hper.intervalIntegral_add_eq (-π) 0
        rw [show -π + 2 * π = π by ring, zero_add] at this
        exact this
      show (K r).toReal = _
      rw [e1, e2, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg (by positivity)
        fun θ _ => by positivity), intervalIntegral.integral_const_mul]).mono_set
        (Ioi_subset_Ioi hR.le)).const_mul (2 * π)) ?_ ?_
      · exact (continuous_id.mul ((continuous_iff_continuousAt.2 fun r => (hasDerivAt_angMode hv 0 n r).continuousAt).norm.pow 2)).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
        have hr0 := (hR.trans hr).le
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := show ‖angMode v 0 n r‖ ^ 2 ≤ 2 * π * ∫ θ in 0..2 * π, ‖v (Φ0 r θ)‖ ^ 2 by
          have h1 : ‖angMode v 0 n r‖ ≤ ∫ θ in 0..2 * π, ‖v (Φ0 r θ)‖ := by
            refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans (le_of_eq ?_)
            congr 1; funext θ
            rw [norm_mul, norm_angChar, one_mul]
          have h2 := sq_intervalIntegral_le ((hv.continuous.comp ((continuous_circPt 0).comp (Continuous.prodMk_right r))).norm) (show 0 < 2 * π by positivity)
          rw [sub_zero] at h2
          exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
        nlinarith) n r hz) (Complex.arg z)
  rwa [show Φ0 r (Complex.arg z) = z by
    simp only [circPt, eI, r, zero_add]
    exact Complex.norm_mul_exp_arg_mul_I z] at this

end PolyaNeumann
