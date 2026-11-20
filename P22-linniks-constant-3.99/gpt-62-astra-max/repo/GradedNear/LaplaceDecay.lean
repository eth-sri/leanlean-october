module

public import GradedNear.Basic

/-!
# Decay of the Laplace transform

For `f` satisfying Condition 1, `F(x + iY) → 0` as `|Y| → ∞`, uniformly for `x` in a compact
interval.

Apply the Riemann–Lebesgue lemma to a single Fourier transform with values in the Banach
space of continuous functions on `[-X,X]`. Its sup norm controls all real parts at once;
no differentiability of the test function is needed.
-/

@[expose] public section

namespace GradedNear

open MeasureTheory Set Filter Complex
open scoped FourierTransform Topology

/-- The real-axis transform, without any smoothness or support assumption. -/
lemma laplace_real (f : ℝ → ℝ) (x : ℝ) :
    (laplace f (x : ℂ)).re = ∫ t in Ioi (0:ℝ), f t * Real.exp (-x*t) := by
  simp_rw [laplace, ← ofReal_mul, ← ofReal_neg, ← ofReal_exp, ← ofReal_mul, integral_complex_ofReal, ofReal_re, neg_mul]

theorem laplace_decay {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (X : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (-X) X, ∀ Y : ℝ, M ≤ |Y| →
      ‖laplace f xy[x,Y]‖ ≤ ε := by
  let A := Icc (-X) X
  let kernel : C(ℝ × A, ℂ) := ⟨fun p => cexp (-(p.2.val * p.1 : ℝ)), by fun_prop⟩
  let F t := (f t : ℂ) • kernel.curry t
  have hF : ContinuousOn F (Icc 0 x₀) := (continuous_ofReal.comp_continuousOn
    (hf.cont.mono Icc_subset_Ici_self)).smul kernel.curry.continuous.continuousOn
  let g := (Ioc 0 x₀).indicator F
  have h := Metric.tendsto_nhds.mp (Real.zero_at_infty_fourier g) ε hε
  rw [← Metric.cobounded_eq_cocompact] at h
  obtain ⟨R, _, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp h
  refine ⟨(max R 1) * (2 * Real.pi), by positivity, fun x hx Y hY => ?_⟩
  let v := Y / (2 * Real.pi)
  have hv : R ≤ ‖v‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < 2 * Real.pi by positivity), le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)).trans hY
  refine le_trans ?_ (le_of_lt (by simpa using hR hv : ‖𝓕 g v‖ < ε))
  apply le_trans (le_of_eq ?_) ((𝓕 g v).norm_coe_le_norm ⟨x,hx⟩)
  congr 1
  rw [laplace, truncate_Ioi (X := x₀) (fun t ht => by simp [hf.vanish t ht]),
    Real.fourier_real_eq_integral_exp_smul]
  simp_rw [g, ← indicator_smul_apply _ (fun t : ℝ => cexp (↑(-2 * Real.pi * t * v) * I)) F, integral_indicator measurableSet_Ioc]
  rw [ContinuousMap.integral_apply]
  · refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    change _ = cexp _ * ((f t : ℂ) * cexp _)
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2; dsimp [v]; push_cast; field_simp; ring
  · exact ((by fun_prop : Continuous fun t : ℝ => cexp (↑(-2 * Real.pi * t * v) * I)).continuousOn.smul
      hF).integrableOn_Icc.mono_set Ioc_subset_Icc_self

end GradedNear
