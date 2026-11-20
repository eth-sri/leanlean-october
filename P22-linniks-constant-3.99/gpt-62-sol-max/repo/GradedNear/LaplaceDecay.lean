module

public import GradedNear.Basic
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

open MeasureTheory Set Complex Filter
open scoped Topology FourierTransform Real

namespace GradedNear

namespace Decay

/-- Since `f` vanishes on `[x₀, ∞)`, the Laplace transform is an integral over `[0, x₀]`. -/
lemma laplace_eq_intervalIntegral {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (z : ℂ) :
    laplace f z = ∫ t in (0 : ℝ)..x₀, (f t : ℂ) * Complex.exp (-(z * t)) := by
  exact (integral_support_interval hf.pos.le fun t ht => by simp [hf.vanish t ht]).symm

end Decay

/-- Apply Riemann–Lebesgue with values in continuous functions of the real part.
The norm on that space gives uniform decay over the whole interval. -/
theorem laplace_decay {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (X : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc (-X) X, ∀ Y : ℝ, M ≤ |Y| →
      ‖laplace f ((x : ℂ) + (Y : ℂ) * I)‖ ≤ ε := by
  let K := Icc (-X) X
  let J := Ioc 0 x₀
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let F (t : ℝ) : C(K, ℂ) := ⟨fun x => (f t : ℂ) * exp (-(x : ℝ) * (t : ℂ)), by fun_prop⟩
  let G := J.indicator F
  have hF : ContinuousOn F (Icc 0 x₀) := by
    apply ContinuousMap.continuousOn_of_continuousOn_uncurry
    exact (continuous_ofReal.comp_continuousOn
      (hf.cont.comp continuous_fst.continuousOn fun _ hp => hp.1.1)).mul (by fun_prop)
  have hG : Integrable G := (hF.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hEval (x : K) (w : ℝ) : (𝓕 G w) x = laplace f ((x : ℝ) + ((2 * π * w : ℝ) : ℂ) * I) := by
    let L := ContinuousMap.evalCLM (R := ℂ) (M := ℂ) x
    change L (𝓕 G w) = _
    rw [Real.fourier_eq, ← L.integral_comp_comm ((Real.fourierIntegral_convergent_iff w).mpr hG),
      Decay.laplace_eq_intervalIntegral hf, intervalIntegral.integral_of_le hf.pos.le,
      ← integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    simp only [G, indicator, apply_ite, smul_zero, map_zero, L,
      ContinuousMap.evalCLM_apply]
    split_ifs <;> try rfl
    simp only [Circle.smul_def, Real.fourierChar_apply, Real.inner_apply, ContinuousMap.smul_apply,
      F, ContinuousMap.coe_mk, smul_eq_mul, mul_left_comm]
    rw [← exp_add]
    congr 2
    push_cast
    ring
  have he := (NormedAddGroup.tendsto_nhds_zero.mp (Real.zero_at_infty_fourier G)) ε hε
  rw [← Metric.cobounded_eq_cocompact, Filter.hasBasis_cobounded_norm.eventually_iff] at he
  obtain ⟨M, -, hM⟩ := he
  have hp : 0 < 2 * π := by positivity
  refine ⟨max 1 (2 * π * M), lt_max_of_lt_left zero_lt_one, fun x hx Y hY => ?_⟩
  have hw : M ≤ ‖Y / (2 * π)‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, le_div_iff₀ hp, mul_comm M]
    exact (le_max_right _ _).trans hY
  have H := ((ContinuousMap.norm_coe_le_norm (𝓕 G (Y / (2 * π))) ⟨x, hx⟩).trans_lt (hM hw)).le
  rwa [hEval, mul_div_cancel₀ _ hp.ne'] at H

end GradedNear
