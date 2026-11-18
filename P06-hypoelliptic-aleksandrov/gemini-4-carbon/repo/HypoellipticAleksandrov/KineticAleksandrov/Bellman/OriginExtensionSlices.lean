module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- Each coordinate is bounded by its exact gauge weight. -/
theorem bellmanGauge_coordinate_bounds (q : ℝ × ℝ) :
    |q.1| ≤ bellmanGauge q ^ 3 ∧ |q.2| ≤ bellmanGauge q := by
  have hr := bellmanGauge_nonneg q
  have he := bellmanGauge_pow_six q
  unfold bellmanGaugePower at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (pow_nonneg hr 3)).mp
    rw [sq_abs, ← pow_mul]
    norm_num only at *
    nlinarith [show 0 ≤ q.2 ^ 6 by positivity]
  · apply (pow_le_pow_iff_left₀ (abs_nonneg _) hr (by decide : 6 ≠ 0)).mp
    rw [pow_abs, abs_of_nonneg (by positivity : 0 ≤ q.2 ^ 6)]
    nlinarith [sq_nonneg q.1]

/-- Absolute real powers of exponent greater than minus one are locally integrable. -/
theorem bellman_abs_rpow_locallyIntegrable (p : ℝ) (hp : -1 < p) :
    LocallyIntegrable (fun x : ℝ => |x| ^ p) volume := by
  have hm : Measurable (fun x => |x| ^ p) :=
    measurable_of_continuousOn_compl_singleton 0
      (continuous_abs.continuousOn.rpow_const (fun x hx => Or.inl
        (abs_pos.mpr (by simpa using hx)).ne'))
  apply locallyIntegrable_of_norm_le_rpow (by simp) (C := 1) (α := -p)
  · simpa using (show -p < 1 by linarith)
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      neg_neg, one_mul]
    exact le_rfl
  · exact hm.aestronglyMeasurable


/-- The position slice derivative is the literal position jet. -/
theorem bellman_hasDerivAt_first {f : (ℝ × ℝ) → ℝ} {X v : ℝ}
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun Y => f (Y, v)) (bellmanDx f (X, v)) X := by
  simpa [bellmanDx, Function.comp_def] using (hf.hasFDerivAt.comp_hasDerivAt X ((hasDerivAt_id X).prodMk (hasDerivAt_const X v)))

/-- The velocity slice derivative is the literal velocity jet. -/
theorem bellman_hasDerivAt_second {f : (ℝ × ℝ) → ℝ} {X v : ℝ}
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun w => f (X, w)) (bellmanDv f (X, v)) v := by
  simpa [bellmanDv, Function.comp_def] using (hf.hasFDerivAt.comp_hasDerivAt v ((hasDerivAt_const v X).prodMk (hasDerivAt_id v)))

end HypoellipticAleksandrov.KineticAleksandrov

