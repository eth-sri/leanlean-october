module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Local integrability from the anisotropic dimension four -/

@[expose] public section
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
    rw [sq_abs]
    norm_num only at *
    nlinarith [show 0 ≤ q.2 ^ 6 by positivity]
  · apply (pow_le_pow_iff_left₀ (abs_nonneg _) hr (by decide : 6 ≠ 0)).mp
    rw [pow_abs, abs_of_nonneg (by positivity : 0 ≤ q.2 ^ 6)]
    nlinarith [sq_nonneg q.1]

/-- Absolute real powers of exponent greater than minus one are locally integrable. -/
theorem bellman_abs_rpow_locallyIntegrable (p : ℝ) (hp : -1 < p) :
    LocallyIntegrable (fun x : ℝ => |x| ^ p) volume := by
  have hm : Measurable (fun x : ℝ => |x| ^ p) :=
    measurable_of_continuousOn_compl_singleton 0
      (continuous_abs.continuousOn.rpow_const (fun x hx => Or.inl
        (abs_pos.mpr (by simp_all)).ne'))
  apply locallyIntegrable_of_norm_le_rpow (by simp) (C := 1) (α := -p)
  · simpa using (show -p < 1 by linarith)
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    simp
  · exact hm.aestronglyMeasurable

end HypoellipticAleksandrov.KineticAleksandrov
