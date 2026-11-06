/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.LocalWeight
public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient

/-! Exact cancellation of the insertion-position factor in the residue chart. -/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs

/-- The background norm cancels the zero-mode power at the critical total charge. The
remaining epsilon-dependent factor tends to one; the insertion separation remains explicit. -/
theorem residue_chart_tail_coefficient (γ α β ε Rbar : ℝ) (hγ : γ ≠ 0)
    (z w : ℂ) (hz : 2 ≤ ‖z‖) (hz8 : ‖z‖ ≤ 8) (hzw : 3 ≤ ‖z - w‖) :
    oneInsertionTailCoefficient γ α z
      (residueLocalWeight γ (2 * α + ε) β w z) Rbar =
      ‖z‖ ^ (γ * ε * reflectionExponent γ α) *
        ‖z - w‖ ^ (-(γ * β * reflectionExponent γ α)) * Rbar := by
  have hn : 0 < ‖z‖ := by positivity
  have hd : 0 < ‖z - w‖ := by positivity
  rw [residue_localWeight_eq γ (2 * α + ε) β z w z hz hz8 hzw
    (Metric.mem_ball_self (by norm_num))]
  change ‖z‖ ^ (-4 * α * (Q γ - α)) *
    (‖z‖ ^ (γ * (2 * α + ε)) / ‖z - w‖ ^ (γ * β)) ^ (reflectionExponent γ α) * Rbar = _
  rw [Real.div_rpow (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hd.le _),
    ← Real.rpow_mul hn.le, ← Real.rpow_mul hd.le, div_eq_mul_inv,
    ← Real.rpow_neg hd.le]
  have he : -4 * α * (Q γ - α) + γ * (2 * α + ε) * reflectionExponent γ α =
      γ * ε * reflectionExponent γ α := by
    unfold reflectionExponent
    grind
  calc _ = (‖z‖ ^ (-4 * α * (Q γ - α)) *
        ‖z‖ ^ (γ * (2 * α + ε) * reflectionExponent γ α)) *
        ‖z - w‖ ^ (-(γ * β * reflectionExponent γ α)) * Rbar := by ring
    _ = _ := by rw [← Real.rpow_add hn, he]

/-- Exact limiting coefficient for any of the admissible chart insertion points. -/
theorem residue_chart_tail_coefficient_limit (γ α β Rbar : ℝ) (hγ : γ ≠ 0)
    (z w : ℂ) (hz : 2 ≤ ‖z‖) (hz8 : ‖z‖ ≤ 8) (hzw : 3 ≤ ‖z - w‖) :
    Tendsto (fun ε : ℝ => oneInsertionTailCoefficient γ α z
      (residueLocalWeight γ (2 * α + ε) β w z) Rbar) (𝓝[>] 0)
      (𝓝 (‖z - w‖ ^ (-(γ * β * reflectionExponent γ α)) * Rbar)) := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow := (Real.continuous_const_rpow (by linarith only [hz])).continuousAt.tendsto.comp
    ((he.const_mul γ).mul_const (reflectionExponent γ α))
  simpa only [residue_chart_tail_coefficient γ α β _ Rbar hγ z w hz hz8 hzw,
    mul_zero, zero_mul, Real.rpow_zero, one_mul, Function.comp_def] using
    (hpow.mul_const _).mul_const Rbar

end DOZZ.Proofs
