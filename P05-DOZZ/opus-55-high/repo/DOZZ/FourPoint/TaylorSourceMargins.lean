/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorMomentBudget
public import DOZZ.FourPoint.TaylorPairIntegrability

/-! Source-level parameter choice and convergent near-diagonal kernels in the strict domain. -/

@[expose] public section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Choose all exponents before the spatial scale, on the literal corrected Taylor domain. -/
theorem twoRooted_region_parameters (γ α : ℝ)
    (hγ : 0 < γ) (hγsq : 2 < γ ^ 2) (hα : γ / 2 < α) (hα2 : α < 2 / γ) :
    ∃ q δ ε η : ℝ, 1 < q ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε ∧ 0 < η ∧
      η < 2 - γ * (Q γ - α) ∧ η ≤ δ * (γ * (α - γ / 2)) ∧
        η ≤ (α - 2 / γ) ^ 2 / 2 ∧
          γ * (Q γ - α) - 2 + η ≤
            -2 - 2 * ε + (1 - δ) * (γ / 2 + Q γ - α) ^ 2 / (2 * q) := by
  obtain ⟨_, hκ, hκ2⟩ := twoRooted_time_exponent γ α hγ hγsq hα hα2
  obtain ⟨heq, hgain⟩ := twoRooted_intermediate_gain γ α hγ hα2
  have hW : 2 * (γ * (Q γ - α)) < (γ / 2 + Q γ - α) ^ 2 := by
    linarith
  obtain ⟨_, hn⟩ := twoRooted_near_gain γ α hγ hα2
  exact taylor_region_margins _ _
    (γ * (α - γ / 2)) _ (zero_lt_one.trans hκ) hκ2 hW
    (mul_pos hγ (sub_pos.mpr hα)) hn

end DOZZ.Proofs
