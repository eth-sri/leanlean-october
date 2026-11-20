module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

lemma pow_groups_le_rpow {C C₀ L : ℝ} {n : ℕ} (hC : 1 ≤ C) (hL : 1 < L)
    (hn : (n : ℝ) ≤ C₀ * Real.log L) : C ^ n ≤ L ^ (C₀ * Real.log C) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (zero_lt_one.trans_le hC),
    Real.rpow_def_of_pos (zero_lt_one.trans hL), Real.exp_le_exp]
  calc
    _ ≤ Real.log C * (C₀ * Real.log L) := mul_le_mul_of_nonneg_left hn (Real.log_nonneg hC)
    _ = _ := by ring

end Erdos821.P3Edge
