module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # The polynomial crossing prefactor has vanishing block rate -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

/-- Uniform crossing probability divided by the exact number of endpoint pairs. -/
noncomputable def blockPenalty (c : ℝ) (n : ℕ) := c / (3 * (n : ℝ) + 1)^2

theorem tendsto_block_log_rate_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (blockPenalty c n) / n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => 3 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [show (0 : ℝ) ≤ n by positivity]) tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (3 * (n : ℝ) + 1) / n) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop (1/3) (-1/3) 1 (by norm_num)).comp ht using 1
    funext n
    simp
    congr 1
    ring
  have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).sub (hlog.const_mul 2)
  simp only [mul_zero, sub_zero] at h
  refine h.congr fun n => ?_
  rw [blockPenalty, Real.log_div hc.ne' (by positivity), Real.log_pow]
  ring

end PottsDiscontinuity.TorusRC
