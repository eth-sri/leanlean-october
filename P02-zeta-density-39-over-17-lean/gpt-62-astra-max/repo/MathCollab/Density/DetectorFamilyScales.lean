module
public import MathCollab.Density.DetectorTaylorFamily
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def detectorTaylorCutoff (T : ℝ) : ℕ := ⌈10*Real.log T⌉₊



theorem detectorTaylorCutoff_le_log {T : ℝ} (hlog : 1 ≤ Real.log T) :
    (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 10*Real.log T by linarith)
  change (detectorTaylorCutoff T : ℝ) < 10*Real.log T+1 at h
  linarith

/-- The chosen Taylor cutoff gives a polynomially small geometric factor. -/
theorem detectorTaylorCutoff_geometric_le {T : ℝ} (hT : 1 ≤ T) :
    (1/3 : ℝ)^(detectorTaylorCutoff T) ≤ T^(-5 : ℝ) := by
  have hTpos : 0 < T := by linarith
  
  have hJ : 10*Real.log T ≤ (detectorTaylorCutoff T : ℝ) := Nat.le_ceil _
  have h3 : (1/2 : ℝ) ≤ Real.log 3 := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
    linarith [Real.log_two_gt_d9]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hTpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  nlinarith [mul_le_mul_of_nonneg_right h3 (show 0 ≤ (detectorTaylorCutoff T : ℝ) by positivity)]


end MathCollab.Density
