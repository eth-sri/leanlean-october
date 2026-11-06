module
import Mathlib
public import MathCollab.Density.DetectorDyadic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open Real Filter
open scoped BigOperators Topology
noncomputable section
namespace MathCollab.Density

def detectorTaylorCutoff (T : ℝ) : ℕ := ⌈10*Real.log T⌉₊

/- A coarse natural-cutoff bound, sufficient for all family counts. -/
theorem firstDetectorCutoff_eventually_le_sq :
    ∀ᶠ T : ℝ in atTop, (firstDetectorCutoff T : ℝ) ≤ T^2 := by
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (2 : ℝ), hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))] with T hT hlog
  have hTpos : 0 < T := by linarith
  have hq : (Real.log T)^2 < T/2 := (div_lt_iff₀ hTpos).mp hlog |>.trans_eq (by ring)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ T*(Real.log T)^2 by positivity)
  change (firstDetectorCutoff T : ℝ) < T*(Real.log T)^2+1 at hc
  nlinarith



theorem detectorTaylorCutoff_le_log {T : ℝ} (hlog : 1 ≤ Real.log T) :
    (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 10*Real.log T by linarith)
  change (detectorTaylorCutoff T : ℝ) < 10*Real.log T+1 at h
  linarith

/- The chosen Taylor cutoff gives a polynomially small geometric factor. -/
theorem detectorTaylorCutoff_geometric_le {T : ℝ} (hT : 1 ≤ T) :
    (1/3 : ℝ)^(detectorTaylorCutoff T) ≤ T^(-5 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hJ : 10*Real.log T ≤ (detectorTaylorCutoff T : ℝ) := Nat.le_ceil _
  have h3 : (1/2 : ℝ) ≤ Real.log 3 := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
    linarith [Real.log_two_gt_d9]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hTpos]
  apply Real.exp_le_exp.mpr
  simp_all <;> nlinarith




