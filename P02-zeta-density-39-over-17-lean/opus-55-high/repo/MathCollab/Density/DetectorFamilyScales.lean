module
public import MathCollab.Density.DetectorDyadic
public import Mathlib.Analysis.Complex.ExponentialBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def detectorTaylorCutoff (T : ℝ) : ℕ := ⌈10*Real.log T⌉₊

/-- A coarse natural-cutoff bound, sufficient for all family counts. -/
theorem firstDetectorCutoff_eventually_le_sq :
    ∀ᶠ T : ℝ in atTop, (firstDetectorCutoff T : ℝ) ≤ T^2 := by
  pm_331
  filter_upwards [eventually_ge_atTop (2 : ℝ), hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))] with T hT hlog
  have hTpos : 0 < T := by linarith
  have hq : (Real.log T)^2 < T/2 := (div_lt_iff₀ hTpos).mp hlog |>.trans_eq (by ring)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ T*(Real.log T)^2 by positivity)
  change (firstDetectorCutoff T : ℝ) < T*(Real.log T)^2+1 at hc
  nlinarith

section
variable {T : ℝ}
include T
/-- Explicit O(log T) size of the fixed dyadic list. -/
theorem detectorDyadicCount_le_log (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hK : (firstDetectorCutoff T : ℝ) ≤ T^2) :
    (detectorDyadicCount T : ℝ) ≤ 5*Real.log T := by pm_4323 firstDetectorCutoff

theorem detectorTaylorCutoff_le_log (hlog : 1 ≤ Real.log T) :
    (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 10*Real.log T by linarith)
  change (detectorTaylorCutoff T : ℝ) < 10*Real.log T+1 at h
  linarith

/-- The chosen Taylor cutoff gives a polynomially small geometric factor. -/
theorem detectorTaylorCutoff_geometric_le (hT : 1 ≤ T) :
    (1/3 : ℝ)^(detectorTaylorCutoff T) ≤ T^(-5 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hJ : 10*Real.log T ≤ (detectorTaylorCutoff T : ℝ) := Nat.le_ceil _
  have h3 : (1/2 : ℝ) ≤ Real.log 3 := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
    linarith [Real.log_two_gt_d9]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hTpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  nlinarith [mul_le_mul_of_nonneg_right h3 (show 0 ≤ (detectorTaylorCutoff T : ℝ) by positivity)]
end

set_option hygiene false in
macro "pf_110" x1:ident x2:term:max x3:ident x4:ident x5:term:max x6:term:max : tactic => `(tactic| (
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at ht
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    $x1:ident, ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1/$x2:term by norm_num))]
    with T hT hlog hK hsmall
  have hD := $x3:ident (by linarith) hlog hK
  refine ⟨hT, hlog, hK, hD, detectorTaylorCutoff_le_log hlog, ?_⟩
  have hTpos : 0 < T := by linarith
  have hDpos : (0 : ℝ) < $x4:ident T := by unfold $x4:ident; positivity
  rw [Real.rpow_neg_one, ← one_div]
  apply (le_div_iff₀ (by positivity : 0 < ($x5:term)*($x4:ident T : ℝ))).2
  have hl : Real.log T < T/$x2:term := (div_lt_iff₀ hTpos).mp hsmall |>.trans_eq (by ring)
  rw [show 3*(1/T)*(($x5:term)*($x4:ident T : ℝ)) = ($x6:term)*($x4:ident T : ℝ)/T by ring]
  apply (div_le_iff₀ hTpos).2
  nlinarith))
/-- All scales are selected before beta, gamma or an actual zero varies. -/
theorem detector_family_scales_eventually :
    ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ 1 ≤ Real.log T ∧
      (firstDetectorCutoff T : ℝ) ≤ T^2 ∧
      (detectorDyadicCount T : ℝ) ≤ 5*Real.log T ∧
      (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T ∧
      3*T^(-1 : ℝ) ≤ 1/(4*(detectorDyadicCount T : ℝ)) := by pf_110 firstDetectorCutoff_eventually_le_sq 60 detectorDyadicCount_le_log detectorDyadicCount 4 12

end MathCollab.Density
