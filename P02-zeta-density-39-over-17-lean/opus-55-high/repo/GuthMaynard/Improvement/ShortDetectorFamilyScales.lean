module
public import MathCollab.Density.DetectorFamilyScales
public import GuthMaynard.Improvement.ShortDetectorDyadic
public import Mathlib.Analysis.Complex.ExponentialBounds
import WeylPort.Analytic.RealLaplace

public section

open Real Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- A coarse natural-cutoff bound, sufficient for all family counts. -/
theorem shortDetectorCutoff_eventually_le_sq :
    ∀ᶠ T : ℝ in atTop, (shortDetectorCutoff T : ℝ) ≤ T^2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), firstDetectorCutoff_eventually_le_sq] with T hT hK
  have hr : T^(1/2:ℝ) ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT (show (1/2:ℝ) ≤ 1 by norm_num)
  have hc : shortDetectorCutoff T ≤ firstDetectorCutoff T :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right hr (sq_nonneg _))
  exact (show (shortDetectorCutoff T : ℝ) ≤ firstDetectorCutoff T by exact_mod_cast hc).trans hK

/-- Explicit O(log T) size of the fixed dyadic list. -/
theorem shortDetectorDyadicCount_le_log {T : ℝ} (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hK : (shortDetectorCutoff T : ℝ) ≤ T^2) :
    (shortDetectorDyadicCount T : ℝ) ≤ 5*Real.log T := by pm_4323 shortDetectorCutoff

/-- All scales are selected before beta, gamma or an actual zero varies. -/
theorem short_detector_family_scales_eventually :
    ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ 1 ≤ Real.log T ∧
      (shortDetectorCutoff T : ℝ) ≤ T^2 ∧
      (shortDetectorDyadicCount T : ℝ) ≤ 5*Real.log T ∧
      (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T ∧
      3*T^(-1 : ℝ) ≤ 1/(6*(shortDetectorDyadicCount T : ℝ)) := by pf_110 shortDetectorCutoff_eventually_le_sq 90 shortDetectorDyadicCount_le_log shortDetectorDyadicCount 6 18

end GuthMaynard.Improvement
