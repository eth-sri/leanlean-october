module
public import QuadraticWindow
public import MathCollab.Density.Stronger.InitialDetector
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Filter
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

def smoothingExponent (a : ℝ) : ℝ := 3*a/2

def detectorY (a T : ℝ) : ℝ := T^(smoothingExponent a)

section
variable {σ a : ℝ} (hw : QuadraticWindow σ a)
include σ a hw
theorem smoothingExponent_pos :
    0 < smoothingExponent a := by unfold smoothingExponent; linarith [hw.a_low]

theorem smoothingExponent_lt_one :
    smoothingExponent a < 1 := by unfold smoothingExponent; linarith [hw.a_high]
end

/-- The initial all-zero contour detector works at the retuned upper length
3a/2. The right-hand polynomial parameter conditions supply its real saving. -/
theorem detector_error_scale {σ a δ T β η : ℝ}
    (hw : QuadraticWindow σ a) (hs : 7/9 ≤ σ)
    (hδ : δ ≤ 1/8) (hT : 1 ≤ T) (hβ : σ ≤ β) :
    Real.sqrt (detectorX δ T)*(detectorY a T)^(1/2-β)*T^(1/6+η) ≤
      T^(-1/48+η) := by
  have hTp : 0 < T := by linarith
  pm_2755
  have hm := mul_nonneg ha.le (show 0 ≤ 9*σ-7 by grind)
  have hsprod : 1/4 ≤ (3*a/2)*(σ-1/2) := by nlinarith only [hw.first,hm]
  pm_2756
  pm_2757 detectorX

end Montgomery.RationalMoment.RightDetector
