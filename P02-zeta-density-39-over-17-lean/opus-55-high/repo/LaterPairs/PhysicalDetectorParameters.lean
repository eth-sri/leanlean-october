module
public import RetunedDetectorParameters
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector

/-- Numeric contour-detector conditions, independent of the old polynomial
counting inequalities in QuadraticWindow. -/
structure PhysicalDetectorWindow (σ a : ℝ) : Prop where
  sigma_low : 3/4 < σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  threshold : 1/8 < (3*a/4)*(σ-1/2)

section
variable {σ a : ℝ} (hw : PhysicalDetectorWindow σ a)
include σ a hw
theorem smoothingExponent_pos_physical :
    0 < smoothingExponent a := by unfold smoothingExponent; linarith [hw.a_low]

theorem smoothingExponent_lt_one_physical :
    smoothingExponent a < 1 := by unfold smoothingExponent; linarith [hw.a_high]
end

/-- The physical threshold supplies the actual contour saving directly. -/
theorem detector_error_scale_physical {σ a δ T β η : ℝ}
    (hw : PhysicalDetectorWindow σ a)
    (hδ : δ ≤ 1/8) (hT : 1 ≤ T) (hβ : σ ≤ β) :
    Real.sqrt (MathCollab.Density.Stronger.detectorX δ T)*(detectorY a T)^(1/2-β)*T^(1/6+η) ≤
      T^(-1/48+η) := by
  have hTp : 0 < T := by linarith
  pm_2755
  have hsprod : 1/4 ≤ (3*a/2)*(σ-1/2) := by nlinarith only [hw.threshold]
  pm_2756
  pm_2757 MathCollab.Density.Stronger.detectorX

end Montgomery.RationalMoment.RightDetector
