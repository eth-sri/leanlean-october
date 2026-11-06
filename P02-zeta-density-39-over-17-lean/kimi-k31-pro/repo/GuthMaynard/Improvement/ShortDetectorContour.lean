module
public import MathCollab.Density.DetectorContour

@[expose] public section
open Complex MeasureTheory Set Filter
open MathCollab.Density MathCollab.Density.ZetaGrowth MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

theorem short_detector_finite_rectangle_residue {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 1/2 < ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral'
      (fun s => detectorContourNumerator ρ X Y s / (s - (1 - ρ)))
      ((a : ℂ) - (R : ℂ)*I) (((1/2 : ℝ) : ℂ) + (R : ℂ)*I) =
        detectorResidue ρ X Y :=
  detector_finite_rectangle_residue hY hβLower hβUpper hR hZero

theorem short_detector_finite_rectangle_kernel {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 1/2 < ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y :=
  detector_finite_rectangle_kernel hY hβLower hβUpper hR hZero

theorem short_detector_finite_rectangle_kernel_nine_thirteenths
    {ρ : ℂ} {X Y R : ℝ} (hY : 0 < Y) (hβLower : 9/13 ≤ ρ.re)
    (hβUpper : ρ.re < 1) (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y :=
  short_detector_finite_rectangle_kernel hY (by linarith) hβUpper hR hZero

end GuthMaynard.Improvement
