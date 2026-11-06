module
/-
Finite contour proof generalized from audited Density.DetectorContour.
The inherited analytic residue argument is adapted there from McColm's MIT
TypeIICoverage (pin2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be).
No original density sources are changed. Numerator, kernel and residue are the
same literal definitions; only the unnecessarily strong lower bound is relaxed.
-/
public import MathCollab.Density.DetectorContour
import WeylPort.Analytic.RealLaplace

public section
open Complex MeasureTheory Filter
open MathCollab.Density MathCollab.Density.Contour
open scoped Topology
namespace GuthMaynard.Improvement

section
variable {ρ : ℂ} {X Y R : ℝ} (hY : 0 < Y) (hβLower : 1/2 < ρ.re) (hβUpper : ρ.re < 1) (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0)
include ρ X Y R hY hβLower hβUpper hR hZero
set_option maxHeartbeats 800000 in
/-- Finite-height rectangle shift.  The apparent pole at zero has already
been removed, so the rectangle crosses exactly the zeta pole `1 - ρ`. -/
theorem short_detector_finite_rectangle_residue :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral'
      (fun s => detectorContourNumerator ρ X Y s / (s - (1 - ρ)))
      ((a : ℂ) - (R : ℂ)*I) (((1/2 : ℝ) : ℂ) + (R : ℂ)*I) =
        detectorResidue ρ X Y := by
  pm_4252
  have hpInterior : Rectangle z w ∈ nhds p := by
    pm_4254
    pm_7845
    · simp [p, z, w]
      grind
  have hRectSubset : Rectangle z w ⊆ {s : ℂ | -(1 : ℝ) < s.re} := by
    pm_4253
    have hzReal : z.re = a := by aesop
    grind
  pm_4251

/-- Exact finite shift for the literal kernel; both exceptional points are
strictly interior for every independently chosen R>|Im(rho)|. -/
theorem short_detector_finite_rectangle_kernel :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y := by
  pm_8395
  pm_4256
  pm_5872
  pm_4257
  pm_8248 short_detector_finite_rectangle_residue
  pm_4255
end

/-- The actual detector kernel, including its exact mollifier and residue,
satisfies the same finite shift for beta>=9/13. -/
theorem short_detector_finite_rectangle_kernel_nine_thirteenths
    {ρ : ℂ} {X Y R : ℝ} (hY : 0 < Y) (hβLower : 9/13 ≤ ρ.re)
    (hβUpper : ρ.re < 1) (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y :=
  short_detector_finite_rectangle_kernel hY (by linarith) hβUpper hR hZero

end GuthMaynard.Improvement
