module
public import MathCollab.Density.DetectorContour
public import MathCollab.Density.DetectorEstimates
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex MeasureTheory Set Filter
open MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The exact infinite contour identity, with no Weyl premise or fixed relation
between the independent mollifier and smoothing parameters. -/
theorem smoothedDetector_contour_identity {ρ : ℂ} {X Y : ℝ}
    (hY : 1 ≤ Y) (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re < 1)
    (hZero : riemannZeta ρ = 0) :
    smoothedDetector ρ X (1/Y) = detectorResidue ρ X Y +
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by pm_4277 integrable_detectorKernel_left integrable_detectorKernel_right tendsto_detector_horizontal_integral detector_finite_rectangle_kernel smoothedDetector_eq_rightContour

/-- Termwise identification preserves the original integer coefficients. -/
theorem smoothedDetector_term_eq (ρ : ℂ) (X Y : ℝ) (n : ℕ) :
    LSeries.term (mollifierDirichletCoeff X) ρ n * Complex.exp (-((n : ℝ)*(1/Y : ℝ))) =
      (mollifierCoefficient X n : ℂ)*(n : ℂ)^(-ρ)*(Real.exp (-(n : ℝ)/Y) : ℂ) := by
  rw [LSeries.term_def₀ (mollifierDirichletCoeff_zero X)]
  simp [mollifierDirichletCoeff, div_eq_mul_inv, Complex.ofReal_exp]

/-- Absolute convergence is proved before the series is used in the detector. -/
theorem summable_zeta_detector_series {ρ : ℂ} (X : ℝ) {Y : ℝ}
    (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ => (mollifierCoefficient X n : ℂ)*(n : ℂ)^(-ρ)*
      (Real.exp (-(n : ℝ)/Y) : ℂ)) :=
  (summable_smoothedDetector (X := X) (one_div_pos.mpr hY) hρ).congr
    (fun n => smoothedDetector_term_eq ρ X Y n)

end MathCollab.Density
