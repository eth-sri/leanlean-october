module
/-
Adapted from the verified MathCollab.Density.DetectorEstimates and DetectorGamma.
The literal kernel and horizontal majorant are reused unchanged. The left-line
Gamma domination uses ShortDetectorGamma, and right-line Mellin integrability
uses ShortDetectorMellin, to cover beta >= 9/13. No original source is modified.
-/
public import GuthMaynard.Improvement.ShortDetectorGamma
public import GuthMaynard.Improvement.ShortDetectorMellin
public import MathCollab.Density.DetectorEstimates

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- Continuity on every fixed negative line between -1/2 and zero. The strict
upper bound excludes the Gamma pole; no imaginary-part restriction is needed. -/
theorem short_continuous_Gamma_detector_strip {a : ℝ} (ha : -(1/2 : ℝ) ≤ a)
    (ha' : a < 0) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) :=
  continuous_Gamma_detector_strip_of_lt_zero ha ha'

/-- Uniform Gamma mass down to beta=9/13. The majorant is exactly twice the
already audited integrable majorant; the new negative-strip estimate supplies
its pointwise domination, including ordinate zero. -/
theorem short_uniform_detector_gamma_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 9/13 ≤ β → β ≤ 1 →
      Integrable (fun t : ℝ => Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)) ∧
      Integrable (fun t : ℝ => (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ∧
      (∫ t : ℝ, (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ≤ C :=
  uniform_detector_gamma_mass_of_half_lt (by norm_num)


/-- The shifted contour is absolutely integrable using only linear zeta growth. -/
theorem short_integrable_detectorKernel_left {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) :=
  integrable_detectorKernel_left_of_half_lt hY (by linarith) hβ'


end GuthMaynard.Improvement
