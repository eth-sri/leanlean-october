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
import WeylPort.Analytic.RealLaplace

public section
open Complex MeasureTheory Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

/-- Continuity on every fixed negative line between -1/2 and zero. The strict
upper bound excludes the Gamma pole; no imaginary-part restriction is needed. -/
theorem short_continuous_Gamma_detector_strip {a : ℝ} (ha : -(1/2 : ℝ) ≤ a)
    (ha' : a < 0) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) := by
  pm_4331
  simp_all
  · have hm' : (1 : ℝ) ≤ m := by aesop
    linarith

/-- Uniform Gamma mass down to beta=9/13. The majorant is exactly twice the
already audited integrable majorant; the new negative-strip estimate supplies
its pointwise domination, including ordinate zero. -/
theorem short_uniform_detector_gamma_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 9/13 ≤ β → β ≤ 1 →
      Integrable (fun t : ℝ => Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)) ∧
      Integrable (fun t : ℝ => (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ∧
      (∫ t : ℝ, (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ≤ C := by
  have hmajor : Integrable (fun t => 2*detectorGammaMajorant t) :=
    integrable_detectorGammaMajorant.const_mul 2
  have hnonneg : 0 ≤ ∫ t : ℝ, 2*detectorGammaMajorant t :=
    integral_nonneg (fun t => by dsimp [detectorGammaMajorant]; positivity)
  refine ⟨(∫ t : ℝ, 2*detectorGammaMajorant t)+1, by linarith, ?_⟩
  pm_4333
  have hg : Continuous g := short_continuous_Gamma_detector_strip (by linarith) (by linarith)
  have hbound : ∀ t : ℝ, (1+|t|)*‖g t‖ ≤ 2*detectorGammaMajorant t := by
    intro t
    pm_4569 β h
    have hh : ‖g t‖ ≤ 96*(1+|t|)*Real.exp (-|t|) :=
      h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity))
    pm_7439 hh
    dsimp [detectorGammaMajorant]
    convert hm using 1; ring
  pm_4335 hmajor.mono'
  pm_4334
  pm_8782 hmajor

section
variable {ρ : ℂ} {X Y : ℝ} (hY : 0 < Y)
include ρ X Y hY
/-- The right contour is absolutely integrable for independent X and Y. -/
theorem short_integrable_detectorKernel_right (hρ : 9/13 ≤ ρ.re) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)) := by
  pm_4317 short_verticalIntegrable_mellin_smoothedDetector
  have hp : Continuous (fun t : ℝ => (Y : ℂ)^(line t)) := by
    apply Continuous.cpow continuous_const (by dsimp [line]; fun_prop)
    intro t
    left; simpa using hY
  have hb : ∀ t : ℝ, ‖(Y : ℂ)^(line t)‖ ≤ Y^(1/2 : ℝ) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp [line]
  pm_4316

/-- The shifted contour is absolutely integrable using only linear zeta growth. -/
theorem short_integrable_detectorKernel_left (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by pf_35 short_uniform_detector_gamma_mass.choose_spec.2 short_continuous_Gamma_detector_strip
end

/-- Both horizontal integrals vanish as the independent rectangle height grows. -/
theorem short_tendsto_detector_horizontal_integral {ρ : ℂ} {X Y ε : ℝ}
    (hY : 1 ≤ Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun R : ℝ => ∫ u in (1/2-ρ.re)..(1/2 : ℝ),
      detectorKernel ρ X Y ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)) atTop (𝓝 0) := by pm_4318

end GuthMaynard.Improvement
