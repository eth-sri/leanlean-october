module
public import GuthMaynard.Improvement.ShortDetectorGamma
public import GuthMaynard.Improvement.ShortDetectorMellin
public import MathCollab.Density.DetectorEstimates

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

theorem short_continuous_Gamma_detector_strip {a : ℝ} (ha : -(1/2 : ℝ) ≤ a)
    (ha' : a < 0) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) :=
  continuous_Gamma_detector_strip ha ha'

theorem short_uniform_detector_gamma_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 9/13 ≤ β → β ≤ 1 →
      Integrable (fun t : ℝ => Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)) ∧
      Integrable (fun t : ℝ => (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ∧
      (∫ t : ℝ, (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ≤ C :=
  uniform_detector_gamma_mass

theorem short_integrable_detectorKernel_right {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 9/13 ≤ ρ.re) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)) :=
  integrable_detectorKernel_right hY hρ

theorem short_integrable_detectorKernel_left {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) :=
  integrable_detectorKernel_left hY hβ hβ'

theorem short_tendsto_detector_horizontal_integral {ρ : ℂ} {X Y ε : ℝ}
    (hY : 1 ≤ Y) (hβ : 9/13 ≤ ρ.re) (hβ' : ρ.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun R : ℝ => ∫ u in (1/2-ρ.re)..(1/2 : ℝ),
      detectorKernel ρ X Y ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)) atTop (𝓝 0) :=
  tendsto_detector_horizontal_integral hY hβ hβ' hε

end GuthMaynard.Improvement
