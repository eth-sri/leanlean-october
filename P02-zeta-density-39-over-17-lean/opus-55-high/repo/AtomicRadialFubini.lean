module
public import AtomicRadialCoordinates
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement.AtomicCubic

def radialIntegrand (a : ℝ → ℂ) (F : ℝ → ℂ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  radialAmplitude a p.1 p.2 r *
    phase (-L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))*r) * ratioFourierProduct F p

section
variable {a : ℝ → ℂ} {F : ℝ → ℂ}
include a F
theorem radialIntegrand_measurable
    (ha : Measurable a) (hF : Continuous F) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a F L m z.1 z.2) := by
  have hp := phase_measurable
  have hf := ratio_fourier_measurable hF
  unfold radialIntegrand radialAmplitude
  fun_prop

/-- Absolute integrability on the full radial/ratio space is proved from
actual compact support and Fourier mass bounds, with no Fubini premise. -/
theorem radialIntegrand_integrable
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a F L m z.1 z.2) := by
  pm_4574
  pm_4577 F
  pm_4575
  apply (integrableOn_const hE.measure_lt_top.ne (C := C*M^3)).mono'
    (radialIntegrand_measurable ha.continuous.measurable hF L m).aestronglyMeasurable
  pm_4576
  exact mul_le_mul hb' (ratio_fourier_bound hM hbF z.2) (norm_nonneg _) hC.le

/-- Fubini moves the actual radial integral inside the ratio integral.
The original three Fourier factors and the exact Jacobian are preserved. -/
theorem spatialCubicMode_radial_fubini
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hF : Continuous F) {M : ℝ} (hM : 0 ≤ M) (hbF : ∀ ξ, ‖F ξ‖ ≤ M)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a F L m x₁ x₂ r) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p * ratioFourierProduct F p := by pm_4578 hF hM hbF F
end

end GuthMaynard.Improvement.AtomicCubic
