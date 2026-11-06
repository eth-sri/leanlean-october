module
public import FiniteCubicBasics
public import GuthMaynard.Improvement.RetainedRadialAssembly
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ContDiff
namespace GuthMaynard.Improvement.AtomicCubic

/-- A general compact-frequency profile; no ordinary time density is assumed. -/
def ratioFourierProduct (F : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  F (-mellinFrequency p.1)*F (mellinFrequency p.1-mellinFrequency p.2)*F (mellinFrequency p.2)

theorem ratio_fourier_measurable {F : ℝ → ℂ} (hF : Continuous F) : Measurable (ratioFourierProduct F) := by
  unfold ratioFourierProduct mellinFrequency
  fun_prop

theorem ratio_fourier_bound {F : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ ξ, ‖F ξ‖ ≤ M) (p : ℝ × ℝ) : ‖ratioFourierProduct F p‖ ≤ M^3 := by
  unfold ratioFourierProduct
  pm_2717 M

def spatialCubicMode (a : ℝ → ℂ) (F : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ))
    (x₁ x₂ r : ℝ) : ℂ :=
  (a x₁*a x₂*a r)*phase (-L*((m.1:ℝ)*x₁+(m.2.1:ℝ)*x₂+(m.2.2:ℝ)*r))*
    (F (mellinFrequency r-mellinFrequency x₁)*
      F (mellinFrequency x₁-mellinFrequency x₂)*
      F (mellinFrequency x₂-mellinFrequency r))
section
variable {a : ℝ → ℂ} (ha : ∀ x, x ≤ 0 → a x = 0) (F : ℝ → ℂ) (L : ℝ) (m : ℤ × (ℤ × ℤ))
include a ha F L m
/-- Exact radial integrand identity on positive cutoff support. The full
Fourier triple product is retained, not replaced by a mass majorant. -/
theorem spatialCubicMode_radial (r v y : ℝ) :
    (r:ℂ)^2*spatialCubicMode a F L m (r*v) (r*y) r =
      radialAmplitude a v y r*phase (-L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))*r)*ratioFourierProduct F (v,y) := by pm_4564

/-- Exact iterated radial-coordinate reduction for each actual retained
spatial mode. This does not silently interchange the r and ratio integrals;
that Fubini step still requires its integrability argument. -/
theorem spatialCubicMode_radial_integrals :
    (∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a F L m x₁ x₂ r) =
      ∫ r, ∫ v, ∫ y, radialAmplitude a v y r*
        phase (-L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))*r)*ratioFourierProduct F (v,y) := by pm_4565 F
end

end GuthMaynard.Improvement.AtomicCubic
