module
public import GuthMaynard.Improvement.RadialRemainder
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace GuthMaynard.Improvement

def spatialCubicMode (a : ℝ → ℂ) (μ : ℝ → ℝ) (L : ℝ) (m : ℤ × (ℤ × ℤ))
    (x₁ x₂ r : ℝ) : ℂ :=
  (a x₁*a x₂*a r)*phase (-L*((m.1:ℝ)*x₁+(m.2.1:ℝ)*x₂+(m.2.2:ℝ)*r))*
    (𝓕 (fun t => (μ t:ℂ)) (mellinFrequency r-mellinFrequency x₁)*
      𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x₁-mellinFrequency x₂)*
      𝓕 (fun t => (μ t:ℂ)) (mellinFrequency x₂-mellinFrequency r))

theorem mellinFrequency_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    mellinFrequency (x*y) = mellinFrequency x+mellinFrequency y := by
  unfold mellinFrequency
  rw [Real.log_mul hx hy]
  ring

/-- Exact radial integrand identity on positive cutoff support. The full
Fourier triple product is retained, not replaced by a mass majorant. -/
theorem spatialCubicMode_radial {a : ℝ → ℂ} (ha : ∀ x, x ≤ 0 → a x = 0)
    (μ : ℝ → ℝ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) (r v y : ℝ) :
    (r:ℂ)^2*spatialCubicMode a μ L m (r*v) (r*y) r =
      radialAmplitude a v y r*phase (-L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))*r)*ratioFourierProduct μ (v,y) := by pm_4564

/-- Actual two-dimensional scaling identity with the exact r^2 Jacobian. -/
theorem two_coordinate_scaling (f : ℝ → ℝ → ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫ v, ∫ y, (r:ℂ)^2*f (r*v) (r*y)) = ∫ x₁, ∫ x₂, f x₁ x₂ := by
  simp_rw [integral_const_mul,Measure.integral_comp_mul_left]
  simp only [Complex.real_smul]
  rw [integral_const_mul,Measure.integral_comp_mul_left (fun x₁ => ∫ x₂, f x₁ x₂) r]
  simp only [Complex.real_smul,abs_inv]
  have hc : (r:ℂ)^2*((|r|⁻¹:ℝ):ℂ)*((|r|⁻¹:ℝ):ℂ) = 1 := by
    have hh : r^2*(|r|⁻¹)^2 = 1 := by
      rw [← sq_abs r]
      field_simp
    exact_mod_cast (by nlinarith only [hh] : r^2*|r|⁻¹*|r|⁻¹ = 1)
  calc
    _ = ((r:ℂ)^2*((|r|⁻¹:ℝ):ℂ)*((|r|⁻¹:ℝ):ℂ))*(∫ x₁, ∫ x₂, f x₁ x₂) := by ring
    _ = _ := by rw [hc,one_mul]

/-- Exact iterated radial-coordinate reduction for each actual retained
spatial mode. This does not silently interchange the r and ratio integrals;
that Fubini step still requires its integrability argument. -/
theorem spatialCubicMode_radial_integrals {a : ℝ → ℂ} (ha : ∀ x, x ≤ 0 → a x = 0)
    (μ : ℝ → ℝ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a μ L m x₁ x₂ r) =
      ∫ r, ∫ v, ∫ y, radialAmplitude a v y r*
        phase (-L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))*r)*ratioFourierProduct μ (v,y) := by pm_4565 μ

end GuthMaynard.Improvement
