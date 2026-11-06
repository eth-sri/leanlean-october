module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                    
                                                                     
                                                                        

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosLinear (r q h n : ℝ) : ℝ := r*n+h*q

def robertSargosQuadratic (r q h n : ℝ) : ℝ :=
  r*n^2+2*h*q*n+h*q^2

def robertSargosReduced (r q₁ q₂ h₁ h₂ d : ℝ) : ℝ :=
  r*d^2+2*h₁*q₁*d+h₁*q₁^2-h₂*q₂^2

def robertSargosTaylorQuadratic (r q h n : ℝ) : ℝ :=
  h*q^2+2*h*q*n-r*n^2-r*h^2-r^2*h

section
variable {r q₁ q₂ h₁ h₂ d : ℝ} (h : r*d+h₁*q₁-h₂*q₂ = 0)
include r q₁ q₂ h₁ h₂ d h
theorem robertSargos_reduced_symmetric :
    robertSargosReduced r q₁ q₂ h₁ h₂ d =
      (h₁*q₁+h₂*q₂)*d+h₁*q₁^2-h₂*q₂^2 := by
  unfold robertSargosReduced
  grind

theorem robertSargos_reduced_factor :
    r*robertSargosReduced r q₁ q₂ h₁ h₂ d =
      h₂*(h₂-r)*q₂^2-h₁*(h₁-r)*q₁^2 := by
  unfold robertSargosReduced
  have he : r*d = h₂*q₂-h₁*q₁ := by grind
  grind
end

end TaoTrudgianYang2025
