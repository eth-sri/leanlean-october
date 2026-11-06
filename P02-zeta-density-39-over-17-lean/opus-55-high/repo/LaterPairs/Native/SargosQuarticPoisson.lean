module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SargosQuarticPhase
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                         
                                                                          
                                                                          

noncomputable section

open Set Filter MeasureTheory Expdb GafniTao
open scoped ContDiff Topology FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem sargos_ford_character_eq_fourier (x : ℝ) :
    fordAdditiveCharacter x = (𝐞 x : ℂ) := by
  rw [fordAdditiveCharacter,Real.fourierChar_apply]
  congr 1
  push_cast
  ring

def sargosQuarticWeightedKernel (χ : ℝ → ℝ) (N α γ x : ℝ) : ℂ :=
  (χ (x/N) : ℂ)*(𝐞 (sargosQuarticPhase α γ x) : ℂ)

section
variable {χ : ℝ → ℝ}
include χ
theorem sargosQuarticWeightedKernel_contDiff
    (hχ : ContDiff ℝ ∞ χ) (N α γ : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticWeightedKernel χ N α γ) := by
  unfold sargosQuarticWeightedKernel sargosQuarticPhase
  simp only [Real.fourierChar_apply]
  have hw : ContDiff ℝ ∞ (fun x : ℝ => χ (x/N)) := hχ.comp (contDiff_id.div_const N)
  have hp : ContDiff ℝ ∞ (fun x : ℝ => 2*Real.pi*(α*x^2+γ*x^4)) := by fun_prop
  pm_7389 hw

theorem sargosQuarticWeightedKernel_zero_of_not_mem {N x : ℝ}
    (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (hx : x ∉ Icc N (2*N)) (α γ : ℝ) :
    sargosQuarticWeightedKernel χ N α γ x = 0 := by pm_1632 sargosQuarticWeightedKernel

theorem sargosQuarticWeightedKernel_hasCompactSupport {N : ℝ}
    (hs : tsupport χ ⊆ Ioo 1 2) (hN : 0 < N) (α γ : ℝ) :
    HasCompactSupport (sargosQuarticWeightedKernel χ N α γ) :=
  HasCompactSupport.intro isCompact_Icc
    (fun _ hx => sargosQuarticWeightedKernel_zero_of_not_mem hs hN hx α γ)
end

end TaoTrudgianYang2025
