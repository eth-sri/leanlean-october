module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.IntegerClosedIntervalPrefix
public import LaterPairs.Native.RobertSargosShiftBoundary
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                          

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

def robertSargosZeroRSource (f : ℝ → ℝ) (M : ℕ) (h q : ℤ) : ℂ :=
  ∑ m ∈ robertSargosMOverlap M h q 0,
    fordAdditiveCharacter (robertSargosSymmetricDifference f (m+q) h-
      robertSargosSymmetricDifference f m h)

theorem robertSargos_zero_r_positive_interval (M : ℕ) (h q : ℤ) (hq : 0 ≤ q) :
    robertSargosMOverlap M h q 0 = Finset.Icc (h+1) ((M:ℤ)-h-q) := by
  rw [robertSargos_m_overlap_zero_source]
  grind

section
variable (f : ℝ → ℝ) (M : ℕ) (h q : ℤ)
include f M h q
theorem robertSargos_zero_r_source_neg :
    robertSargosZeroRSource f M h (-q) = star (robertSargosZeroRSource f M h q) := by
  unfold robertSargosZeroRSource
  pm_7763
  symm
  pm_8905 q
  · intro m hm
    pm_6933
  grind
  · intro m hm
    refine ⟨m-q,?_,by omega⟩
    pm_6933
  · intro m _
    rw [conj_fordAdditiveCharacter]
    congr 1
    simp only [Int.cast_add,Int.cast_neg,add_neg_cancel_right]
    ring

theorem norm_robertSargos_zero_r_source_neg :
    ‖robertSargosZeroRSource f M h (-q)‖ = ‖robertSargosZeroRSource f M h q‖ := by
  rw [robertSargos_zero_r_source_neg,norm_star]
end

end TaoTrudgianYang2025
