module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaUniformityFull
public import TaoTrudgianYang2025.HeathBrownPairParameters
public import TaoTrudgianYang2025.ExponentPair
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-! Triangle and slope of Heath--Brown's exact family, including the first order. -/

noncomputable section

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

section
variable {r : ℝ} (hr : 3 ≤ r)
include r hr
theorem heathBrownPair_slope :
    1/2 ≤ heathBrownPairL r-heathBrownPairK r := by
  pm_1643
  have hx : 0 ≤ r-3 := by linarith
  have hid : heathBrownPairL r-heathBrownPairK r-1/2 =
      ((r-3)^4+12*(r-3)^3+45*(r-3)^2+62*(r-3)+20)/
        (2*r*(r-1)^2*(r+2)) := by
    unfold heathBrownPairL heathBrownPairK
    field_simp
    ring
  have hn : 0 ≤ heathBrownPairL r-heathBrownPairK r-1/2 := by
    rw [hid]
    positivity
  linarith

theorem heathBrownPair_sum_le :
    heathBrownPairK r+heathBrownPairL r ≤ 1 := by
  pm_1643
  have h3 : 0 ≤ 3*r-1 := by linarith
  have h4 : 0 ≤ r-2 := by linarith
  have hid : 1-heathBrownPairK r-heathBrownPairL r =
      (3*r-1)*(r-2)/(r*(r-1)^2*(r+2)) := by
    unfold heathBrownPairL heathBrownPairK
    field_simp
    ring
  have hn : 0 ≤ 1-heathBrownPairK r-heathBrownPairL r := by
    rw [hid]
    positivity
  linarith

theorem heathBrownPair_inTriangle :
    InExponentPairTriangle (heathBrownPairK r) (heathBrownPairL r) := by
  have hp := heathBrownPairK_pos hr
  have hs := heathBrownPair_slope hr
  have hsum := heathBrownPair_sum_le hr
  exact ⟨hp.le,by linarith,by linarith,by linarith,hsum⟩
end

end TaoTrudgianYang2025

