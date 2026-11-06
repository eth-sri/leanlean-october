module
public import LaterPairs.NativeSharpRow6
public import LaterPairs.SharpPreservedCurveComparisons

@[expose] public section
noncomputable section

namespace TaoTrudgianYang2025

/-- The genuine B A image of the native Sargos D Bourgain pair. -/
theorem exponentPair_BATY2 : ExponentPair (593/1736) (235/434) := by
  convert CubicJointCount.exponentPair_sargosD_bourgain.aProcess.bProcess using 1 <;> norm_num

end TaoTrudgianYang2025

namespace Montgomery.RationalMoment

theorem sharp_row5_density_exponent {σ : ℝ} :
    3*(3066/(10848*σ-3645))*(1-σ) = 3066*(1-σ)/(3616*σ-1215) := by
  have hd : 10848*σ-3645 = 3*(3616*σ-1215) := by ring
  calc
    _ = (3*3066/(3*(3616*σ-1215)))*(1-σ) := by rw [hd]; ring
    _ = (3066/(3616*σ-1215))*(1-σ) := by
      rw [mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
    _ = _ := div_mul_eq_mul_div _ _ _

end Montgomery.RationalMoment

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

end Montgomery.RationalMoment.RightDetector.Physical
