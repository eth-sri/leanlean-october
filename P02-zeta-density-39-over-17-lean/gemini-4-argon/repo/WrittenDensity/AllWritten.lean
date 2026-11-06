module
public import WrittenDensity.Common

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity
open MathCollab.Density

theorem source_oct2_mixed_4 {σ ε : ℝ} (_hlo : (19/22) ≤ σ)
    (_hhi : σ ≤ (23/26)) (_hε : 0 < ε) :
    DensityBound σ ((24 + (-24 * σ)) / (-11 + (30 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  by_cases hc0 : σ ≤ (2905/3354)
  · apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) hc0 _hε)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  · apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

