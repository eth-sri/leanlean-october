module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaTaylorPastedUniform
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Positive compact bounds for the genuine closed endpoint slopes

This includes the original one-sided endpoint convention. It does not
differentiate an arbitrary exterior extension of the original phase.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

section
variable {F : ℝ → ℝ} {σ δ : ℝ}
include F σ δ
theorem modelPhaseClosedSlope_positive_window {P : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    modelPhaseClosedSlope F u ∈ Icc ((2 : ℝ)^(-σ)/2) 2 := by
  have he := abs_le.mp (modelPhaseClosedSlope_model_error hF hu)
  have hp : 0 < u := zero_lt_one.trans_le hu.1
  have hlow := Real.rpow_le_rpow_of_nonpos hp hu.2 (neg_nonpos.mpr hσ.le)
  have hhigh := Real.rpow_le_one_of_one_le_of_nonpos hu.1 (neg_nonpos.mpr hσ.le)
  pm_4998 hd₁ hδ.trans hd₂
  have hbase : 0 < (2 : ℝ)^(-σ) := by positivity
  grind

theorem modelPhaseClosedSlope_endpoint_width
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) :
    modelPhaseCurvatureLower σ ≤ modelPhaseClosedSlope F 1-modelPhaseClosedSlope F 2 := by
  simpa only [show (2 : ℝ)-1 = 1 by norm_num,mul_one] using
    modelPhaseClosedSlope_drop hσ hδ hF
      (u := 1) (v := 2) (by norm_num) (by norm_num) (by norm_num)
end

end TaoTrudgianYang2025
