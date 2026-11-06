module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaClosedSlopeInverseAdapter
public import TaoTrudgianYang2025.BetaBufferedCoreStationary

@[expose] public section

/-!
# Exact integer partition of the genuine nonstationary core

The two endpoint integers are derived from the one-sided slopes of the
original phase. They are included in the nonstationary complement, even
when an endpoint slope is exactly an integer physical frequency.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def modelPhaseEndpointLower (F : ℝ → ℝ) (T N : ℝ) : ℤ :=
  ⌊(T/N)*modelPhaseClosedSlope F 2⌋

def modelPhaseEndpointUpper (F : ℝ → ℝ) (T N : ℝ) : ℤ :=
  ⌈(T/N)*modelPhaseClosedSlope F 1⌉

theorem modelPhaseEndpoints_inside_core {σ δ T N : ℝ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ 1 δ) (hT : 0 ≤ T) (hN : 0 < N) :
    modelPhaseCoreLower σ δ T N ≤ modelPhaseEndpointLower F T N ∧
      modelPhaseEndpointUpper F T N ≤ modelPhaseCoreUpper δ T N := by
  have hl := abs_le.mp (modelPhaseClosedSlope_model_error hF
    (show (2 : ℝ) ∈ phaseInterval by norm_num [phaseInterval]))
  have hu := abs_le.mp (modelPhaseClosedSlope_model_error hF
    (show (1 : ℝ) ∈ phaseInterval by norm_num [phaseInterval]))
  rw [Real.one_rpow] at hu
  constructor
  · exact Int.floor_mono (mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ)^(-σ)-δ ≤
      modelPhaseClosedSlope F 2) (div_nonneg hT hN.le))
  · exact Int.ceil_mono (mul_le_mul_of_nonneg_left (by linarith : modelPhaseClosedSlope F 1 ≤
      1+δ) (div_nonneg hT hN.le))

end TaoTrudgianYang2025
