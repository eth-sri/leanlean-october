module

public import NearlyMinimax.PairPilotAssumptions
public import NearlyMinimax.FieldPairVariance


@[expose] public section

/-! Full two-stage variance of the paper's actual score and denominator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

def pairEvaluationCoefficient {d : ℕ} (C : ModelConstants d) (m k : ℕ) : ℝ :=
  C.densityUpper / (m : ℝ) + (k : ℝ) ^ d / (2 * (m : ℝ) * (m - 1 : ℕ))

def pairPilotVarianceBase {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) : ℝ :=
  2 * (∫ w, ‖bar w‖ ^ 2 ∂regularPairDesignMeasure θ k hk) +
    ∫ z : Ω × (CovariatePair d), ‖η z.1 z.2‖ ^ 2
      ∂μ.prod (regularPairDesignMeasure θ k hk)

theorem pairPilotVarianceBase_nonneg {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k) (μ : Measure Ω)
    (bar : CovariatePair d → PairVector)
    (η : Ω → CovariatePair d → PairVector) :
    0 ≤ pairPilotVarianceBase θ k hk μ bar η := by
  unfold pairPilotVarianceBase
  positivity

section
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ)
variable (k : ℕ) (hk : 0 < k)
variable (bar : CovariatePair d → PairVector)
variable (η : Ω → CovariatePair d → PairVector) (Cp W : ℝ)
variable {m : ℕ} (hm : 2 ≤ m) (X : Fin m → Ξ → Observation d)
variable (hind : iIndepFun X ν) (hX : ∀ i, MeasurePreserving (X i) ν (observationLaw θ))
local notation "L" => (2 * Cp^2 + 2 * Cp * W)
local notation "w" => ((k : ℝ)^d)
local notation "pairKernel" A => pairEvaluationKernel k hk A (pairPilotCoefficient bar η)

include hθ hm hind hX in
theorem pairPilotEvaluation_variance {A : PairOperator d} {E v center : ℝ}
    (hG : PairKernelMoments (μ.prod μ) θ (pairKernel A) (L^2 * (E * (C.densityUpper / w))))
    (hmean : MemLp (PairUStatistic.fieldPairMean (μ := observationLaw θ) w (pairKernel A)) 2 (μ.prod μ))
    (hvar : (∫ p, (PairUStatistic.fieldPairMean (μ := observationLaw θ) w (pairKernel A) p - center)^2 ∂μ.prod μ) ≤ v) :
    (∫ z, (PairUStatistic.fieldPairAverage m w (pairKernel A) X z - center)^2 ∂(μ.prod μ).prod ν) ≤
      2 * pairEvaluationCoefficient C m k * (L^2 * E * C.densityUpper) + 2 * v := by
  let := observationLaw_isProbability C θ hθ
  have hv := (integral_nonneg (fun _ => sq_nonneg _)).trans hvar
  have hw : 0 < w := by positivity
  have hd := zero_le_one.trans C.one_lt_densityUpper.le
  have hr := PairUStatistic.fieldPairAverage_centered_sq_le hm X hind hX
    (regularObservationLabel k hk) (regularObservationLabel_measurable k hk) hG.1 hG.2.1
    (fun _ _ _ h => by simp [pairEvaluationKernel, PilotFields.maskedPilotKernel, sameLabelKernel, h]) hw
    (div_nonneg hd hw.le) (fun i => (regularObservationLabel_mass C θ hθ k hk i).le.trans
      (regularGridProbability_cap C θ hθ k hk i))
    (show w * (C.densityUpper / w) ≤ C.densityUpper by rw [mul_div_cancel₀ _ hw.ne'])
    hv hmean hvar
  refine hr.trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity)) le_rfl)
  simpa only [mul_div_assoc, mul_left_comm w, mul_div_cancel₀ _ hw.ne', ← mul_assoc]
    using mul_le_mul_of_nonneg_left hG.2.2 hw.le

end
end NearlyMinimax
