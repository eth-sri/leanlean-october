module

public import NearlyMinimax.PaperPairRisk
public import NearlyMinimax.SampleThirds


@[expose] public section

/-! A Borel pair estimator constructed directly from observable coefficient
fields, with its actual original-sample risk and minimax comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000

def coefficientPairStatistic {d : ℕ} (C : ModelConstants d) (m k : ℕ) (hk : 0 < k)
    (c : ObservedSample d m → CovariatePair d → PairVector)
    (z : (((ObservedSample d m) × ObservedSample d m) × ObservedSample d m)) : ℝ :=
  stabilizedRatio C.varianceLower C.varianceUpper (1 / 4)
    (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (coefficientPairNumeratorKernel k hk c)
      (fun i x => x i))
    (PairUStatistic.fieldPairAverage m ((k : ℝ) ^ d) (rawModelPairNoise k hk c)
      (fun i x => x i)) z

theorem coefficientPairStatistic_measurable {d : ℕ} (C : ModelConstants d) (m k : ℕ)
    (hk : 0 < k) {c : ObservedSample d m → CovariatePair d → PairVector}
    (hmc : Measurable (fun z : ObservedSample d m × (CovariatePair d) => c z.1 z.2)) :
    Measurable (coefficientPairStatistic C m k hk c) := by
  apply stabilizedRatio_measurable
  · exact PairUStatistic.fieldPairAverage_measurable _ _
      (pairEvaluationKernel_measurable k hk hmc (observationPairScoreOperator_measurable_apply 0))
      _ (fun i => measurable_pi_apply i)
  · exact PairUStatistic.fieldPairAverage_measurable _ _
      (pairEvaluationKernel_measurable k hk hmc (observationPairNoiseOperator_measurable_apply d))
      _ (fun i => measurable_pi_apply i)

def coefficientPairEstimator {d n : ℕ} (C : ModelConstants d) (k : ℕ) (hk : 0 < k)
    (c : (Fin (threeBlockSize n) → Observation d) → CovariatePair d → PairVector)
    (hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
      (CovariatePair d) => c z.1 z.2)) : Estimator d n :=
  threeBlockEstimator (coefficientPairStatistic C (threeBlockSize n) k hk c)
    (coefficientPairStatistic_measurable C _ k hk hmc)

section
variable {d n : ℕ} (C : ModelConstants d)

/-- Independent pilots and evaluation data arise from the original iid sample;
the coefficient field is observable and carries no unknown parameter. -/
theorem coefficientPairEstimator_rms_bound
    (θ : RegressionParameter d) (hθ : Admissible C θ) (hn : 6 ≤ n)
    (k : ℕ) (hk : 0 < k)
    (c : (Fin (threeBlockSize n) → Observation d) → CovariatePair d → PairVector)
    (hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
      (CovariatePair d) => c z.1 z.2))
    (bar : CovariatePair d → PairVector)
    (η : (Fin (threeBlockSize n) → Observation d) → CovariatePair d → PairVector)
    (Cp W b : ℝ) (heq : c = pairPilotCoefficient bar η)
    (hp : PairPilotAssumptions θ k hk (sampleLaw θ (threeBlockSize n)) bar η
      Cp W (Cp ^ 2 * W / (n : ℝ)))
    (hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, bar w 0 = 1)
    (hresidual : ∀ᵐ w ∂regularPairDesignMeasure θ k hk,
      |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤ b) :
    meanSquaredRisk (coefficientPairEstimator C k hk c hmc) θ ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
        (b ^ 2 + pairFluctuationScale (d := d) n k * (1 + W))) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ (threeBlockSize n)
  have hi := iIndepFun_pi (μ := fun _ : Fin (threeBlockSize n) => observationLaw θ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  have hm := fun i => measurePreserving_eval (fun _ : Fin (threeBlockSize n) => observationLaw θ) i
  have h := paper_common_pair_rms (sampleLaw θ (threeBlockSize n)) (sampleLaw θ (threeBlockSize n))
    C θ hθ k hk bar η Cp W (by omega : 0 < n) (threeBlockSize_two_le hn)
    (by norm_num : (0 : ℝ) < 1 / 4) (threeBlockSize_fraction hn) hp hfirst
    (fun i x => x i) hi hm b hresidual
  unfold coefficientPairEstimator
  rw [threeBlockEstimator_risk_eq C θ hθ]
  have hnum : coefficientPairNumeratorKernel k hk (pairPilotCoefficient bar η) =
      pairPilotNumeratorKernel k hk bar η := rfl
  have hden : rawModelPairNoise k hk (pairPilotCoefficient bar η) =
      pairPilotNoiseKernel k hk bar η := rfl
  simp_rw [coefficientPairStatistic, heq, hnum, hden]
  exact h

theorem minimaxRMS_le_of_estimator_rms
    (T : Estimator d n) {B : ℝ≥0∞}
    (hT : ∀ θ : RegressionParameter d, Admissible C θ → meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ B) :
    minimaxRMS C n ≤ B := by
  have h := ENNReal.rpow_le_rpow (minimaxRisk_le_worstCaseRisk C T)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply h.trans
  let φ := ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)
  change φ (⨆ θ : {θ : RegressionParameter d // Admissible C θ}, meanSquaredRisk T θ.val) ≤ B
  rw [φ.map_iSup]
  exact iSup_le (fun θ => hT θ.val θ.property)

end

end NearlyMinimax
