module

public import NearlyMinimax.AllocatedPilotAssumptions
public import NearlyMinimax.DyadicRawCoefficients
public import NearlyMinimax.CoefficientPairEstimator
public import NearlyMinimax.UpperMasterRate


@[expose] public section

/-! The exact original sharp minimax upper bound. All constants and the
sample cutoff precede the extension-domain quantifier. The estimator consists
only of observable factorial lifts and the stabilized pair statistic. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ}

theorem paper_upper_sharp_estimator {C : ModelConstants d}
    (hreg : highSmoothnessRegime C) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ U n, n₀ ≤ n → ∃ T : Estimator d n,
        ∀ θ, Admissible (C.withDomain U) θ →
          meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (K * paperUpperScale C n) := by
  obtain ⟨A, Cp, hA, hCp, hp⟩ := uniform_domain_eventually_allocated_pair_pilot_assumptions hreg
  let C₀ := max 1 (12 * paperPilotMomentFactor (pilotModelConstants C) A)
  let C_D := max 1 (4 * paperDegreeSlope C)
  have hC : 1 ≤ C₀ := le_max_left _ _
  have hD : 1 ≤ C_D := le_max_left _ _
  have hCpos  := zero_lt_one.trans_le hC
  have hDpos  := zero_lt_one.trans_le hD
  let H := C₀ * C_D
  have hH  := mul_pos hCpos hDpos
  obtain ⟨_, B, _, hB, hpop⟩ := uniform_domain_allocated_population_pair_witnesses hreg hH
  obtain ⟨S, hS, hscale⟩ := paper_allocated_risk_scale_upper hreg hH
  let root := Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4))
  let K := root *
    paperAllocatedMasterConstant C B * S
  have hK : 0 < K := mul_pos (mul_pos
    (Real.sqrt_pos.mpr (pairRateSquaredConstant_pos C hCp.le (by norm_num) (by norm_num)))
    (by unfold paperAllocatedMasterConstant; positivity)) hS
  have hW := eventually_paperAllocatedPilotBudget_le_one (C := (pilotModelConstants C))
    hreg hC hD (le_max_right _ _) (le_max_right _ _)
  have hall : ∀ᶠ n in atTop, ∀ U,
      ∃ T : Estimator d n, ∀ θ, Admissible (C.withDomain U) θ →
        meanSquaredRisk T θ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (K * paperUpperScale C n) := by
    filter_upwards [hp C₀ C_D hCpos hDpos, hpop, hscale, hW,
      eventually_paper_allocated_master_rate hreg hH B,
      eventually_ge_atTop 6] with n hpn hpopn hscalen hWn hmastern hn6
    intro U
    let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n
    let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) H n
    let k := 2 ^ (paperAllocatedFinestLevel C H n)
    let W := paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n
    let c := dyadicRawCoefficients C (threeBlockSize n) J m
    have hmc : Measurable (fun z : (Fin (threeBlockSize n) → Observation d) ×
        (Covariate d × Covariate d) => c z.1 z.2) :=
      dyadicRawCoefficients_joint_measurable ..
    refine ⟨(coefficientPairEstimator (C.withDomain U) k (by positivity) hmc), ?_⟩
    intro θ hθ
    let bar := dyadicPopulationCoefficients C θ J m
    have heq : c = pairPilotCoefficient bar (dyadicNoiseCoefficients C θ (threeBlockSize n) J m) := by
      funext z w
      apply dyadicRawCoefficients_eq_population_add_noise
    have hpr  := hpn U θ hθ
    have hpopulation := hpopn U θ hθ
    have hr := coefficientPairEstimator_rms_bound hθ hn6
      (by positivity) hmc heq hpr (Filter.Eventually.of_forall hpopulation.2.1) hpopulation.2.2.2
    apply hr.trans
    apply ENNReal.ofReal_mono
    have hw0  := paperAllocatedPilotBudget_nonneg (pilotModelConstants C) A C₀ C_D n
    have hPC : 0 ≤ root := Real.sqrt_nonneg _
    have hMC  := ((by unfold paperAllocatedMasterConstant; positivity : 0 < paperAllocatedMasterConstant C B)).le
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmastern W hw0 hWn) hPC
      _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscalen (mul_nonneg hPC hMC)
      _ = _ := by ring
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
  refine ⟨K, hK, max 2 n₀, le_max_left _ _, ?_⟩
  intro U n hn
  exact hn₀ n ((le_max_right _ _).trans hn) U

theorem paper_upper_sharp (C : ModelConstants d) : UpperSharpClaim C := by
  intro hreg
  obtain ⟨K, hK, n₀, hn₀, hT⟩ := paper_upper_sharp_estimator hreg
  refine ⟨K, hK, n₀, hn₀, ?_⟩
  intro U n hn
  obtain ⟨T, hr⟩ := hT U n hn
  exact minimaxRMS_le_of_estimator_rms hr

end NearlyMinimax
