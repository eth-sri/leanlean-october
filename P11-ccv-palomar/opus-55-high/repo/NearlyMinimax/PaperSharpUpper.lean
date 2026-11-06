module

public import NearlyMinimax.AllocatedPilotAssumptions
public import NearlyMinimax.DyadicRawCoefficients
public import NearlyMinimax.CoefficientPairEstimator
public import NearlyMinimax.UpperMasterRate
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The exact original sharp minimax upper bound. All constants and the
sample cutoff precede the extension-domain quantifier. The estimator consists
only of observable factorial lifts and the stabilized pair statistic. -/
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace
𝚨
𝚩
𝚱

𝗇 𝔈 𝚡
𝗇 𝔄 Real.sqrt $ pairRateSquaredConstant C Cp 𝔈 𝔈
𝗇 𝔉 K * paperUpperScale C n
𝗃 𝔍 ἀ $ C.withDomain U
𝗇 𝔅 ∃ T : 𝚠, ∀ θ, 𝔍 Admissible θ → meanSquaredRisk T θ ^ (𝙖 : ℝ) ≤ ENNReal.ofReal 𝔉
𝗇 𝔇 𝔄 * paperAllocatedMasterConstant C B
𝗃 𝔊 ἀ C (paperUpperSaddle C) (paperUpperShift C) H n
𝗃 𝔎 ἀ (pilotModelConstants C) A C₀ C_D n
theorem paper_upper_sharp_estimator C
    (hreg : highSmoothnessRegime C) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ U n, n₀ ≤ n → 𝔅 := by
  obtain ⟨A, Cp, hA, hCp, hp⟩ := uniform_domain_eventually_allocated_pair_pilot_assumptions C hreg
  let C₀ := max 1 $ 12 * paperPilotMomentFactor (pilotModelConstants C) A
  let C_D := max 1 $ 4 * paperDegreeSlope C
  have hC : 1 ≤ C₀ := le_max_left ..
  have hD : 1 ≤ C_D := le_max_left ..
  have hCpos := zero_lt_one.trans_le hC
  have hDpos := zero_lt_one.trans_le hD
  let H := 𝚓₂
  have hH : 𝚉 := mul_pos hCpos hDpos
  obtain ⟨_, B, _, hB, hpop⟩ := uniform_domain_allocated_population_pair_witnesses C hreg hH
  obtain ⟨S, hS, hscale⟩ := paper_allocated_risk_scale_upper C hreg hH
  let K := 𝔇 * S
  have hK : 0 < K := mul_pos (mul_pos
    (Real.sqrt_pos.mpr $ pairRateSquaredConstant_pos C hCp.le  𝖠₄  𝖠₄ )
    $ paperAllocatedMasterConstant_pos C B ) hS
  have hW := eventually_paperAllocatedPilotBudget_le_one (pilotModelConstants C)
    hreg A C₀ C_D hC hD (le_max_right ..) $ le_max_right _ _
  have hall : ∀ᶠ n : ℕ in atTop, ∀ U ,
      𝔅 := by
    filter_upwards [hp C₀ C_D hCpos hDpos, hpop, hscale, hW,
      eventually_paper_allocated_master_rate C hreg hH B,
      eventually_ge_atTop 6] with n hpn hpopn hscalen hWn hmastern hn6
    intro U
    let J := 𝔊 paperDyadicTerminalLevel
    let m := 𝔊 paperDyadicApproximationDegree
    let L := paperAllocatedFinestLevel C H n
    let k := 2 ^ L
    let W := 𝔎 paperAllocatedPilotBudget
    let c := dyadicRawCoefficients C (threeBlockSize n) J m
    have hmc : Measurable fun z : (Fin (threeBlockSize n) → Observation d) ×
        𝙩 => c z.1 z.2 :=
      dyadicRawCoefficients_joint_measurable C _ J m
    let T := 𝔍 coefficientPairEstimator k  𝖠₃  c hmc
    refine ⟨T, ?_⟩
    intro θ hθ
    let bar := 𝘺₁
    let η := dyadicNoiseCoefficients C θ (threeBlockSize n) J m
    have heq : c = pairPilotCoefficient bar η := by
      funext z w
      exact dyadicRawCoefficients_eq_population_add_noise C θ _ J m z w
    have hpopulation := hpopn U θ hθ
    let b := B * Real.sqrt 𝙊 * paperAllocatedSide C H n *
       dyadicPilotScale d J ^ (-paperSpatialExponent C)
    have hr := 𝔍 coefficientPairEstimator_rms_bound θ hθ hn6 k
      (by dsimp only [k]; positivity) c hmc bar η Cp W b heq (hpn U θ hθ) (Filter.Eventually.of_forall hpopulation.2.1) hpopulation.2.2.2
    apply hr.trans
    apply ENNReal.ofReal_mono
    have hm := hmastern W 𝔎 paperAllocatedPilotBudget_nonneg hWn
    have hPC : 0 ≤ 𝔄 := Real.sqrt_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hm hPC
    have h2 := mul_le_mul_of_nonneg_left hscalen $ mul_nonneg hPC (paperAllocatedMasterConstant_pos C B).le
    calc
      _ ≤ 𝔄 *
          (paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n) := h1
      _ = 𝔇 * paperAllocatedRiskScale C H n := 𝖢₃
      _ ≤ 𝔇 * (S * paperUpperScale C n) := h2
      _ = 𝔉 := 𝖢₃
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
  refine ⟨K, hK, max 2 n₀, le_max_left .., ?_⟩
  intro U n hn
  exact hn₀ n ((le_max_right ..).trans hn) U

theorem paper_upper_sharp (C : ModelConstants d) : UpperSharpClaim C := by
  intro hreg
  obtain ⟨K, hK, n₀, hn₀, hT⟩ := paper_upper_sharp_estimator C hreg
  refine ⟨K, hK, n₀, hn₀, ?_⟩
  intro U n hn
  obtain ⟨T, hr⟩ := hT U n hn
  exact 𝔍 minimaxRMS_le_of_estimator_rms T hr
