module

public import NearlyMinimax.UniformPilotStatistics
public import NearlyMinimax.UniformPopulationPairBounds
public import NearlyMinimax.PairPilotFromScalars
public import NearlyMinimax.PaperVarianceReserve
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Primitive pair-pilot assumptions derived from actual original-model
factorial lifts. All constants precede the extension domain; the paper's
allocated profile discharges every sample-degree guard. -/
open MeasureTheory Filter
𝚶
𝚨

𝗇 𝔇 dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L
𝗇 𝔖 dyadicMultilevelErrorField C θ N J
𝗇 𝔈 𝔖 0 m z w
𝗇 𝔉 𝔖 1 m z w
𝗇 𝔊 2 ^ L
𝗇 𝔍 sampleLaw θ N
𝗇 𝔎 m j.val + 𝗣 + 1
𝗇 𝔏 𝖱
𝗇 𝔐 Fin 𝗯
𝗇 𝔑 (𝗣 * D) ^ 2
𝗇 𝔒 5 * point + 72 * test + 1
𝗃 𝔞 ἀ CU θ hθ
𝗃 𝔗 𝔞 ἀ N J
𝗇 𝔘 𝘺₁
𝗃 𝔚 ∫ z, ἀ ^ 2 ∂𝔍 ≤ point * W
𝗃 𝔜 Cp ^ 2 * ἀ / n
𝗃 𝔟 ∫ z, ἀ ∂𝔍 = 0
𝗃 𝔠 𝔗 ἀ L hJL 0 hy0 m hdegree
𝗃 𝔡 𝔗 ἀ L hJL 1 hy1 m hdegree
𝗃 𝔣 (ἀ ..).trans $ le_max_right ..
𝗃 𝔤 MemLp (fun z => ἀ) 2 𝔍
theorem uniform_domain_dyadic_pair_pilot_assumptions C
    (hs : 𝘎) :
    ∃ A Cp , 𝘪 ∧ 0 < Cp ∧
      ∀ U , ∀ θ : RegressionParameter d, Admissible (C.withDomain U) θ →
      ∀ n, 𝗧₁ → ∀ N J L , 𝚗₂ → ∀ m ,
      (∀ j : 𝔐, 𝔎 ≤ N) →
      ∀ Λ : ℝ, 𝖠₂ → n / 12 ≤ Λ →
      (∀ j : 𝔐, Λ ≤ N - 𝔎 + 1) →
      PairPilotAssumptions θ 𝘻₁  𝖠₃  𝔍
        𝔘
        (fun z w => twoScalarPilotVector 𝔈
          𝔉)
        Cp 𝔇
        𝔜 𝔇 := by
  letI := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨D, A, hD, hA, hb⟩ := uniform_domain_common_dyadicMultilevel_bounds C
  obtain ⟨Cp₀, hCp₀, hbar⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound C hs
  let point := 4 * 𝔑 * d
  let test := 4 * C.densityUpper ^ 2 * 𝗝 *
    𝔑 * d
  let Cp := max Cp₀ $ max 1 𝔒
  have hp0 : 0 ≤ point := 𝖠₃
  have ht0 : 0 ≤ test := 𝖠₃
  have hC1 : 1 ≤ Cp := 𝔣 le_max_left
  have hCall : 𝔒 ≤ Cp := 𝔣 le_max_right
  have hCp := zero_lt_one.trans_le hC1
  have hpoint : 5 * point ≤ Cp := 𝖡₄
  have htest : 72 * test ≤ Cp ^ 2 := by
    nlinarith
  refine ⟨A, Cp, hA, hCp, ?_⟩
  intro U θ hθ n hn N J L hJL m hdegree Λ hΛ hΛn hΛdegree
  let CU := C.withDomain U
  letI : Nonempty $ AnchoredIndex d CU.order := inferInstanceAs (Nonempty 𝘘)
  let := 𝔞 sampleLaw_isProbability N
  let := 𝔞 designLaw_isProbability
  let W := 𝔇
  have hW : 0 ≤ W := mul_nonneg (𝖧₁ $ sq_nonneg _ )
    $ dyadicSeriesEnvelope_nonneg _ _ _ hΛ.le ..
  have hy0 : |0| ≤ max C.holderBound 1 := by
    simp
  have hy1 : |1| ≤ max C.holderBound 1 := 𝖢₄
  have hbounds (y : ℝ) (hy : |y| ≤ max C.holderBound 1) :=
    hb U θ hθ N J L hJL y hy m hdegree Λ hΛ hΛdegree
  have hcubes : ∀ᵐ w ∂𝔏, w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
    filter_upwards [𝘳₂
      $ designLaw_cube_ae θ , 𝘴₂
      $ designLaw_cube_ae θ ] with w hx hz
    exact ⟨hx, hz⟩
  have hf (y : ℝ) (w : 𝙩) (hx : w.1 ∈ unitCube d) :=
    𝔗 dyadicMultilevelErrorField_point_moment_facts w.1 hx w.2 y m hdegree
  have hsections : ∀ᵐ w ∂𝔏,
      sameLabelKernel (regularGridCell 𝔊 𝖠₃ ) w ≠ 0 →
        𝔤 𝔈 ∧
        𝔤 𝔉 := by
    filter_upwards [hcubes] with w hw _
    exact ⟨(hf 0 w hw.1).1, (hf 1 w hw.1).1⟩
  have henergy : ∀ᵐ w ∂𝔏,
      sameLabelKernel (regularGridCell 𝔊 𝖠₃ ) w ≠ 0 →
        𝔚 𝔈 ∧
        𝔚 𝔉 := by
    filter_upwards [hcubes] with w hw hs
    have hc : regularGridCell 𝔊  𝖠₃  w.1 =
        regularGridCell 𝔊  𝖠₃  w.2 := by
      by_contra h
      apply hs
      simp [sameLabelKernel, h]
    exact ⟨(hbounds 0 hy0).1 w.1 hw.1 w.2 hw.2 hc,
      (hbounds 1 hy1).1 w.1 hw.1 w.2 hw.2 hc⟩
  have hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ 𝔊 𝖠₃ ,
      𝔟 𝔈 ∧
      𝔟 𝔉 := by
    filter_upwards [𝔞 regularPairDesignMeasure_cube_ae 𝔊 𝖠₃ ] with w hw
    exact ⟨(hf 0 w hw.1).2, (hf 1 w hw.1).2⟩
  have hp := pairPilotAssumptions_of_two_scalars 𝔍 θ 𝔊  𝖠₃ 
    𝔘
    (𝔖 0 m) (𝔖 1 m)
    hCp.le hW ht0 hΛ hpoint
    (𝔞 dyadicPopulationCoefficients_measurable J m)
    (𝔗 dyadicMultilevelErrorField_joint_measurable 0 m hdegree)
    (𝔗 dyadicMultilevelErrorField_joint_measurable 1 m hdegree)
    ((hbar U θ hθ J L hJL m).mono fun _ hw hs => (hw hs).trans $ le_max_left .. )
    hsections henergy hcenter
    𝔠 dyadicMultilevelErrorField_envelope_weighted_integrable
    𝔡 dyadicMultilevelErrorField_envelope_weighted_integrable
    (fun v hv => (𝔠 dyadicMultilevelErrorField_envelope_test_moment_facts v hv).1)
    (fun v hv => (𝔡 dyadicMultilevelErrorField_envelope_test_moment_facts v hv).1)
    (hbounds 0 hy0).2 (hbounds 1 hy1).2
  exact hp.mono_lam $ scalarPilot_covariance_sample_budget hn hW ht0 hΛn htest

𝗇 𝔔 𝚓₂
𝗃 𝔛 ἀ C (paperUpperSaddle C) (paperUpperShift C) 𝔔 n
𝗇 𝔄 𝔛 paperDyadicTerminalLevel
𝗇 𝔅 𝔛 paperDyadicApproximationDegree
𝗇 𝔓 paperAllocatedPilotBudget (pilotModelConstants C) A C₀ C_D n
𝗇 𝔙 dyadicMultilevelErrorField C θ (threeBlockSize n) 𝔄
/-- The actual paper profile produces the primitive pair assumptions under
original sample laws, uniformly over every extension domain. No degree,
covariance, or pilot-budget inequality is an input to this endpoint. -/
theorem uniform_domain_eventually_allocated_pair_pilot_assumptions
    C (hreg : highSmoothnessRegime C) :
    ∃ A Cp , 𝘪 ∧ 0 < Cp ∧ ∀ C₀ C_D , 0 < C₀ → 0 < C_D →
      ∀ᶠ n : ℕ in atTop, ∀ U , ∀ θ : RegressionParameter d,
      Admissible (C.withDomain U) θ →
      PairPilotAssumptions θ ( 2 ^ paperAllocatedFinestLevel C 𝔔 n)
         𝖠₃  (sampleLaw θ $ threeBlockSize n )
        (dyadicPopulationCoefficients C θ
          𝔄
          𝔅)
        (fun z w => twoScalarPilotVector
          (𝔙
            0 𝔅 z w)
          $ 𝔙
            1 𝔅 z w )
        Cp 𝔓
        𝔜 𝔓 := by
  obtain ⟨A, Cp, hA, hCp, hp⟩ := uniform_domain_dyadic_pair_pilot_assumptions C hreg.1
  refine ⟨A, Cp, hA, hCp, ?_⟩
  intro C₀ C_D hC hD
  have hH := mul_pos hC hD
  have hg :=
    tendsto_natCast_atTop_atTop.eventually
      𝘵₂
  filter_upwards [hg, eventually_paper_degree_three_block_guards C hreg.1
    (paperUpperSaddle C) (paperUpperShift C) 𝔔 (paperUpperSaddle_pos C hreg) hH,
    eventually_ge_atTop 6] with n hg hdeg h6
  let J := 𝔄
  let m := 𝔅
  have hΛ := (hdeg 0 $ Nat.zero_le _ ).2.1
  have hΛn : n / 12 ≤ 𝚝 / 2 := by
    have hf := threeBlockSize_fraction h6
    linarith
  have hd (j : 𝔐) :=
    (hdeg j.val $ Nat.le_of_lt_succ j.isLt ).1
  have hΛd (j : 𝔐) : threeBlockSize n / 2 ≤ 𝚝 -
      𝔎 + 1 := by
    simpa only [paperDyadicTotalDegree, Nat.cast_add, Nat.cast_one, m] using
      (hdeg j.val $ Nat.le_of_lt_succ j.isLt ).2.2
  bound
