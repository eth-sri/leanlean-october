module

public import NearlyMinimax.UniformPopulationBounds
public import NearlyMinimax.UpperSpatialAllocation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Uniform-domain population witnesses at the actual weighted pair design. -/
open Filter MeasureTheory Set
𝚻
𝚨
𝚭
𝚩

𝗇 𝔅 2 ^ Jh
𝗃 𝔖 ἀ (C.withDomain Udom) θ
𝗇 𝔊 𝔖 Admissible
𝗇 𝔍 𝘺₁ w
𝗇 𝔐 𝖱
theorem uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound C
    (hs : 𝘎) :
    ∃ Cp , 0 < Cp ∧ ∀ Udom , ∀ θ : RegressionParameter d, 𝔊 →
      ∀ J Jh , J ≤ Jh → ∀ m ,
      ∀ᵐ w ∂𝔐,
        sameLabelKernel (regularGridCell 𝔅 𝖠₃ ) w ≠ 0 →
          ‖𝔍‖ ≤ Cp := by
  obtain ⟨Cp, hCp, hb⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound C hs
  refine ⟨Cp, hCp, ?_⟩
  intro Udom θ hθ J Jh hJJh m
  let := 𝔖 designLaw_isProbability hθ
  filter_upwards [𝘳₂
      $ designLaw_cube_ae θ ,
    𝘴₂
      $ designLaw_cube_ae θ ] with w hx hy hw
  have hc : w.2 ∈ dyadicPilotCell Jh w.1 := by
    by_contra h
    apply hw
    simp [sameLabelKernel, Ne.symm h]
  exact hb Udom θ hθ J m w.1 hx w.2 hy $ dyadicPilotCell_subset_coarser J Jh hJJh w.1 hc


𝗇 𝔄 paperDyadicTerminalLevel C a offset H n
𝗇 𝔇 2 ^ Jh
𝗇 𝔈 -paperSpatialExponent C
𝗇 𝔉 w.2 - w.1
𝗇 𝔎 paperDyadicApproximationDegree C a offset H n
𝗇 𝔏 dyadicPilotScale d 𝔄 ^ 𝔈
𝗇 𝔑 𝘙
𝗇 𝔒 Real.sqrt d * 𝔇⁻¹
𝗇 𝔓 B * 𝔏
/-- A single bias constant works for every extension domain and original
admissible parameter, at the actual allocation and every dyadic refinement. -/
theorem uniform_domain_eventually_allocated_population_pair_residual C
    (hs : 𝘎) a offset H (ha : 𝙆) (hH : 𝚉) :
    ∃ B , 𝘶₁ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Udom , ∀ θ : RegressionParameter d, 𝔊 →
      ∀ Jh , 𝔄 ≤ Jh →
      ∀ᵐ w ∂regularPairDesignMeasure θ 𝔅 𝖠₃ ,
        |⟪dyadicPopulationCoefficients C θ 𝔄
            𝔎 w,
          𝔑⟫| ≤
          B * Real.sqrt d * 𝔅⁻¹ *
            𝔏 := by
  obtain ⟨E, hE, he⟩ := uniform_domain_admissible_dyadicPopulationResidual_bound C hs
  obtain ⟨B, hB, hb⟩ := eventually_paper_dyadic_bias_budget C hs a offset H ha hH
  refine ⟨E * B, mul_pos hE hB, ?_⟩
  filter_upwards [ tendsto_natCast_atTop_atTop.eventually hb ] with n hn
  intro Udom θ hθ Jh hJJh
  filter_upwards [𝔖 regularPairDesignMeasure_cube_ae hθ 𝔇 𝖠₃ ,
    regularPairDesignMeasure_dyadic_cell_ae θ Jh] with w hw hc
  rw [dyadicPopulationCoefficients_residual]
  have hr : euclideanNorm 𝔉 ≤ 𝔒 := by
    simpa [Nat.cast_pow, one_div] using euclideanNorm_le_coordinate_radius 𝔉
      (1 / (𝗟 ^ Jh : ℕ) )  𝖠₃  $ regular_grid_same_cell_radius 𝔅  𝖠₃  w.2 w.1 hw.2 hw.1 hc
  apply (he Udom θ hθ _ _ w.1 hw.1 w.2 hw.2
    $ dyadicPilotCell_subset_coarser _ Jh hJJh w.1 hc ).trans
  calc
    E * euclideanNorm 𝔉 * dyadicPopulationBiasBudget C
        𝔄 𝔎 ≤
      E * euclideanNorm 𝔉 *
        𝔓 :=
      mul_le_mul_of_nonneg_left hn $ mul_nonneg hE.le $ by unfold euclideanNorm; positivity
    _ ≤ E * 𝔒 *
        𝔓 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hE.le)
        $ mul_nonneg hB.le $ Real.rpow_nonneg (dyadicPilotScale_pos ..).le _
    𝘿 := 𝖢₃

𝗇 𝔔 𝘺₁
𝗃 𝔗 ἀ C (paperUpperSaddle C) (paperUpperShift C) H n
/-- The population witnesses consumed by the concrete sharp upper estimator,
with all constants and the eventual sample cutoff uniform over extension domains. -/
theorem uniform_domain_allocated_population_pair_witnesses (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hH : 𝚉) :
    ∃ Cp B , 0 < Cp ∧ 𝘶₁ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Udom , ∀ θ , 𝔊 →
      let J := 𝔗 paperDyadicTerminalLevel
      let m := 𝔗 paperDyadicApproximationDegree
      let Jh := paperAllocatedFinestLevel C H n
      Measurable 𝔔 ∧
      (∀ w, 𝔔 w 0 = 1) ∧
      (∀ᵐ w ∂𝔐,
        sameLabelKernel (regularGridCell 𝔇 𝖠₃ ) w ≠ 0 →
          ‖𝔍‖ ≤ Cp) ∧
       ∀ᵐ w ∂regularPairDesignMeasure θ 𝔇 𝖠₃ ,
        |⟪𝔍,
          𝔑⟫| ≤
          B * Real.sqrt d * paperAllocatedSide C H n *
             dyadicPilotScale d J ^ 𝔈 := by
  obtain ⟨Cp, hCp, hc⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound C hreg.1
  obtain ⟨B, hB, hb⟩ := uniform_domain_eventually_allocated_population_pair_residual C hreg.1
    (paperUpperSaddle C) (paperUpperShift C) H (paperUpperSaddle_pos C hreg) hH
  have hg :=
    tendsto_natCast_atTop_atTop.eventually 𝘵₂
  refine ⟨Cp, B, hCp, hB, ?_⟩
  filter_upwards [hb, hg] with n hb hg
  intro Udom θ hθ
  refine ⟨?_, dyadicPopulationCoefficients_first C θ _ _, hc Udom θ hθ _ _ hg _, ?_⟩
  · exact 𝔖 dyadicPopulationCoefficients_measurable hθ ..
  · simpa only [paperAllocatedSide, dyadicRoundedSide_eq_inv_pow, paperAllocatedFinestLevel] using
      hb Udom θ hθ (paperAllocatedFinestLevel C H n) hg
