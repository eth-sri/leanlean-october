module

public import NearlyMinimax.PairDesignMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual marginal localization of the weighted design-pair measure. -/
𝚫
𝚮
𝚨
𝚩

𝗇 𝔄 𝚌₁
𝗇 𝔅 Prod.fst ⁻¹' A
𝗇 𝔇 X × X
𝗇 𝔉 ENNReal.ofReal cap * μ A
theorem partitionPairMeasure_fst_le
    [MeasurableSpace X] [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [MeasurableEq I]
    (μ : Measure X) [IsProbabilityMeasure μ] (label : X → I) (hlabel : Measurable label)
    (hw : 0 ≤ weight) (hcap : 0 ≤ cap)
    (hmass : 𝗧) :
    (partitionPairMeasure μ label weight).map Prod.fst ≤ ENNReal.ofReal (weight * cap) • μ := by
  apply Measure.le_iff.2
  intro A hA
  have hC : MeasurableSet {z : 𝔇 | 𝔄} :=
    𝗝₁
  rw [Measure.map_apply measurable_fst hA, partitionPairMeasure,
    Measure.smul_apply, Measure.restrict_apply $ measurable_fst hA ,
    Measure.prod_apply $ (measurable_fst hA).inter hC , Measure.smul_apply,
    ENNReal.ofReal_mul hw]
  change ENNReal.ofReal weight *
     ∫⁻ x, μ (Prod.mk x ⁻¹' (𝔅 ∩ {z : 𝔇 | 𝔄})) ∂μ ≤
       ENNReal.ofReal weight * ENNReal.ofReal cap * μ A
  have hi : ∫⁻ x, μ (Prod.mk x ⁻¹'
      (𝔅 ∩ {z : 𝔇 | 𝔄})) ∂μ ≤
      𝔉 := by
    calc
      _ ≤ ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal cap) x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ A
        · have he : Prod.mk x ⁻¹'
              (𝔅 ∩ {z : 𝔇 | 𝔄}) =
              𝗃₂ := by
            grind
          have hb := ENNReal.ofReal_le_ofReal $ hmass $ label x
          simp_all
        · have he : Prod.mk x ⁻¹'
              (𝔅 ∩ {z : 𝔇 | 𝔄}) = ∅ := by
            grind
          simp_all
      𝘿 := lintegral_indicator_const hA _
  calc
    _ ≤ ENNReal.ofReal weight * 𝔉 := 𝖩₃
    𝘿 := (mul_assoc ..).symm

𝗇 𝔈 (𝗪₁).map Prod.fst
theorem regularPairDesignMeasure_fst_le C
    (θ : RegressionParameter d) (hθ : 𝙟) k hk :
    𝔈 ≤ ENNReal.ofReal C.densityUpper • designLaw θ := by
  let := 𝘪₁
  have hkp : 0 < 𝙦 ^ d := pow_pos (by exact_mod_cast hk) d
  have h := partitionPairMeasure_fst_le (designLaw θ) 𝘯
    (regular_grid_cell_measurable k hk) hkp.le
    (div_nonneg (by linarith [C.one_lt_densityUpper]) hkp.le)
    $ regularGridProbability_cap C θ hθ k hk
  simpa only [regularPairDesignMeasure, partitionPairMeasure,
    mul_div_cancel₀ _ hkp.ne'] using h

theorem regularPairDesignMeasure_fst_cube_le C
    θ (hθ : 𝙟) k hk :
    𝔈 ≤
      ENNReal.ofReal (C.densityUpper ^ 2) • cubeVolume d := by
  calc
    _ ≤ ENNReal.ofReal C.densityUpper • designLaw θ :=
      regularPairDesignMeasure_fst_le C θ hθ k hk
    _ ≤ ENNReal.ofReal C.densityUpper • ENNReal.ofReal C.densityUpper • cubeVolume d := by
      gcongr
      exact admissible_designLaw_le_cubeVolume C θ hθ
    𝘿 := by rw [smul_smul, ← ENNReal.ofReal_mul $ by linarith [C.one_lt_densityUpper] , ← pow_two]
