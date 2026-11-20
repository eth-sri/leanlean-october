module

public import NearlyMinimax.PairDesignMeasure


@[expose] public section

/-! Actual marginal localization of the weighted design-pair measure. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

theorem partitionPairMeasure_fst_le {X I : Type*}
    [MeasurableSpace X] [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [MeasurableEq I]
    {μ : Measure X} [IsProbabilityMeasure μ] {label : X → I} (hlabel : Measurable label)
    {weight cap : ℝ} (hw : 0 ≤ weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) :
    (partitionPairMeasure μ label weight).map Prod.fst ≤ ENNReal.ofReal (weight * cap) • μ := by
  apply Measure.le_iff.2
  intro A hA
  have hC : MeasurableSet {z : X × X | label z.1 = label z.2} :=
    measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd)
  rw [Measure.map_apply measurable_fst hA, partitionPairMeasure,
    Measure.smul_apply, Measure.restrict_apply (measurable_fst hA),
    Measure.prod_apply ((measurable_fst hA).inter hC), Measure.smul_apply,
    ENNReal.ofReal_mul hw]
  change ENNReal.ofReal weight *
    _ ≤
      _
  have hi : (∫⁻ x, μ (Prod.mk x ⁻¹'
      (Prod.fst ⁻¹' A ∩ {z | label z.1 = label z.2})) ∂μ) ≤
      ENNReal.ofReal cap * μ A := by
    calc
      _ ≤ _ := by
        apply lintegral_mono
        intro x
        change μ _ ≤ _
        by_cases hx : x ∈ A
        · have he : Prod.mk x ⁻¹'
              (Prod.fst ⁻¹' A ∩ {z | label z.1 = label z.2}) =
              label ⁻¹' {label x} := by
            ext y
            simp [hx, eq_comm]
          rw [he, Set.indicator_of_mem hx]
          simpa using ENNReal.ofReal_le_ofReal (hmass (label x))
        · have he : Prod.mk x ⁻¹'
              (Prod.fst ⁻¹' A ∩ {z | label z.1 = label z.2}) = ∅ := by
            ext y
            simp [hx]
          rw [he, measure_empty, Set.indicator_of_notMem hx]
      _ = _ := lintegral_indicator_const hA _
  calc
    _ ≤ _ := by gcongr
    _ = _ := (mul_assoc ..).symm

variable {d : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) {k : ℕ}
    (hk : 0 < k)
include hθ

theorem regularPairDesignMeasure_fst_le :
    (regularPairDesignMeasure θ k hk).map Prod.fst ≤ ENNReal.ofReal C.densityUpper • designLaw θ := by
  let := designLaw_isProbability C θ hθ
  have hkp : 0 < (k : ℝ) ^ d := by positivity
  have h := partitionPairMeasure_fst_le
    (regular_grid_cell_measurable k hk) hkp.le
    (div_nonneg (by linarith [C.one_lt_densityUpper]) hkp.le)
    (regularGridProbability_cap hθ hk)
  simpa only [regularPairDesignMeasure, partitionPairMeasure,
    mul_div_cancel₀ _ hkp.ne'] using h

theorem regularPairDesignMeasure_fst_cube_le :
    (regularPairDesignMeasure θ k hk).map Prod.fst ≤
      ENNReal.ofReal (C.densityUpper ^ 2) • cubeVolume d := by
  calc
    _ ≤ _ :=
      regularPairDesignMeasure_fst_le hθ hk
    _ ≤ ENNReal.ofReal C.densityUpper • (ENNReal.ofReal C.densityUpper • cubeVolume d) := by
      gcongr
      exact admissible_designLaw_le_cubeVolume hθ
    _ = _ := by rw [smul_smul, ← ENNReal.ofReal_mul (by linarith [C.one_lt_densityUpper]), ← pow_two]

end NearlyMinimax
