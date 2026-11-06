module

public import NearlyMinimax.TernaryMeasure
public import NearlyMinimax.Risk


@[expose] public section

/-! Exact restriction of the original minimax problem to bounded estimators.
This keeps extended-valued losses for arbitrary estimators and proves that
clipping to the effective variance interval preserves the minimax value.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax

def effectiveVarianceUpper  (C : ModelConstants d) : ℝ :=
  min C.varianceUpper (Real.sqrt C.fourthBound)

def clippedEstimator  (C : ModelConstants d) (T : Estimator d n) :
    Estimator d n :=
  ⟨fun z => clip C.varianceLower (effectiveVarianceUpper C) (T.val z),
    (clip_lipschitz _ _).continuous.measurable.comp T.property⟩

/-- The bounded estimator class still quantifies all measurable statistics
with values in the effective variance interval. -/
abbrev BoundedEstimator {d : ℕ} (C : ModelConstants d) (n : ℕ) :=
  {T : Estimator d n // ∀ z, T.val z ∈ Icc C.varianceLower (effectiveVarianceUpper C)}

theorem minimaxRisk_eq_inf_bounded  (C : ModelConstants d) (n ) :
    minimaxRisk C n = ⨅ T : BoundedEstimator C n, worstCaseRisk C T.val := by
  apply le_antisymm
  · apply le_iInf
    intro T
    exact minimaxRisk_le_worstCaseRisk C T.val
  · apply le_iInf
    intro T
    have h_clippedEstimator_mem_Icc (z : Fin n → Observation d) : (clippedEstimator C T).val z ∈ Icc C.varianceLower (effectiveVarianceUpper C) := clip_mem_Icc (effective_variance_interval_nondegenerate C).le
    have h_clippedEstimator_worstCaseRisk_le : worstCaseRisk C (clippedEstimator C T) ≤ worstCaseRisk C T := by
      apply iSup_le
      intro θ
      have h_clippedEstimator_risk_le : meanSquaredRisk (clippedEstimator C T) θ.val ≤ meanSquaredRisk T θ.val := by
        have hV := admissible_variance_effective_interval C θ.val θ.property
        apply lintegral_mono
        intro z
        apply ENNReal.ofReal_le_ofReal
        have h := clip_error_le hV.1 hV.2 (x := T.val z)
        change |clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.val.variance| ≤
          |T.val z - θ.val.variance| at h
        change (clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.val.variance) ^ 2 ≤ _
        nlinarith [sq_abs (clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.val.variance),
          sq_abs (T.val z - θ.val.variance), abs_nonneg (T.val z - θ.val.variance),
          abs_nonneg (clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.val.variance)]
      exact h_clippedEstimator_risk_le.trans
        (le_iSup (fun θ => meanSquaredRisk T θ.val) θ)
    exact (iInf_le (fun B : BoundedEstimator C n => worstCaseRisk C B.val)
      ⟨clippedEstimator C T, h_clippedEstimator_mem_Icc⟩).trans
      h_clippedEstimator_worstCaseRisk_le

theorem boundedEstimator_risk_le_diameter  (C : ModelConstants d)
    (T : BoundedEstimator C n) (θ : RegressionParameter d) (hθ : Admissible C θ) :
    meanSquaredRisk T.val θ ≤
      ENNReal.ofReal ((effectiveVarianceUpper C - C.varianceLower) ^ 2) := by
  let _ := sampleLaw_isProbability C θ hθ n
  have hV := admissible_variance_effective_interval C θ hθ
  change θ.variance ∈ Icc C.varianceLower (effectiveVarianceUpper C) at hV
  have hp : ∀ z, (T.val.val z - θ.variance) ^ 2 ≤
      (effectiveVarianceUpper C - C.varianceLower) ^ 2 := by
    intro z
    have hT := T.property z
    have : |T.val.val z - θ.variance| ≤ effectiveVarianceUpper C - C.varianceLower := by
      apply abs_le.mpr
      constructor <;> linarith [hV.1, hV.2, hT.1, hT.2]
    nlinarith [sq_abs (T.val.val z - θ.variance), abs_nonneg (T.val.val z - θ.variance)]
  calc
    meanSquaredRisk T.val θ ≤ ∫⁻ _ : Fin n → Observation d,
        ENNReal.ofReal ((effectiveVarianceUpper C - C.varianceLower) ^ 2) ∂sampleLaw θ n :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hp z))
    _ = _ := by simp

end NearlyMinimax
