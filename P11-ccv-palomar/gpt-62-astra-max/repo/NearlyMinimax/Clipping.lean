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

variable {d n : ℕ} (C : ModelConstants d)

def effectiveVarianceUpper : ℝ :=
  min C.varianceUpper (Real.sqrt C.fourthBound)

def clippedEstimator (T : Estimator d n) :
    Estimator d n :=
  ⟨fun z => clip C.varianceLower (effectiveVarianceUpper C) (T.val z),
    (clip_lipschitz _ _).continuous.measurable.comp T.property⟩

theorem clippedEstimator_mem_Icc
    (T : Estimator d n) (z : Fin n → Observation d) :
    (clippedEstimator C T).val z ∈ Icc C.varianceLower (effectiveVarianceUpper C) :=
  clip_mem_Icc (effective_variance_interval_nondegenerate C).le

theorem clippedEstimator_risk_le {C : ModelConstants d}
    (T : Estimator d n) {θ : RegressionParameter d} (hθ : Admissible C θ) :
    meanSquaredRisk (clippedEstimator C T) θ ≤ meanSquaredRisk T θ := by
  have hV := admissible_variance_effective_interval hθ
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  have h := clip_error_le hV.1 hV.2 (x := T.val z)
  change |clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.variance| ≤
    _ at h
  change (clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.variance) ^ 2 ≤ _
  nlinarith [sq_abs (clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.variance),
    sq_abs (T.val z - θ.variance), abs_nonneg (T.val z - θ.variance),
    abs_nonneg (clip C.varianceLower (effectiveVarianceUpper C) (T.val z) - θ.variance)]

/-- The bounded estimator class still quantifies all measurable statistics
with values in the effective variance interval. -/
abbrev BoundedEstimator (n : ℕ) :=
  {T : Estimator d n // ∀ z, T.val z ∈ Icc C.varianceLower (effectiveVarianceUpper C)}

theorem minimaxRisk_eq_inf_bounded (n : ℕ) :
    minimaxRisk C n = ⨅ T : BoundedEstimator C n, worstCaseRisk C T.val := by
  apply le_antisymm
  · apply le_iInf
    intro T
    exact minimaxRisk_le_worstCaseRisk C T.val
  · apply le_iInf
    intro T
    exact (iInf_le (fun B : BoundedEstimator C n => worstCaseRisk C B.val)
      ⟨clippedEstimator C T, clippedEstimator_mem_Icc C T⟩).trans
      (by apply iSup_le; intro θ; exact (clippedEstimator_risk_le T θ.property).trans (le_iSup (fun θ : {θ // Admissible C θ} => meanSquaredRisk T θ.val) θ))

theorem boundedEstimator_memLp
    (T : BoundedEstimator C n) (μ : Measure (Fin n → Observation d))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) : MemLp T.val.val p μ := by
  apply MemLp.of_bound T.val.property.aestronglyMeasurable (effectiveVarianceUpper C)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
  exact (T.property z).2

theorem boundedEstimator_risk_le_diameter {C : ModelConstants d}
    (T : BoundedEstimator C n) {θ : RegressionParameter d} (hθ : Admissible C θ) :
    meanSquaredRisk T.val θ ≤
      ENNReal.ofReal ((effectiveVarianceUpper C - C.varianceLower) ^ 2) := by
  let _ := sampleLaw_isProbability C θ hθ n
  have hV := admissible_variance_effective_interval hθ
  change θ.variance ∈ Icc C.varianceLower (effectiveVarianceUpper C) at hV
  have hp : ∀ z, (T.val.val z - θ.variance) ^ 2 ≤
      (effectiveVarianceUpper C - C.varianceLower) ^ 2 := by
    intro z
    have habs : |T.val.val z - θ.variance| ≤ effectiveVarianceUpper C - C.varianceLower := by
      grind
    nlinarith [sq_abs (T.val.val z - θ.variance), abs_nonneg (T.val.val z - θ.variance)]
  calc
    _ ≤ _ :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hp z))
    _ = _ := by simp

end NearlyMinimax
