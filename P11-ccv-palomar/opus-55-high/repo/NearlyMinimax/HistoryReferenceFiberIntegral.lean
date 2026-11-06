module

public import NearlyMinimax.HistoryReferenceMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Integrating genuine conditional fiber bounds over the countable history reference
-/

open MeasureTheory Filter
𝚨

𝚲

𝗇 𝔄 ∫ h, F h ∂𝙤
𝗇 𝔅 integral_map (historyMarked_measurable_mk dependent g).aemeasurable
/-- A uniform conditional fiber bound passes to the actual normalized countable reference law. -/
theorem historyMarkedReference_integral_le_of_fiber_bound (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝘼)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝘽)
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    F (hF : Measurable F)
    (R C : ℝ) (hbound : ∀ h, |F h| ≤ R)
    (hconditional : ∀ g, ∫ marks, F 𝗬
      ∂𝘰 ≤ C) :
    𝔄 ≤ C := by
  let μ := 𝚊₂
  let := historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  let :=
    historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable R
    $ Eventually.of_forall fun h => by simpa only [Real.norm_eq_abs] using hbound h
  have hc : Integrable (fun _ => C) μ := integrable_const C
  have hr : ∫ h, F h ∂μ ≤ ∫ _ : 𝙗, C ∂μ := by
    change ∫ h, F h ∂Measure.sum _ ≤ ∫ _ : 𝙗, C ∂Measure.sum _
    rw [integral_sum_measure hi, integral_sum_measure hc]
    apply Summable.tsum_le_tsum (fun g => ?_)
      (hasSum_integral_measure hi).summable (hasSum_integral_measure hc).summable
    rw [integral_smul_measure, integral_smul_measure,
      𝔅 hF.aestronglyMeasurable,
      𝔅 measurable_const.aestronglyMeasurable]
    simpa using mul_le_mul_of_nonneg_left (hconditional g) ENNReal.toReal_nonneg
  have he : 𝔄 ≤
      ∫ _ : 𝙗, C ∂𝙤 := by
    unfold historyMarkedReference
    rw [integral_smul_measure, integral_smul_measure]
    exact mul_le_mul_of_nonneg_left hr ENNReal.toReal_nonneg
  simpa using he
