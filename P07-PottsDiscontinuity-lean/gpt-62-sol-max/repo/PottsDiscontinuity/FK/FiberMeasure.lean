module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Conditional estimates summed over a selected family of finite fibers. -/

@[expose] public section

namespace PottsDiscontinuity.FK.FiniteProbability

open MeasureTheory Set

variable {α β : Type*} [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]

private theorem measureReal_inter_fibers (μ : Measure α) [IsFiniteMeasure μ]
    (S : Set α) (f : α → β) (T : Finset β) :
    μ.real (S ∩ f ⁻¹' (↑T : Set β)) = ∑ b ∈ T, μ.real (S ∩ f ⁻¹' {b}) := by
  classical
  have h := sum_measureReal_preimage_singleton (μ := μ.restrict S) (f := f) T
    (fun b _ => (Set.toFinite _).measurableSet)
  simpa only [Measure.real_def, Measure.restrict_apply (Set.toFinite _).measurableSet,
    inter_comm] using h.symm

private theorem real_filter_mul (p : PMF α) (S H : Set α) (hH : ∃ a ∈ H, a ∈ p.support) :
    (p.toMeasure H).toReal * ((p.filter H hH).toMeasure S).toReal =
      (p.toMeasure (S ∩ H)).toReal := by
  classical
  have hmass := p.toMeasure_apply_eq_tsum H
  have hne : p.toMeasure H ≠ 0 := by
    simp_all
  rw [← ENNReal.toReal_mul, (p.filter H hH).toMeasure_apply_eq_tsum, ← ENNReal.tsum_mul_left,
    p.toMeasure_apply_eq_tsum (S ∩ H)]
  congr 1
  apply tsum_congr
  intro a
  by_cases hs : a ∈ S <;> by_cases hh : a ∈ H
  · simp [hs, hh, ← hmass, mul_left_comm (p.toMeasure H), ENNReal.mul_inv_cancel hne (measure_ne_top _ _)]
  all_goals simp [hs, hh]

variable [Fintype β]

/-- A signed comparison on conditional probabilities can be summed over selected fibers. -/
theorem pmf_joint_signed_le (p : PMF α) (f : α → β)
    (hf : ∀ b, ∃ a ∈ {x | f x = b}, a ∈ p.support)
    (S : Set α) (T : Set β) (d c : ℝ)
    (h : ∀ b ∈ T, d * (p.filter {x | f x = b} (hf b)).toMeasure.real S ≤ d * c) :
    d * p.toMeasure.real (S ∩ f ⁻¹' T) ≤ d * c * p.toMeasure.real (f ⁻¹' T) := by
  classical
  let F : Finset β := Finset.univ.filter (· ∈ T)
  have hF : (↑F : Set β) = T := by grind
  rw [← hF, measureReal_inter_fibers, ← sum_measureReal_preimage_singleton F
    (fun b _ => (Set.toFinite _).measurableSet), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  change d * (p.toMeasure (S ∩ {x | f x = b})).toReal ≤
    d * c * (p.toMeasure {x | f x = b}).toReal
  rw [← real_filter_mul p S _ (hf b), mul_comm (p.toMeasure {x | f x = b}).toReal, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h b (Finset.mem_filter.mp hb).2) ENNReal.toReal_nonneg

end PottsDiscontinuity.FK.FiniteProbability
