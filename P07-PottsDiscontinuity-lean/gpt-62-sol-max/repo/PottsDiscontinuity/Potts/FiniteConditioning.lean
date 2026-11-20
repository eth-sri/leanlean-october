module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Setoid.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.SetTheory.Cardinal.Finite

/-! Finite conditional probabilities and exterior-event decomposition. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Classical
noncomputable section

variable {E D : Type*} [Fintype E] [Fintype D]
local instance finiteConditioningMeasurable : MeasurableSpace E := ⊤
local instance finiteConditioningDiscrete : DiscreteMeasurableSpace E := ⟨fun _ => trivial⟩

theorem finite_filter_measure (p : PMF E) (B S : Set E)
    (h : ∃ a ∈ B, a ∈ p.support) :
    (p.filter B h).toMeasure S = p.toMeasure (S ∩ B) / p.toMeasure B := by
  classical
  have ht (a : E) : S.indicator (p.filter B h) a =
      (S ∩ B).indicator p a * (∑' b, B.indicator p b)⁻¹ := by
    by_cases hS : a ∈ S <;> by_cases hB : a ∈ B <;>
      simp [Set.indicator, PMF.filter_apply, hS, hB]
  rw [PMF.toMeasure_apply_fintype]
  simp_rw [ht]
  simp [← Finset.sum_mul, div_eq_mul_inv]

theorem finite_filter_measureReal (p : PMF E) (B S : Set E)
    (h : ∃ a ∈ B, a ∈ p.support) :
    (p.filter B h).toMeasure.real S = p.toMeasure.real (S ∩ B) / p.toMeasure.real B := by
  rw [Measure.real, finite_filter_measure, ENNReal.toReal_div]
  rfl

end
end PottsDiscontinuity.Potts
