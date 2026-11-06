/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoundaryComparison
public import PottsDiscontinuity.FK.PositiveAssociation
public import PottsDiscontinuity.FK.Expectation

/-!
# FKG and wiring comparison for actual increasing events

The finite sums are identified with the real-valued probabilities of the
existing full power-set FK measure. In particular the correlation inequality
and wiring comparison below are statements about that measure itself.
-/

public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance increasingEventsEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

theorem measure_toReal_eq_indicator_sum (q : Parameters) (ξ : BoundaryCondition V)
    (s : Set (Configuration G)) :
    (measure G q ξ s).toReal =
      ∑ A, configurationProbability G q ξ A * s.indicator (fun _ => (1 : ℝ)) A := by
  rw [measure_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro A hA
    by_cases h : A ∈ s
    · simp [Set.indicator, h, law_apply,
        ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]
    simp_all
  · intro A hA
    by_cases h : A ∈ s
    · simpa [Set.indicator, h] using (law G q ξ).apply_ne_top A
    simp_all

theorem fkLaw_measure_toReal_eq_expectation (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      FiniteProbability.expectation (law G q ξ) (S.indicator (fun _ => (1 : ℝ))) := by
  rw [measure_toReal_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S
  · simp [Set.indicator, h, law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]
  simp_all

omit [Finite V] in
theorem event_indicator_nonneg (s : Set (Configuration G)) :
    ∀ A, 0 ≤ s.indicator (fun _ => (1 : ℝ)) A := by
  grind [Set.indicator]

omit [Finite V] in
theorem event_indicator_monotone (s : Set (Configuration G)) (hs : IsUpperSet s) :
    Monotone (s.indicator (fun _ => (1 : ℝ))) := by
  intro A B hAB
  by_cases hA : A ∈ s
  · have hB := hs hAB hA
    simp_all
  · simp_all [event_indicator_nonneg]

section
variable (q : Parameters)
/-- Any two increasing events are positively correlated under the actual FK measure. -/
theorem measure_positive_association (ξ : BoundaryCondition V)
    (s t : Set (Configuration G)) (hs : IsUpperSet s) (ht : IsUpperSet t) :
    (measure G q ξ s).toReal * (measure G q ξ t).toReal ≤
      (measure G q ξ (s ∩ t)).toReal := by
  have h := configurationProbability_positive_association q ξ
    (s.indicator fun _ => (1 : ℝ)) (t.indicator fun _ => (1 : ℝ))
    (event_indicator_nonneg s) (event_indicator_nonneg t)
    (event_indicator_monotone s hs) (event_indicator_monotone t ht)
  have hi (A : Configuration G) :
      s.indicator (fun _ => (1 : ℝ)) A * t.indicator (fun _ => (1 : ℝ)) A =
        (s ∩ t).indicator (fun _ => (1 : ℝ)) A := by
    grind [Set.indicator]
  simp_all
  simpa only [measure_toReal_eq_indicator_sum] using h

/-- Increasing event probabilities increase when boundary identifications are added. -/
theorem measure_boundary_comparison (ξ η : BoundaryCondition V)
    (hξη : ξ.partition ≤ η.partition) (s : Set (Configuration G)) (hs : IsUpperSet s) :
    (measure G q ξ s).toReal ≤ (measure G q η s).toReal := by
  have h := configurationProbability_boundary_comparison q ξ η hξη
    (s.indicator fun _ => (1 : ℝ)) (event_indicator_nonneg s) (event_indicator_monotone s hs)
  grind [measure_toReal_eq_indicator_sum]
end

end
end PottsDiscontinuity.FK
