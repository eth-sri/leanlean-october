/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import PottsDiscontinuity.FK.BoundaryComparison

/-!
# Positive association of the actual finite FK law

The component count is the original wired quotient count, including isolated
vertices. Its proved supermodularity gives the lattice condition for the exact
FK weights. The complete mathlib four-functions/FKG theorem then yields
positive association, without introducing any probabilistic assumption.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
private theorem event_indicator_nonneg {α : Type*} (s : Set α) :
    ∀ a, 0 ≤ s.indicator (fun _ => (1 : ℝ)) a :=
  Set.indicator_nonneg fun _ _ => zero_le_one

theorem event_indicator_monotone {α : Type*} [Preorder α] {s : Set α} (hs : IsUpperSet s) :
    Monotone (s.indicator (fun _ => (1 : ℝ))) := by
  intro a b hab
  by_cases ha : a ∈ s
  · simp [ha, hs hab ha]
  · simpa only [Set.indicator_of_notMem ha] using event_indicator_nonneg s b

/-- FKG for increasing events under a normalized finite lattice weight. -/
theorem fkg_events {α : Type*} [Fintype α] [DistribLattice α] (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hnorm : ∑ a, w a = 1)
    (hlattice : ∀ a b, w a * w b ≤ w (a ⊓ b) * w (a ⊔ b))
    (s t : Set α) (hs : IsUpperSet s) (ht : IsUpperSet t) :
    (∑ a, s.indicator w a) * (∑ a, t.indicator w a) ≤ ∑ a, (s ∩ t).indicator w a := by
  have h := _root_.fkg (μ := w) (f := s.indicator fun _ => (1 : ℝ))
    (g := t.indicator fun _ => (1 : ℝ)) hw (event_indicator_nonneg s) (event_indicator_nonneg t)
    (event_indicator_monotone hs) (event_indicator_monotone ht) hlattice
  simp only [← Set.inter_indicator_mul, one_mul] at h
  simpa only [hnorm, one_mul, ← Set.indicator_mul_right, mul_one] using h

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance positiveAssociationEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveAssociationEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Increasing nonnegative functions are positively correlated under the exact
normalized configuration probabilities of equation (1.2). -/
theorem configurationProbability_positive_association (q : Parameters)
    (ξ : BoundaryCondition V) (f g : Configuration G → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ A, configurationProbability G q ξ A * f A) *
      (∑ A, configurationProbability G q ξ A * g A) ≤
        ∑ A, configurationProbability G q ξ A * (f A * g A) := by
  classical
  have h := _root_.fkg (μ := configurationProbability G q ξ)
    (f := f) (g := g) (fun A => (configurationProbability_pos G q ξ A).le)
    hf0 hg0 hf hg (configurationProbability_cross_lattice_condition q ξ ξ le_rfl)
  simpa only [sum_configurationProbability, one_mul] using h

end
end PottsDiscontinuity.FK
