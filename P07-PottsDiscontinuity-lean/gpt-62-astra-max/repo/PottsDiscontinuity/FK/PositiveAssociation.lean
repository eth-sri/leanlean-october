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
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance positiveAssociationEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveAssociationEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Increasing nonnegative functions are positively correlated under the exact
normalized configuration probabilities of equation (1.2). -/
theorem configurationProbability_positive_association (q : Parameters)
    (ξ : BoundaryCondition V) {f g : Configuration G → ℝ}
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
