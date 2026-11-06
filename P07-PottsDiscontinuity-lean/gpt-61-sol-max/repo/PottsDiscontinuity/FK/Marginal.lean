/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.WiredRemoval
public import PottsDiscontinuity.FK.ProbabilityProduct

/-!
# The exact marginal after removing prewired edges

This proves the sampling equivalence on page 5 of the paper. Removed edges have
endpoints already identified by the boundary partition. The law of every other
edge is exactly the normalized FK weight with those edges omitted from sampling.
All original vertices and the original boundary partition are retained.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance marginalEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
local instance remainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance removedFintype (R : Configuration G) :
    Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

/-- The normalized FK law when only the edges outside `R` are sampled. -/
def remainingLaw (q : Parameters) (ξ : BoundaryCondition V) (R : Configuration G)  :=
  FiniteProbability.pmf (remainingWeight G q ξ R) (remainingWeight_pos G q ξ R)

/-- The Bernoulli weight on the removed edge carrier, normalized as a PMF. -/
def removedLaw (q : Parameters) (R : Configuration G)  :=
  FiniteProbability.pmf (removedWeight G q R) (removedWeight_pos G q R)

/-- The partition function with the preselected edges removed from sampling. -/
def remainingPartitionFunction (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G)  :=
  FiniteProbability.partition (remainingWeight G q ξ R)

theorem remainingPartitionFunction_pos (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) : 0 < remainingPartitionFunction G q ξ R :=
  FiniteProbability.partition_pos _ (remainingWeight_pos G q ξ R)

variable [DecidableEq G.edgeSet]

section

variable (q : Parameters) (ξ : BoundaryCondition V) (R : Configuration G) (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v)
include q hR

/-- The complete joint law splits into the remaining FK law and the independent
Bernoulli law on edges whose endpoints are already boundary-identified. -/
theorem law_map_split  :
    (law G q ξ).map (configurationSplitEquiv G R) =
      FiniteProbability.productPMF (remainingLaw G q ξ R) (removedLaw G q R) := by
  rw [remainingLaw, removedLaw, ← FiniteProbability.pmf_product]
  apply FiniteProbability.pmf_map_equiv_of_weight_eq
  intro C
  let P := configurationSplitEquiv G R C
  
  exact (congrArg (weight G q ξ) ((configurationSplitEquiv G R).symm_apply_apply C)).symm.trans
    (weight_union_factorization G q ξ R hR P.1 P.2)

/-- Forgetting all prewired edges gives exactly the FK law on the remaining edges. -/
theorem law_map_remove  :
    (law G q ξ).map (fun C => (configurationSplitEquiv G R C).1) =
      remainingLaw G q ξ R := by
  change (law G q ξ).map (Prod.fst ∘ configurationSplitEquiv G R) = _
  rw [← PMF.map_comp, law_map_split G q ξ R hR, FiniteProbability.productPMF_map_fst]

end

end

end PottsDiscontinuity.FK
