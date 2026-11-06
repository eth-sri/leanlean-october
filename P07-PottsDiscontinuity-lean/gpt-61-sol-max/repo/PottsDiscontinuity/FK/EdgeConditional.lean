/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Generalized to independent interior edge probability and cluster weight at least one. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.PositiveAssociation

/-!
# The exact law of an edge within a wired component

Fix all edges except one original graph edge, whose endpoints are already in
the same wired component. The two remaining configurations have FK weight
odds `p / (1 - p)`. Their normalized probabilities therefore give open
conditional probability `p`. Boundary identification alone suffices for this
calculation, as required by the wired-edge convention on page 5 of the paper.

The conditional formula below is the ratio of actual singleton probabilities
on the two-element event `{A, insert e A}`. Its denominator is strictly positive.
It is not a claim that an arbitrary edge has open conditional probability `p`.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V} [DecidableEq G.edgeSet]

section

variable (q : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v) (he : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A) (hrelated : (componentSetoid G ξ A).r u v)
include he hrelated

/-- An absent edge inside an existing wired component changes only the two
Bernoulli factors in the FK weight. -/
theorem weight_insert_balance_of_related  :
    (1 - edgeParameter q) * weight G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      edgeParameter q * weight G q ξ A := by
  have hcard : A.card + 1 ≤ Nat.card G.edgeSet := by
    let : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
    rw [Nat.card_eq_fintype_card, ← Finset.card_insert_of_notMem he]
    exact Finset.card_le_univ _
  
  rw [weight, weight, Finset.card_insert_of_notMem he, componentCount_insert_eq_of_related ξ A huv hrelated, (by omega : Nat.card G.edgeSet - A.card =
       Nat.card G.edgeSet - (A.card + 1)  + 1)]
  ring

theorem configurationProbability_insert_balance_of_related  :
    (1 - edgeParameter q) *
        configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) =
      edgeParameter q * configurationProbability G q ξ A := by
  grind [configurationProbability, weight_insert_balance_of_related]

/-- The open probability conditional on the two possible states of this edge,
with every other original edge fixed by `A`, equals the edge parameter. -/
theorem configurationProbability_pair_ratio_of_related  :
    configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A) /
      (configurationProbability G q ξ A +
        configurationProbability G q ξ (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ A)) =
      edgeParameter q := by
  apply (div_eq_iff (add_pos (configurationProbability_pos G q ξ A)
    (configurationProbability_pos G q ξ _)).ne').mpr
  
  nlinarith only [ configurationProbability_insert_balance_of_related q ξ A huv he hrelated ]

end

end PottsDiscontinuity.FK
