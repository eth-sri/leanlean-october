/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionConnectivity
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetEdgeCount
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

theorem parafermionicCoverFiniteFaceUnionGraph_edgeSet_eq_support {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    (parafermionicCoverFiniteFaceUnionGraph S).edgeSet =
      (parafermionicCoverFiniteFaceSetEdgeSupport S :
        Set (Sym2 (ParafermionicCoverBoxVertex n))) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf v w =>
      simp only [parafermionicCoverFiniteFaceUnionGraph,
        parafermionicCoverFiniteFaceSetEdgeSupport,
        parafermionicCoverFiniteFaceSelectedIncidentFaces,
        parafermionicCoverFiniteFaceIncidentFaces,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.Nonempty, SimpleGraph.mem_edgeSet]
      simp only [and_comm]

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (H : SimpleGraph (ParafermionicCoverBoxVertex n)) (hH : H ≤ parafermionicCoverFiniteFaceUnionGraph S)
include H hH
theorem parafermionicCoverFaceUnionSubgraph_support_subset  :
    H.support ⊆ parafermionicCoverFiniteFaceUnionCarrier S := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  exact ⟨w, hH hvw⟩

theorem parafermionicCoverFiniteFaceUnionCarrier_induce_reachable_iff
    (v w : ParafermionicCoverBoxVertex n)
    (hv : v ∈ parafermionicCoverFiniteFaceUnionCarrier S)
    (hw : w ∈ parafermionicCoverFiniteFaceUnionCarrier S) :
    H.Reachable v w ↔
      (H.induce (parafermionicCoverFiniteFaceUnionCarrier S)).Reachable
        ⟨v, hv⟩ ⟨w, hw⟩ := by
  constructor
  · rintro ⟨p⟩
    have hsupp : ∀ x ∈ p.support,
        x ∈ parafermionicCoverFiniteFaceUnionCarrier S := by
      induction p with
      | nil =>
          simp_all
      | @cons a b c hab tail ih =>
          intro x hx
          rcases List.mem_cons.mp hx with hxa | hxt
          · grind
          · have hb : b ∈ parafermionicCoverFiniteFaceUnionCarrier S :=
              ⟨a, (hH hab).symm⟩
            grind
    exact ⟨p.induce (parafermionicCoverFiniteFaceUnionCarrier S) hsupp⟩
  · rintro ⟨p⟩
    exact ⟨p.map (Embedding.induce
      (parafermionicCoverFiniteFaceUnionCarrier S)).toHom⟩

theorem parafermionicCoverFiniteFaceUnionCarrier_induce_edgeSet_card
     :
    Nat.card {e // e ∈ (H.induce
        (parafermionicCoverFiniteFaceUnionCarrier S)).edgeSet} =
      Nat.card {e // e ∈ H.edgeSet} := by
  classical
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_induce_of_support_subset (parafermionicCoverFaceUnionSubgraph_support_subset S H hH),
    SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
