/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteEdgeCount
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaceCount

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The actual finite vertex, ordinary-face, and edge counts satisfy this integer
identity for the literal parafermionic cover carriers. This is a numerical count
identity only. -/
theorem parafermionicCoverFiniteEulerCount (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (ParafermionicCoverBoxVertex n) +
        (parafermionicCoverFiniteOrdinaryFaces n).card =
      (parafermionicCoverBoxGraph n).edgeFinset.card + 1 := by
  let S := 2*n^5+1
  let V := Fintype.card (ParafermionicCoverBoxVertex n)
  let F := (parafermionicCoverFiniteOrdinaryFaces n).card
  let E := (parafermionicCoverBoxGraph n).edgeFinset.card
  have hV :=
    parafermionicCoverBoxVertex_card n
  have hF :=
    parafermionicCoverFiniteOrdinaryFaces_card n hn
  have hE :=
    parafermionicCoverBoxGraph_edgeFinset_card_add_n n (by omega)
  grind

end PottsDiscontinuity.TorusTopology.Planar.Medial
