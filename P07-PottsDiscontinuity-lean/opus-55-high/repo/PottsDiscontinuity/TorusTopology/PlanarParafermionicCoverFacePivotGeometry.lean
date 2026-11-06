/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopTree

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable (n : ℕ)
abbrev ParafermionicCoverFiniteFaceTopIndex  :=
  {f : ParafermionicCoverVertex // f ∈ parafermionicCoverFiniteOrdinaryFaces n}

/-- The retained face's actual positively oriented top edge, carried by the
finite box vertex type. -/
def parafermionicCoverFiniteFaceTopPivot (f : ParafermionicCoverFiniteFaceTopIndex n) :
    Sym2 (ParafermionicCoverBoxVertex n) :=
  s(⟨parafermionicCoverFaceRightUpLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).1⟩,
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1.1 f.1.1.2 f.1.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f.1 f.2).2⟩)

theorem parafermionicCoverFiniteFaceTopPivot_map (f : ParafermionicCoverFiniteFaceTopIndex n) :
    Sym2.map Subtype.val (parafermionicCoverFiniteFaceTopPivot n f) =
      parafermionicCoverFiniteFaceTopEdge f.1 := by
  rfl

theorem parafermionicCoverFiniteFaceTopPivot_injective  :
    Function.Injective (parafermionicCoverFiniteFaceTopPivot n) := by
  intro f g h
  apply Subtype.ext
  apply parafermionicCoverFiniteFaceTopEdge_injective n f.2 g.2
  have hm := congrArg (Sym2.map Subtype.val) h
  tauto


def parafermionicCoverFiniteFaceTopRank (f : ParafermionicCoverFiniteFaceTopIndex n) : ℕ :=
  (f.1.1.2 + (n : ℤ)).toNat

theorem parafermionicCoverFiniteFaceTopRank_strict_height {f g : ParafermionicCoverFiniteFaceTopIndex n}
    (hheight : f.1.1.2 < g.1.1.2) :
    parafermionicCoverFiniteFaceTopRank n f <
      parafermionicCoverFiniteFaceTopRank n g := by
  have hf := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n f.1).mp f.2
  grind [parafermionicCoverFiniteFaceTopRank]

theorem parafermionicCoverBoxGraph_deleteTopPivots_eq  :
    (parafermionicCoverBoxGraph n).deleteEdges
      (Set.range (parafermionicCoverFiniteFaceTopPivot n)) =
        parafermionicCoverBoxGraphWithoutFaceTops n := by
  ext u v
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hadj,hnot⟩
    refine ⟨hadj,?_⟩
    intro f hf htop
    let f' : ParafermionicCoverFiniteFaceTopIndex n := ⟨f,hf⟩
    have hmap : Sym2.map Subtype.val (parafermionicCoverFiniteFaceTopPivot n f') =
        Sym2.map Subtype.val (s(u,v)) := by
      tauto
    have heq :=
      Sym2.map.injective Subtype.val_injective hmap
    grind
  · rintro ⟨hadj,hnot⟩
    refine ⟨hadj,?_⟩
    intro hmem
    obtain ⟨f,heq⟩ := Set.mem_range.mp hmem
    apply hnot f.1 f.2
    have hmap := congrArg (Sym2.map Subtype.val) heq
    tauto

theorem parafermionicCoverBoxGraph_deleteTopPivots_isAcyclic
    (hn : 1 ≤ n) :
    ((parafermionicCoverBoxGraph n).deleteEdges
      (Set.range (parafermionicCoverFiniteFaceTopPivot n))).IsAcyclic := by
  rw [parafermionicCoverBoxGraph_deleteTopPivots_eq]
  exact (parafermionicCoverBoxGraphWithoutFaceTops_isTree n hn).isAcyclic
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
