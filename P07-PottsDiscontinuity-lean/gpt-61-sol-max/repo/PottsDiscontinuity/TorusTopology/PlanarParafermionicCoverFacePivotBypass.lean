/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceBoundaryGraph
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotGeometry
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial


open SimpleGraph

private theorem reachable_of_sym2_pair_eq {V : Type*} (G : SimpleGraph V)
    {e : Sym2 V} {x y : V} (he : e = s(x,y))
    (h : G.Reachable x y) : G.Reachable e.out.1 e.out.2 := by
  have hout : s(e.out.1,e.out.2) = s(x,y) := by
    rw [Sym2.mk, e.out_eq, he]
  rcases Sym2.eq_iff.mp hout with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · simpa [h₁,h₂] using h
  · simpa [h₁,h₂] using h.symm

/-- The three nonpivot sides of an actual retained lifted face connect the
endpoints of its top pivot after deleting that pivot alone. -/
theorem parafermionicCoverFiniteFaceTopPivot_bypass {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    ((parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).deleteEdges
      {parafermionicCoverFiniteFaceTopPivot n i}).Reachable
        (parafermionicCoverFiniteFaceTopPivot n i).out.1
        (parafermionicCoverFiniteFaceTopPivot n i).out.2 := by
  
  let f := i.1
  let hf := i.2
  let b0 : ParafermionicCoverBoxVertex n :=
    ⟨f, (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
      (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
      (by simp [parafermionicCoverFiniteFaceDarts])).1⟩
  let b1 : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
        (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
        (by simp [parafermionicCoverFiniteFaceDarts])).2⟩
  let b2 : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩
  let b3 : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩
  let G := parafermionicCoverFiniteFaceBoundaryGraph f hf
  let p := parafermionicCoverFiniteFaceTopPivot n i
  
  have hmapRight : Sym2.map Subtype.val  s(b1,b2)  =
      parafermionicCoverFiniteFaceRightEdge f := rfl
  have hmapBottom : Sym2.map Subtype.val  s(b0,b1)  =
      parafermionicCoverFiniteFaceBottomEdge f := rfl
  have hmapLeft : Sym2.map Subtype.val  s(b3,b0)  =
      parafermionicCoverFiniteFaceLeftEdge f := rfl
  have hEdgeOfRaw (e : Sym2 (ParafermionicCoverBoxVertex n))
      (he : Sym2.map Subtype.val e ∈
        ({parafermionicCoverFiniteFaceBottomEdge f,
         parafermionicCoverFiniteFaceRightEdge f,
         parafermionicCoverFiniteFaceTopEdge f,
         parafermionicCoverFiniteFaceLeftEdge f} :
          Set (Sym2 ParafermionicCoverVertex))) : e ∈ G.edgeSet := by
    have himg : Sym2.map Subtype.val e ∈
        Sym2.map Subtype.val '' G.edgeSet := by
      rw [parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet]
      exact he
    rcases (Set.mem_image _ _ _).mp himg with ⟨e', he', heq⟩
    
    simpa [ Sym2.map.injective Subtype.val_injective heq ] using he'
  have hright : G.Adj b1 b2 := by
    apply (SimpleGraph.mem_edgeSet G).mp
    apply hEdgeOfRaw
    erw [hmapRight]
    simp
  have hbottom : G.Adj b0 b1 := by
    apply (SimpleGraph.mem_edgeSet G).mp
    apply hEdgeOfRaw
    erw [hmapBottom]
    simp
  have hleft : G.Adj b3 b0 := by
    apply (SimpleGraph.mem_edgeSet G).mp
    apply hEdgeOfRaw
    erw [hmapLeft]
    simp
  
  
  have hleft_ne : s(b3,b0) ≠ p := fun he =>
                                    parafermionicCoverFiniteFaceLeftEdge_ne_topEdge hf hf
                                      (Eq.trans (Eq.trans (Eq.symm hmapLeft) (congrArg (Sym2.map Subtype.val) he))
                                        (parafermionicCoverFiniteFaceTopPivot_map n i))
  
  
  have hleft' : (G.deleteEdges {p}).Adj b0 b3 := by
    apply (SimpleGraph.deleteEdges_adj).2
    have hne  := fun he => hleft_ne (Trans.trans Sym2.eq_swap he)
    exact ⟨hleft.symm, by simpa using hne⟩
  have hwalk  :=
    Walk.cons (by
                 apply (SimpleGraph.deleteEdges_adj).2
                 have hne  := fun he => (fun he =>
                                                                                          parafermionicCoverFiniteFaceRightEdge_ne_topEdge hf hf
                                                                                            (Eq.trans (Eq.trans (Eq.symm hmapRight) (congrArg (Sym2.map Subtype.val) he))
                                                                                              (parafermionicCoverFiniteFaceTopPivot_map n i))) (Trans.trans Sym2.eq_swap he)
                 exact ⟨hright.symm, by simpa using hne⟩) (Walk.cons (by
                                    apply (SimpleGraph.deleteEdges_adj).2
                                    have hne  := fun he => (fun he =>
                                                                                                              parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le hf hf le_rfl
                                                                                                                (Eq.trans (Eq.trans (Eq.symm hmapBottom) (congrArg (Sym2.map Subtype.val) he))
                                                                                                                  (parafermionicCoverFiniteFaceTopPivot_map n i))) (Trans.trans Sym2.eq_swap he)
                                    exact ⟨hbottom.symm, by simpa using hne⟩) (Walk.cons hleft' Walk.nil))
  exact reachable_of_sym2_pair_eq (G.deleteEdges {p}) (e := p) (x := b2) (y := b3) (rfl) hwalk.reachable

end PottsDiscontinuity.TorusTopology.Planar.Medial
