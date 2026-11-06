/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenSubgraphOfCycle
public import PottsDiscontinuity.TorusTopology.PlanarFiniteFaceSubfamilyBoundary
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetBoundary
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFilling

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial





theorem faceSymmDiffList_eq_of_perm
    {V I : Type*} [DecidableEq I] (F : I → SimpleGraph V)
    {L M : List I} (hperm : List.Perm L M) :
    faceSymmDiffList F L = faceSymmDiffList F M := by
  classical
  ext x y
  constructor
  · intro hxy
    
    
    
    exact (faceSymmDiffList F M).mem_edgeSet.mp
      ((faceSymmDiffList_edge_iff_countP_mod F M s(x,y)).mpr (by
                                                                rw [← hperm.countP_eq  fun i => decide (s(x,y) ∈ (F i).edgeSet) ]
                                                                exact  (faceSymmDiffList_edge_iff_countP_mod F L s(x,y)).mp ((faceSymmDiffList F L).mem_edgeSet.mpr hxy) ))
  · intro hxy
    
    
    
    exact (faceSymmDiffList F L).mem_edgeSet.mp
      ((faceSymmDiffList_edge_iff_countP_mod F L s(x,y)).mpr (by
                                                                rw [hperm.countP_eq  fun i => decide (s(x,y) ∈ (F i).edgeSet) ]
                                                                exact  (faceSymmDiffList_edge_iff_countP_mod F M s(x,y)).mp ((faceSymmDiffList F M).mem_edgeSet.mpr hxy) ))

section

variable {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n} (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
include hn hp

theorem parafermionicCoverSimpleCycleFillingSet_no_disjoint_nonempty_subfamily
    
    (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hTsub : T ⊆ parafermionicCoverSimpleCycleFillingSet hn p hp)
    (hTnonempty : T.Nonempty)
    (hcross : ∀ i ∈ T,
      ∀ j ∈ parafermionicCoverSimpleCycleFillingSet hn p hp, j ∉ T →
        Disjoint (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet
          (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet) :
    T = parafermionicCoverSimpleCycleFillingSet hn p hp := by
  
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let F : ParafermionicCoverFiniteFaceTopIndex n →
      SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2
  
  obtain ⟨⟨L, hLnodup, hLS, hLcycle⟩, hSnonempty, hScoeff⟩ :=  parafermionicCoverSimpleCycleFillingSet_spec hn p hp 
  have hperm  :=
    List.perm_of_nodup_nodup_toFinset_eq hLnodup S.nodup_toList
      (hLS.trans (Finset.toList_toFinset S).symm)
  have hScycle : faceSymmDiffList F S.toList = p.toSubgraph.spanningCoe := by
    grind [faceSymmDiffList_eq_of_perm]
  have hsmallBoundary := faceSymmDiffList_le_of_no_cross_shared_edge
    F T S hTsub  hcross 
  
  
  
  
  have hTcycle : faceSymmDiffList F T.toList = p.toSubgraph.spanningCoe := Or.casesOn (evenSubgraphOfCycle_eq_bot_or_cycle p hp
                                                                                         (parafermionicCoverFiniteFaceSetBoundaryGraph T) (by
                                                                                                                                             change faceSymmDiffList F T.toList ≤ p.toSubgraph.spanningCoe
                                                                                                                                             all_goals grind) (parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree T)) (fun hbot => False.elim (((parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff T).2 hTnonempty) hbot)) fun hcycle => hcycle
  
  have hsets  := (parafermionicCoverFiniteFaceChain_toFinset_unique
                    T.toList S.toList T.nodup_toList S.nodup_toList (by rw [hTcycle, hScycle]))
  simpa using hsets


theorem parafermionicCoverSimpleCycleFillingSet_boundary_eq
     :
    parafermionicCoverFiniteFaceSetBoundaryGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp) =
      p.toSubgraph.spanningCoe := by
  
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  
  obtain ⟨⟨L, hLnodup, hLS, hLcycle⟩, _, _⟩ :=  parafermionicCoverSimpleCycleFillingSet_spec hn p hp 
  
  change faceSymmDiffList
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) S.toList = _
  rw [← faceSymmDiffList_eq_of_perm _ (List.perm_of_nodup_nodup_toFinset_eq hLnodup S.nodup_toList
                                           (hLS.trans (Finset.toList_toFinset S).symm))]
  exact hLcycle

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
