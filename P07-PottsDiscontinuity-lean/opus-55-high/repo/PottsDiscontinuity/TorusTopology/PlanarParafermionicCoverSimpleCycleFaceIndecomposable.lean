/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenSubgraphOfCycle
public import PottsDiscontinuity.TorusTopology.PlanarFiniteFaceSubfamilyBoundary
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetBoundary
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFilling

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open scoped symmDiff

theorem faceSymmDiffList_eq_of_perm
    {V I : Type*} [DecidableEq I] (F : I → SimpleGraph V)
    {L M : List I} (hperm : List.Perm L M) :
    faceSymmDiffList F L = faceSymmDiffList F M := by
  classical
  ext x y
  constructor
  · intro hxy
    have hmod := (faceSymmDiffList_edge_iff_countP_mod F L s(x,y)).mp (by simp_all)
    have hmod' : (M.countP (fun i => decide (s(x,y) ∈ (F i).edgeSet))) % 2 = 1 := by
      rw [← hperm.countP_eq (fun i => decide (s(x,y) ∈ (F i).edgeSet))]
      omega
    exact (faceSymmDiffList F M).mem_edgeSet.mp
      ((faceSymmDiffList_edge_iff_countP_mod F M s(x,y)).mpr hmod')
  · intro hxy
    have hmod := (faceSymmDiffList_edge_iff_countP_mod F M s(x,y)).mp (by simp_all)
    have hmod' : (L.countP (fun i => decide (s(x,y) ∈ (F i).edgeSet))) % 2 = 1 := by
      rw [hperm.countP_eq (fun i => decide (s(x,y) ∈ (F i).edgeSet))]
      omega
    exact (faceSymmDiffList F L).mem_edgeSet.mp
      ((faceSymmDiffList_edge_iff_countP_mod F L s(x,y)).mpr hmod')

section
variable {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n} (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
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
  obtain ⟨⟨L, hLnodup, hLS, hLcycle⟩, hSnonempty, hScoeff⟩ := (parafermionicCoverSimpleCycleFillingSet_spec hn p hp)
  have hperm :=
    List.perm_of_nodup_nodup_toFinset_eq hLnodup S.nodup_toList
      (hLS.trans (Finset.toList_toFinset S).symm)
  have hScycle : faceSymmDiffList F S.toList = p.toSubgraph.spanningCoe := by
    grind [faceSymmDiffList_eq_of_perm]
  have hsmallBoundary := faceSymmDiffList_le_of_no_cross_shared_edge
    F T S hTsub (by
      omega)
  have hsmallLe : parafermionicCoverFiniteFaceSetBoundaryGraph T ≤
      p.toSubgraph.spanningCoe := by
    change faceSymmDiffList F T.toList ≤ p.toSubgraph.spanningCoe
    grind
  have hsmallNonbot :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff T).2 hTnonempty
  have hsmallCycle := evenSubgraphOfCycle_eq_bot_or_cycle p hp
    (parafermionicCoverFiniteFaceSetBoundaryGraph T) hsmallLe (parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree T)
  have hTcycle : faceSymmDiffList F T.toList = p.toSubgraph.spanningCoe := by
    tauto
  have hlists := parafermionicCoverFiniteFaceChain_toFinset_unique
    T.toList S.toList T.nodup_toList S.nodup_toList (by grind)
  simpa using hlists


theorem parafermionicCoverSimpleCycleFillingSet_boundary_eq
     :
    parafermionicCoverFiniteFaceSetBoundaryGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp) =
      p.toSubgraph.spanningCoe := by
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  obtain ⟨⟨L, hLnodup, hLS, hLcycle⟩, _, _⟩ := (parafermionicCoverSimpleCycleFillingSet_spec hn p hp)
  have hperm :=
    List.perm_of_nodup_nodup_toFinset_eq hLnodup S.nodup_toList
      (hLS.trans (Finset.toList_toFinset S).symm)
  change faceSymmDiffList
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) S.toList = _
  rwa [← faceSymmDiffList_eq_of_perm _ hperm]
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
