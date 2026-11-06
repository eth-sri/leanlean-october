/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedFaceIncidence
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

noncomputable def faceGraphEdges {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ G.edgeSet

private theorem coverFaceBoundary_edgeFinset_card_four {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).card = 4 := by
  
  let f := i.1
  
  obtain ⟨q, hcycle, hlength, hsupp⟩ :=
    parafermionicCoverFiniteOrdinaryFace_has_cycle n f  (Finset.mem_filter.mp i.2).1  i.2
  let b0 : ParafermionicCoverBoxVertex n := ⟨f,  (Finset.mem_filter.mp i.2).1 ⟩
  let b1 : ParafermionicCoverBoxVertex n := ⟨
    parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2, (parafermionicCoverFiniteFaceDart_endpoints_mem n f i.2
                                                 (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
                                                 (by simp [parafermionicCoverFiniteFaceDarts])).2⟩
  let b2 : ParafermionicCoverBoxVertex n := ⟨
    parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2, (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f i.2).1⟩
  let b3 : ParafermionicCoverBoxVertex n := ⟨
    parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f i.2).2⟩
  have hsupp' : q.support = [b0,b1,b2,b3,b0] := by
    apply Function.Injective.list_map Subtype.val_injective
    all_goals aesop
  have hqedges : q.edges = [s(b0,b1),s(b1,b2),s(b2,b3),s(b3,b0)] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hsupp']
    rfl
  
  have hqset : q.edgeSet =
      (parafermionicCoverFiniteFaceBoundaryGraph f i.2).edgeSet := by
    rw [SimpleGraph.Walk.edgeSet, hqedges,
      parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
    ext e
    change  e ∈ [s(b0,b1),s(b1,b2),s(b2,b3),s(b3,b0)]  ↔
      e ∈  {s(b0,b1),s(b1,b2),s(b2,b3),s(b3,b0)} 
    simp
  have hfinset : q.edges.toFinset =
      faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph f i.2) := by
    ext e
    simp only [List.mem_toFinset, faceGraphEdges, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change e ∈ q.edgeSet ↔
      e ∈ (parafermionicCoverFiniteFaceBoundaryGraph f i.2).edgeSet
    rw [hqset]
  rw [← hfinset]
  exact  by
           rw [List.toFinset_card_of_nodup hcycle.isTrail.edges_nodup,
             q.length_edges, hlength] 


noncomputable def parafermionicCoverFiniteFaceSetEdgeSupport {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Finset (Sym2 (ParafermionicCoverBoxVertex n)) := by
  classical
  exact Finset.univ.filter fun e =>
    (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).Nonempty

noncomputable def parafermionicCoverFiniteFaceSetBoundaryEdges {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))  :=
  faceGraphEdges (parafermionicCoverFiniteFaceSetBoundaryGraph S)

noncomputable def faceIncidencePairsByFace {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Finset (ParafermionicCoverFiniteFaceTopIndex n ×
      Sym2 (ParafermionicCoverBoxVertex n)) := by
  classical
  exact S.biUnion fun i =>
    (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).image
      fun e => (i,e)

noncomputable def faceIncidencePairsByEdge {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Finset (ParafermionicCoverFiniteFaceTopIndex n ×
      Sym2 (ParafermionicCoverBoxVertex n)) := by
  classical
  exact (parafermionicCoverFiniteFaceSetEdgeSupport S).biUnion fun e =>
    (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).image
      fun i => (i,e)

section

variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))


private theorem faceIncidencePairsByFace_card  :
    (faceIncidencePairsByFace S).card =
      ∑ i ∈ S,
        (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).card := by
  
  let T := fun i : ParafermionicCoverFiniteFaceTopIndex n =>
    (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).image
      fun e => (i,e)
  have hdisj : (S : Set (ParafermionicCoverFiniteFaceTopIndex n)).PairwiseDisjoint T := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    rcases Finset.mem_image.mp hzi with ⟨e,he,rfl⟩
    rcases Finset.mem_image.mp hzj with ⟨e',he',hEq⟩
    exact hij (by simpa [eq_comm] using congrArg Prod.fst hEq)
  rw [faceIncidencePairsByFace, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro i hi
  
  exact Finset.card_image_of_injective _  fun e e' h => congrArg Prod.snd h 

private theorem faceIncidencePairsByEdge_card  :
    (faceIncidencePairsByEdge S).card =
      ∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
        (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card := by
  
  let T := fun e  =>
    (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).image fun i => (i,e)
  have hdisj :
      (parafermionicCoverFiniteFaceSetEdgeSupport S :
        Set (Sym2 (ParafermionicCoverBoxVertex n))).PairwiseDisjoint T := by
    intro e he e' he' hee'
    apply Finset.disjoint_left.mpr
    intro z hze hze'
    rcases Finset.mem_image.mp hze with ⟨i,hi,rfl⟩
    rcases Finset.mem_image.mp hze' with ⟨i',hi',hEq⟩
    exact hee' (by simpa [eq_comm] using congrArg Prod.snd hEq)
  rw [faceIncidencePairsByEdge, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro e he
  
  exact Finset.card_image_of_injective _  fun i i' h => congrArg Prod.fst h 

private theorem faceIncidencePairs_eq  :
    faceIncidencePairsByFace S = faceIncidencePairsByEdge S := by
  classical
  ext z
  rcases z with ⟨i,e⟩
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨j,hj,himg⟩
    rcases Finset.mem_image.mp himg with ⟨e',he',heq⟩
    have hij : j = i := congrArg Prod.fst heq
    have heq' : e' = e := congrArg Prod.snd heq
    subst j
    subst e'
    have hiInc : i ∈ parafermionicCoverFiniteFaceIncidentFaces e :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he').2⟩
    have hiSel  :=
      Finset.mem_filter.mpr ⟨hiInc,hj⟩
    
    exact Finset.mem_biUnion.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i,hiSel⟩⟩ ,Finset.mem_image.mpr ⟨i,hiSel,rfl⟩⟩
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨e',he,himg⟩
    rcases Finset.mem_image.mp himg with ⟨j,hj,heq⟩
    have hij : j = i := congrArg Prod.fst heq
    have heq' : e' = e := congrArg Prod.snd heq
    subst j
    subst e'
    have hmem := Finset.mem_filter.mp hj
    
    
    exact Finset.mem_biUnion.mpr
      ⟨i,hmem.2,Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,  (Finset.mem_filter.mp hmem.1).2 ⟩ ,rfl⟩⟩


private theorem faceSet_edgeSupport_boundary_subset  :
    parafermionicCoverFiniteFaceSetBoundaryEdges S ⊆
      parafermionicCoverFiniteFaceSetEdgeSupport S := by
  classical
  intro e he
  
  have hone :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
      S e).1  (Finset.mem_filter.mp he).2 
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, Finset.card_pos.mp (by omega)⟩

private theorem faceSet_faceIncidence_count  :
    (faceIncidencePairsByFace S).card = 4 * S.card := by
  
  rw [faceIncidencePairsByFace_card]
  calc
     ∑ i ∈ S,
        (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).card  =
        ∑ i ∈ S,  4  := by
          simp_all [coverFaceBoundary_edgeFinset_card_four]
    _ = 4 * S.card := by simp [mul_comm]

private alias faceSet_edgeIncidence_count := _root_.PottsDiscontinuity.TorusTopology.Planar.Medial.faceIncidencePairsByEdge_card

private theorem faceSet_boundary_indicator_sum  :
    (∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
      if e ∈ parafermionicCoverFiniteFaceSetBoundaryEdges S then 1 else 0) =
      (parafermionicCoverFiniteFaceSetBoundaryEdges S).card := by
  
  rw [Finset.sum_ite]
  simp [faceSet_edgeSupport_boundary_subset]

private theorem faceSet_local_incidence_equation  :
     ∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
      ((parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card +
         if e ∈ parafermionicCoverFiniteFaceSetBoundaryEdges S then 1 else 0 )  =
      2 * (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
  classical
  
  calc
    _ = ∑ _e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,  2  := Finset.sum_congr rfl (by
                                                                                                intro e he
                                                                                                have hpos : 0 < (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card := by
                                                                                                  grind +locals
                                                                                                by_cases hb : e ∈ parafermionicCoverFiniteFaceSetBoundaryEdges S
                                                                                                · 
                                                                                                  have hone :=
                                                                                                    (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
                                                                                                      S e).1  (Finset.mem_filter.mp hb).2 
                                                                                                  simp [hone, hb]
                                                                                                · have hle := parafermionicCoverFiniteFaceSelectedIncidentFaces_card_le_two S e
                                                                                                  have hnotone : (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card ≠ 1 := fun hone =>
                                                                                                                                                                                       hb
                                                                                                                                                                                         (Finset.mem_filter.mpr
                                                                                                                                                                                           ⟨Finset.mem_univ e,
                                                                                                                                                                                             (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one S e).mpr hone⟩)
                                                                                                  simp [hb]
                                                                                                  omega)
    _ = 2 * (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by simp [mul_comm]

/-- Counting the four actual boundary edges of every selected face counts an
interior edge twice and a selected-set boundary edge once. -/
theorem parafermionicCoverFiniteFaceSetEdgeCount  :
    4 * S.card + (parafermionicCoverFiniteFaceSetBoundaryEdges S).card =
      2 * (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
  
  have hpairs := faceIncidencePairs_eq S
  have hface := faceSet_faceIncidence_count S
  have hedge := faceSet_edgeIncidence_count S
  
  
  have hlocal := faceSet_local_incidence_equation S
  have hsum :
       ∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
        (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card  = 4 * S.card := by
    simp_all
  rw [Finset.sum_add_distrib, hsum,  faceSet_boundary_indicator_sum S ] at hlocal
  exact hlocal

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
