/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetEdgeCount
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleComplementConnectivity

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial




section

variable {n : ℕ}
include n

section

variable (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (e : Sym2 (ParafermionicCoverBoxVertex n))


private theorem fillingContainment_selectedIncident_mem 
    
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces S e ↔
      i ∈ S ∧ e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  grind [parafermionicCoverFiniteFaceSelectedIncidentFaces, parafermionicCoverFiniteFaceIncidentFaces]

private theorem fillingContainment_support_mem_iff 
     :
    e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S ↔
      (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).Nonempty := by
  grind [parafermionicCoverFiniteFaceSetEdgeSupport]

end

private theorem fillingContainment_no_three_incident 
    (e : Sym2 (ParafermionicCoverBoxVertex n))
    (i j k : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hj : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hk : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet) : False := by
  
  let I := parafermionicCoverFiniteFaceIncidentFaces e
  have hiI : i ∈ I := by
    grind [parafermionicCoverFiniteFaceIncidentFaces]
  have hjI : j ∈ I := by
    grind [parafermionicCoverFiniteFaceIncidentFaces]
  have hkI : k ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces]
    grind
  have hsub :  {i,j,k}  ⊆ I := by
    grind
  have hthree : ({i,j,k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)).card = 3 := by
    simp [hij,hik,hjk]
  have hcard := Finset.card_le_card hsub
  have hbound := parafermionicCoverFiniteFaceIncidentFaces_card_le_two e
  dsimp [I] at hcard hbound
  omega

private theorem fillingContainment_crossEdge_card_one 
    (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (e : Sym2 (ParafermionicCoverBoxVertex n)) (hij : i ≠ j)
    (hiEdge : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hjEdge : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hiT : i ∈ T) (hjT : j ∉ T) :
    (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card = 1 := by
  
  have hiSelected  :=
    (fillingContainment_selectedIncident_mem T e i).2 ⟨hiT, hiEdge⟩
  have hle : (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card ≤ 1 :=
    Finset.card_le_one.mpr (by
      intro a ha b hb
      have haData := (fillingContainment_selectedIncident_mem T e a).mp ha
      have hbData := (fillingContainment_selectedIncident_mem T e b).mp hb
      have haEq : a = i := by
        by_contra hneai
        
        exact fillingContainment_no_three_incident e i j a hij (Ne.symm hneai) (by
                                                                                  intro heq
                                                                                  subst a
                                                                                  exact hjT haData.1)
          hiEdge hjEdge haData.2
      have hbEq : b = i := by
        by_contra hnebi
        
        exact fillingContainment_no_three_incident e i j b hij (Ne.symm hnebi) (by
                                                                                  intro heq
                                                                                  subst b
                                                                                  exact hjT hbData.1)
          hiEdge hjEdge hbData.2
      exact haEq.trans hbEq.symm)
  grind

section

variable (S T : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (hsub : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport S : Set (Sym2 (ParafermionicCoverBoxVertex n))))
include hsub

private theorem fillingContainment_exposed_not_mem 
    
    (i : ParafermionicCoverFiniteFaceTopIndex n) (hiS : i ∉ S)
    (e : Sym2 (ParafermionicCoverBoxVertex n))
    (hiEdge : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hexposed : ∀ j, j ≠ i → e ∉
      (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet) :
    i ∉ T := by
  intro hiT
  
  
  
  obtain ⟨k,hk⟩ := (fillingContainment_support_mem_iff S e).mp (hsub ((parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
                                                                          T e).2 (by
                                                                                    have hle  :=
                                                                                      Finset.card_le_one.mpr (by
                                                                                                                exact fun a ha b hb =>
                                                                                                                        Eq.trans
                                                                                                                          (Decidable.byContradiction fun hneai =>
                                                                                                                            hexposed a hneai ((fillingContainment_selectedIncident_mem T e a).mp ha).right)
                                                                                                                          (Eq.symm
                                                                                                                            (Decidable.byContradiction fun hnebi =>
                                                                                                                              hexposed b hnebi ((fillingContainment_selectedIncident_mem T e b).mp hb).right)))
                                                                                    have hpos  :=
                                                                                      Finset.card_pos.mpr ⟨i, (fillingContainment_selectedIncident_mem T e i).2 ⟨hiT,hiEdge⟩⟩
                                                                                    omega)))
  obtain ⟨hkS,hkEdge⟩ := (fillingContainment_selectedIncident_mem S e k).mp hk
  
  exact (hexposed k (by
                       intro heq
                       subst k
                       exact hiS hkS) hkEdge).elim

private theorem fillingContainment_crossEdge_forces_both_or_neither 
    
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hiS : i ∉ S) (hjS : j ∉ S)
    (hij : (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j) :
    i ∈ T ↔ j ∈ T := by
  
  rcases hij with ⟨hne, e, hiEdge, hjEdge⟩
  constructor
  · intro hiT
    by_contra hjT
    
    
    obtain ⟨k, hk⟩ := (fillingContainment_support_mem_iff S e).mp (hsub ((parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
                                                                             T e).2 (fillingContainment_crossEdge_card_one T i j e hne hiEdge hjEdge hiT hjT)))
    obtain ⟨hkS, hkEdge⟩ := (fillingContainment_selectedIncident_mem S e k).mp hk
    have hki : k ≠ i := by intro heq; subst k; exact hiS hkS
    
    exact fillingContainment_no_three_incident e i j k hne hki.symm (by
                                                                       intro heq
                                                                       subst k
                                                                       exact hjS hkS) hiEdge hjEdge hkEdge
  · intro hjT
    by_contra hiT
    
    
    obtain ⟨k, hk⟩ := (fillingContainment_support_mem_iff S e).mp (hsub ((parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
                                                                             T e).2 (fillingContainment_crossEdge_card_one T j i e hne.symm hjEdge hiEdge hjT hiT)))
    obtain ⟨hkS, hkEdge⟩ := (fillingContainment_selectedIncident_mem S e k).mp hk
    have hkj : k ≠ j := by intro heq; subst k; exact hjS hkS
    
    exact fillingContainment_no_three_incident e j i k hne.symm hkj.symm (by
                                                                            intro heq
                                                                            subst k
                                                                            exact hiS hkS) hjEdge hiEdge hkEdge

end

/-- If the symmetric-difference boundary of a finite actual face family uses
only edges in a fixed cycle filling's actual face support, then every face in
the family belongs to that filling. -/
theorem parafermionicCoverSimpleCycleFillingSet_contains_boundary_supported_faces
     (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hsub : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport
        (parafermionicCoverSimpleCycleFillingSet hn p hp) :
          Set (Sym2 (ParafermionicCoverBoxVertex n)))) :
    T ⊆ parafermionicCoverSimpleCycleFillingSet hn p hp := by
  
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let Cset := parafermionicCoverSimpleCycleComplementCarrier S
  let G  :=
    parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n
  let C  := G.induce Cset
  let root : Cset := ⟨none, by simp [Cset, parafermionicCoverSimpleCycleComplementCarrier]⟩
  
  
  intro i hiT
  by_contra hiS
  
  obtain ⟨walk⟩ := ((parafermionicCoverSimpleCycleComplementAdjacency_connected hn p hp).preconnected root)  ⟨some i, hiS⟩ 
  let P : Cset → Prop := fun x => x.1.elim False  fun j => j ∈ T 
  have hboundaryStable : ∀ {x y }, (w : C.Walk x y) →  P x ↔ P y  := by
    intro x y w
    induction w with
    | nil => simp
    | @cons x y z hadj tail ih =>
        have hstep : P x ↔ P y := by
          change G.Adj x.1 y.1 at hadj
          cases hx : x.1 with
          | none =>
            cases hy : y.1 with
            | none =>
              simp_all
            | some j =>
              obtain ⟨e, hjEdge, hexposed⟩ :=
                (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_none_some_iff j).mp
                  (by aesop)
              
              have hjT := fillingContainment_exposed_not_mem S T hsub j (by
                                                                           aesop) e hjEdge hexposed
              simp [P, hx, hy, hjT]
          | some i =>
            cases hy : y.1 with
            | none =>
              have hadj' : ∃ e, e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet ∧
                  ∀ j, j ≠ i → e ∉ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
                simpa [G, hx, hy, parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph] using hadj
              obtain ⟨e, hiEdge, hexposed⟩ := hadj'
              
              have hiT := fillingContainment_exposed_not_mem S T hsub i (by
                                                                           aesop) e hiEdge hexposed
              simp [P, hx, hy, hiT]
            | some j =>
              
              
              
              have hmem := fillingContainment_crossEdge_forces_both_or_neither
                S T hsub i j (by
                                aesop) (by
                                    aesop) ((parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_some_some_iff i j).mp
                                        (by aesop))
              simpa [P, hx, hy] using hmem
        exact hstep.trans ih
  
  
  
  have hstart  := (hboundaryStable walk).mpr  hiT 
  exact (of_eq_true not_false_eq_true) hstart

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
