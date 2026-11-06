/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceAdjacency
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedFaceIncidence

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial



private theorem coverFaceSetPositiveDartCount_le_one {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFacePositiveDartCount S u v ≤ 1 := Finset.card_le_one.mpr fun i hi j hj =>
                                                           Subtype.ext
                                                             (parafermionicCoverFiniteFaceDart_unique n i.property j.property (Finset.mem_filter.mp hi).right
                                                               (Finset.mem_filter.mp hj).right)

private theorem coverFaceSetDarts_no_opposite {f u v : ParafermionicCoverVertex}
    (huv : (u,v) ∈ parafermionicCoverFiniteFaceDarts f)
    (hvu : (v,u) ∈ parafermionicCoverFiniteFaceDarts f) : False := by
  
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert, parafermionicCoverFaceRightLift_formula, parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula] at huv hvu
  grind

section

variable {n : ℕ}
include n

private theorem coverFaceSet_exists_dart 
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n)
    (hcount : parafermionicCoverFacePositiveDartCount S u v = 1) :
    ∃ i, i ∈ S ∧ (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 := by
  
  have hpos : 0 < parafermionicCoverFacePositiveDartCount S u v := by omega
  unfold parafermionicCoverFacePositiveDartCount at hpos
  grind

private theorem coverFaceSet_not_three_incident 
    (u v : ParafermionicCoverBoxVertex n)
    (i j k : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hj : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hk : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet) : False := by
  
  let I := parafermionicCoverFiniteFaceIncidentFaces  s(u,v) 
  have hiI : i ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hi⟩
  have hjI : j ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hj⟩
  have hkI : k ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hk⟩
  have hsub :  {i,j,k}  ⊆ I := by
    grind
  have hthree : ({i,j,k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)).card = 3 := by
    simp [hij, hik, hjk]
  have hcard := Finset.card_le_card hsub
  have hbound := parafermionicCoverFiniteFaceIncidentFaces_card_le_two  s(u,v) 
  dsimp [I] at hcard hbound
  omega

section

variable (S T : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (hdisjoint : Disjoint S T) (hno_exposed : ∀ i ∈ T,
      ¬ (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj none (some i)) (hno_cross : ∀ i ∈ T, ∀ j,
      j ∉ S → j ∉ T →
      ¬ (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j)
include hdisjoint hno_exposed hno_cross

/-- If a disjoint actual face family has no exposed edge and no shared edge
with the complement of both families, its actual boundary is contained in
the boundary of the selected family. -/
private theorem unselectedBoundary_coefficient_ne_zero 
    
    (u v : ParafermionicCoverBoxVertex n)
    (hp : parafermionicCoverFacePositiveDartCount T u v = 1)
    (hq : parafermionicCoverFacePositiveDartCount T v u = 0) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 := by
  classical
  have hST  := hdisjoint
  obtain ⟨i, hiT, hidart⟩ := coverFaceSet_exists_dart T u v hp
  have hiEdge  :=
    (parafermionicCoverFiniteFaceBoundaryEdge_iff_darts i.1 i.2 u v).2 (Or.inl hidart)
  have hex : ∃ j, j ≠ i ∧ s(u,v) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := Decidable.byContradiction fun h =>
                                                                       hno_exposed i hiT
                                                                         ((parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_none_some_iff i).mpr
                                                                           (Exists.intro s(u, v) ⟨hiEdge, fun j hji hmem => h (Exists.intro j ⟨hji, hmem⟩)⟩))
  obtain ⟨j,hji,hjEdge⟩ := hex
  obtain ⟨a,b,hab_i,hba_j,hmap⟩ :=
    parafermionicCoverFiniteFaceBoundaryDistinctFaces_oppositeDarts i j hji.symm
       s(u,v)  hiEdge hjEdge
  
  have hqj : (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts j.1 := by
    rcases Sym2.eq_iff.mp (by
                             simpa  using hmap) with hsame | hrev
    · simp_all
    · rcases hrev with ⟨rfl,rfl⟩
      exact (coverFaceSetDarts_no_opposite hidart hab_i).elim
  
  
  have hPzero : parafermionicCoverFacePositiveDartCount S u v = 0 := by
    by_contra hP
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S u v := by omega
    
    obtain ⟨k,hk⟩ := Finset.card_pos.mp hpos
    have hkS := (Finset.mem_filter.mp hk).1
    have hkp := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro hki
      subst k
      exact Finset.disjoint_left.mp hST hkS hiT
    have hkj : k ≠ j := by
      intro hkj
      subst k
      exact (coverFaceSetDarts_no_opposite hkp hqj).elim
    
    exact coverFaceSet_not_three_incident u v i j k hji.symm hki.symm hkj.symm
      hiEdge hjEdge ((parafermionicCoverFiniteFaceBoundaryEdge_iff_darts k.1 k.2 u v).2 (Or.inl hkp))
  have hQone : parafermionicCoverFacePositiveDartCount S v u = 1 := by
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S v u := Finset.card_pos.mpr (Exists.intro j (Finset.mem_filter.mpr ⟨ by
                                                                                                                                                        exact Decidable.byContradiction fun hjS => hno_cross i hiT j hjS (by
                                                                                                                                                                                                                            intro hjT
                                                                                                                                                                                                                            have hpos : 0 < parafermionicCoverFacePositiveDartCount T v u := Finset.card_pos.mpr (Exists.intro j (Finset.mem_filter.mpr ⟨hjT, hqj⟩))
                                                                                                                                                                                                                            all_goals omega) ⟨Ne.symm hji, Exists.intro s(u, v) ⟨hiEdge, hjEdge⟩⟩ , hqj⟩))
    have hle := coverFaceSetPositiveDartCount_le_one S v u
    omega
  unfold parafermionicCoverFaceBoundaryCoefficient
  rw [hPzero,hQone]
  norm_num

theorem parafermionicCoverFiniteFaceUnselectedBoundary_le_selectedBoundary
      :
    parafermionicCoverFiniteFaceSetBoundaryGraph T ≤
      parafermionicCoverFiniteFaceSetBoundaryGraph S := by
  
  intro u v hTedge
  have hcoeffT  :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff T u v).2 hTedge
  let p := parafermionicCoverFacePositiveDartCount T u v
  let q := parafermionicCoverFacePositiveDartCount T v u
  have hp  := coverFaceSetPositiveDartCount_le_one T u v
  have hq  := coverFaceSetPositiveDartCount_le_one T v u
  have hcases :  p = 1 ∧ q = 0  ∨  p = 0 ∧ q = 1  := by
    grind [parafermionicCoverFaceBoundaryCoefficient]
  rcases hcases with ⟨hp1,hq0⟩ | ⟨hp0,hq1⟩
  · exact (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff S u v).1
      (unselectedBoundary_coefficient_ne_zero S T hdisjoint hno_exposed hno_cross u v hp1 hq0)
  · have hrev := unselectedBoundary_coefficient_ne_zero S T hdisjoint hno_exposed hno_cross
      v u hq1 hp0
    have hanti := parafermionicCoverFaceBoundaryCoefficient_antisymm S u v
    
    exact (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff S u v).1 (by
                                                                                            omega)

end

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
