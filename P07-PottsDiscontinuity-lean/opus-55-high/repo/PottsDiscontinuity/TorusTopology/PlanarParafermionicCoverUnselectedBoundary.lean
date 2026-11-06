/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceAdjacency
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedFaceIncidence

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable {n : ℕ}
theorem coverFaceSet_exists_dart (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n)
    (hcount : parafermionicCoverFacePositiveDartCount S u v = 1) :
    ∃ i, i ∈ S ∧ (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 := by
  have hpos : 0 < parafermionicCoverFacePositiveDartCount S u v := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

theorem coverFaceSet_not_three_incident (u v : ParafermionicCoverBoxVertex n)
    (i j k : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hj : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hk : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet) : False := by
  let I := parafermionicCoverFiniteFaceIncidentFaces (s(u,v))
  have hiI : i ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hi⟩
  have hjI : j ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hj⟩
  have hkI : k ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hk⟩
  have hsub : ({i,j,k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)) ⊆ I := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl <;> omega
  have hthree : ({i,j,k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)).card = 3 := by
    simp_all
  have hcard := Finset.card_le_card hsub
  have hbound := parafermionicCoverFiniteFaceIncidentFaces_card_le_two (s(u,v))
  dsimp [I] at hcard hbound
  omega
end

section
variable {n : ℕ} (S T : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (hdisjoint : Disjoint S T) (hno_exposed : ∀ i ∈ T, ¬ (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj none (some i)) (hno_cross : ∀ i ∈ T, ∀ j, j ∉ S → j ∉ T → ¬ (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j)
include hdisjoint hno_exposed hno_cross
/-- If a disjoint actual face family has no exposed edge and no shared edge
with the complement of both families, its actual boundary is contained in
the boundary of the selected family. -/
theorem unselectedBoundary_coefficient_ne_zero (u v : ParafermionicCoverBoxVertex n)
    (hp : parafermionicCoverFacePositiveDartCount T u v = 1)
    (hq : parafermionicCoverFacePositiveDartCount T v u = 0) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 := by
  obtain ⟨i, hiT, hidart⟩ := coverFaceSet_exists_dart T u v hp
  have hiEdge :=
    (parafermionicCoverFiniteFaceBoundaryEdge_iff_darts i.1 i.2 u v).2 (Or.inl hidart)
  have hex : ∃ j, j ≠ i ∧ s(u,v) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
    by_contra h
    have hall : ∀ j, j ≠ i → s(u,v) ∉
        (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
      intro j hji hmem
      exact h ⟨j,hji,hmem⟩
    have hadj :=
      (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_none_some_iff i).2
        ⟨s(u,v),hiEdge,hall⟩
    tauto
  obtain ⟨j,hji,hjEdge⟩ := hex
  obtain ⟨a,b,hab_i,hba_j,hmap⟩ :=
    parafermionicCoverFiniteFaceBoundaryDistinctFaces_oppositeDarts i j hji.symm
      (s(u,v)) hiEdge hjEdge
  have hraw : s(u.1,v.1) = s(a,b) := by
    tauto
  have hqj : (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts j.1 := by
    rcases Sym2.eq_iff.mp hraw with hsame | hrev
    · rcases hsame with ⟨rfl,rfl⟩
      omega
    · rcases hrev with ⟨rfl,rfl⟩
      exact (coverFaceDarts_no_opposite hidart hab_i).elim
  have hjnotT : j ∉ T := by
    intro hjT
    have hpos : 0 < parafermionicCoverFacePositiveDartCount T v u := by
      apply Finset.card_pos.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨hjT,hqj⟩⟩
    omega
  have hjS : j ∈ S := by
    by_contra hjS
    exact (hno_cross i hiT j hjS hjnotT) (⟨hji.symm, s(u,v), hiEdge, hjEdge⟩)
  have hPzero : parafermionicCoverFacePositiveDartCount S u v = 0 := by
    by_contra hP
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S u v := by omega
    obtain ⟨k,hk⟩ := Finset.card_pos.mp hpos
    have hkp := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro hki
      subst k
      exact Finset.disjoint_left.mp hdisjoint ((Finset.mem_filter.mp hk).1) hiT
    have hkj : k ≠ j := by
      intro hkj
      subst k
      exact (coverFaceDarts_no_opposite hkp hqj).elim
    exact coverFaceSet_not_three_incident u v i j k hji.symm hki.symm hkj.symm
      hiEdge hjEdge ((parafermionicCoverFiniteFaceBoundaryEdge_iff_darts k.1 k.2 u v).2 (Or.inl hkp))
  have hQone : parafermionicCoverFacePositiveDartCount S v u = 1 := by
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S v u := by
      apply Finset.card_pos.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨hjS,hqj⟩⟩
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
  have hcoeffT :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff T u v).2 hTedge
  let p := parafermionicCoverFacePositiveDartCount T u v
  let q := parafermionicCoverFacePositiveDartCount T v u
  have hp := coverFaceSetPositiveDartCount_le_one T u v
  have hq := coverFaceSetPositiveDartCount_le_one T v u
  have hcases : (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by
    grind [parafermionicCoverFaceBoundaryCoefficient]
  rcases hcases with ⟨hp1,hq0⟩ | ⟨hp0,hq1⟩
  · exact (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff S u v).1
      (unselectedBoundary_coefficient_ne_zero S T hdisjoint hno_exposed hno_cross u v hp1 hq0)
  · have hrev := unselectedBoundary_coefficient_ne_zero S T hdisjoint hno_exposed hno_cross
      v u hq1 hp0
    have hanti := parafermionicCoverFaceBoundaryCoefficient_antisymm S u v
    have hcoeffS : parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 := by
      omega
    exact (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff S u v).1 hcoeffS
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
