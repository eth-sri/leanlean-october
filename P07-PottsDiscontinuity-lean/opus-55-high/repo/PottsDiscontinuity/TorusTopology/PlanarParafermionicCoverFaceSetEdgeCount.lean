/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedFaceIncidence
public import Mathlib.Tactic

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def faceGraphEdges {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ G.edgeSet

section
variable {n : ℕ}
theorem coverFaceBoundary_edgeFinset_card_four (i : ParafermionicCoverFiniteFaceTopIndex n) :
    (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).card = 4 := by
  classical
  let f := i.1
  have hbox :=
    (Finset.mem_filter.mp i.2).1
  obtain ⟨q, hcycle, hlength, hsupp⟩ :=
    parafermionicCoverFiniteOrdinaryFace_has_cycle n f hbox i.2
  let b0 : ParafermionicCoverBoxVertex n := ⟨f, by
    omega⟩
  let b1 : ParafermionicCoverBoxVertex n := ⟨
    parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2, by
      exact (parafermionicCoverFiniteFaceDart_endpoints_mem n f i.2
        (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
        (by simp [parafermionicCoverFiniteFaceDarts])).2⟩
  let b2 : ParafermionicCoverBoxVertex n := ⟨
    parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2, by
      exact (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f i.2).1⟩
  let b3 : ParafermionicCoverBoxVertex n := ⟨
    parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, by
      exact (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f i.2).2⟩
  have hsupp' : q.support = [b0,b1,b2,b3,b0] := by
    apply Function.Injective.list_map Subtype.val_injective
    tauto
  have hqedges : q.edges = [s(b0,b1),s(b1,b2),s(b2,b3),s(b3,b0)] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hsupp']
    rfl
  have hqcard : q.edges.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hcycle.isTrail.edges_nodup,
      q.length_edges, hlength]
  have hqset : q.edgeSet =
      (parafermionicCoverFiniteFaceBoundaryGraph f i.2).edgeSet := by
    rw [SimpleGraph.Walk.edgeSet, hqedges,
      parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
    ext e
    change (e ∈ [s(b0,b1),s(b1,b2),s(b2,b3),s(b3,b0)]) ↔
      e ∈ ({s(b0,b1),s(b1,b2),s(b2,b3),s(b3,b0)} : Set _)
    simp
  have hfinset : q.edges.toFinset =
      faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph f i.2) := by
    ext e
    simp only [List.mem_toFinset, faceGraphEdges, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change e ∈ q.edgeSet ↔
      e ∈ (parafermionicCoverFiniteFaceBoundaryGraph f i.2).edgeSet
    simp_all
  rwa [← hfinset]


def parafermionicCoverFiniteFaceSetEdgeSupport (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Finset (Sym2 (ParafermionicCoverBoxVertex n)) := by
  classical
  exact Finset.univ.filter fun e =>
    (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).Nonempty

def parafermionicCoverFiniteFaceSetBoundaryEdges (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Finset (Sym2 (ParafermionicCoverBoxVertex n)) :=
  faceGraphEdges (parafermionicCoverFiniteFaceSetBoundaryGraph S)

def faceIncidencePairsByFace (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Finset (ParafermionicCoverFiniteFaceTopIndex n ×
      Sym2 (ParafermionicCoverBoxVertex n)) := by
  classical
  exact S.biUnion fun i =>
    (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).image
      fun e => (i,e)
end

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
def faceIncidencePairsByEdge  :
    Finset (ParafermionicCoverFiniteFaceTopIndex n ×
      Sym2 (ParafermionicCoverBoxVertex n)) := by
  classical
  exact (parafermionicCoverFiniteFaceSetEdgeSupport S).biUnion fun e =>
    (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).image
      fun i => (i,e)

theorem faceIncidencePairsByFace_card  :
    (faceIncidencePairsByFace S).card =
      ∑ i ∈ S,
        (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).card := by
  classical
  let T := fun i : ParafermionicCoverFiniteFaceTopIndex n =>
    (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).image
      fun e => (i,e)
  have hdisj : (S : Set (ParafermionicCoverFiniteFaceTopIndex n)).PairwiseDisjoint T := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    grind
  rw [faceIncidencePairsByFace, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.card_image_of_injective _ (fun e e' h => congrArg Prod.snd h)

theorem faceIncidencePairsByEdge_card  :
    (faceIncidencePairsByEdge S).card =
      ∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
        (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card := by
  classical
  let T := fun e : Sym2 (ParafermionicCoverBoxVertex n) =>
    (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).image fun i => (i,e)
  have hdisj :
      (parafermionicCoverFiniteFaceSetEdgeSupport S :
        Set (Sym2 (ParafermionicCoverBoxVertex n))).PairwiseDisjoint T := by
    intro e he e' he' hee'
    apply Finset.disjoint_left.mpr
    grind
  rw [faceIncidencePairsByEdge, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro e he
  exact Finset.card_image_of_injective _ (fun i i' h => congrArg Prod.fst h)

theorem faceIncidencePairs_eq  :
    faceIncidencePairsByFace S = faceIncidencePairsByEdge S := by
  classical
  ext z
  rcases z with ⟨i,e⟩
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨j,hj,himg⟩
    rcases Finset.mem_image.mp himg with ⟨e',he',heq⟩
    have hij : j = i := by grind
    have heq' : e' = e := by grind
    subst j
    subst e'
    have hiInc : i ∈ parafermionicCoverFiniteFaceIncidentFaces e :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he').2⟩
    have hiSel :=
      Finset.mem_filter.mpr ⟨hiInc,hj⟩
    exact Finset.mem_biUnion.mpr
      ⟨e,(Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i,hiSel⟩⟩),Finset.mem_image.mpr ⟨i,hiSel,rfl⟩⟩
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨e',he,himg⟩
    rcases Finset.mem_image.mp himg with ⟨j,hj,heq⟩
    have hij : j = i := by grind
    have heq' : e' = e := by grind
    subst j
    subst e'
    have hmem := Finset.mem_filter.mp hj
    exact Finset.mem_biUnion.mpr
      ⟨i,hmem.2,Finset.mem_image.mpr ⟨e,(Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hmem.1).2)⟩),rfl⟩⟩


theorem faceSet_edgeSupport_boundary_subset  :
    parafermionicCoverFiniteFaceSetBoundaryEdges S ⊆
      parafermionicCoverFiniteFaceSetEdgeSupport S := by
  classical
  intro e he
  have hone :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
      S e).1 ((Finset.mem_filter.mp he).2)
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, Finset.card_pos.mp (by omega)⟩

theorem faceSet_faceIncidence_count  :
    (faceIncidencePairsByFace S).card = 4 * S.card := by
  classical
  rw [faceIncidencePairsByFace_card]
  calc
    (∑ i ∈ S,
        (faceGraphEdges (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)).card) =
        ∑ i ∈ S, (4 : ℕ) := by
          simp [coverFaceBoundary_edgeFinset_card_four]
    _ = 4 * S.card := by simp [mul_comm]

theorem faceSet_boundary_indicator_sum  :
    (∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
      if e ∈ parafermionicCoverFiniteFaceSetBoundaryEdges S then 1 else 0) =
      (parafermionicCoverFiniteFaceSetBoundaryEdges S).card := by
  classical
  rw [Finset.sum_ite]
  simp [faceSet_edgeSupport_boundary_subset]

theorem faceSet_local_incidence_equation  :
    (∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
      ((parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card +
        (if e ∈ parafermionicCoverFiniteFaceSetBoundaryEdges S then 1 else 0))) =
      2 * (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
  classical
  have hterm : ∀ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
      (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card +
        (if e ∈ parafermionicCoverFiniteFaceSetBoundaryEdges S then 1 else 0) = 2 := by
    intro e he
    have hpos :=
      Finset.card_pos.mpr (Finset.mem_filter.mp he).2
    by_cases hb : e ∈ parafermionicCoverFiniteFaceSetBoundaryEdges S
    · have hone :=
        (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
          S e).1 ((Finset.mem_filter.mp hb).2)
      simp_all
    · have hle := parafermionicCoverFiniteFaceSelectedIncidentFaces_card_le_two S e
      have hnotone : (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card ≠ 1 := by
        intro hone
        have hedge :=
          (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
            S e).2 hone
        exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge⟩)
      grind
  calc
    _ = ∑ _e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S, (2 : ℕ) := by
      apply Finset.sum_congr rfl
      omega
    _ = 2 * (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by simp [mul_comm]

/-- Counting the four actual boundary edges of every selected face counts an
interior edge twice and a selected-set boundary edge once. -/
theorem parafermionicCoverFiniteFaceSetEdgeCount  :
    4 * S.card + (parafermionicCoverFiniteFaceSetBoundaryEdges S).card =
      2 * (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
  classical
  have hpairs := faceIncidencePairs_eq S
  have hface := faceSet_faceIncidence_count S
  have hedge := faceIncidencePairsByEdge_card S
  have hedge' : (faceIncidencePairsByFace S).card =
      ∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
        (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card := by
    simp_all
  have hlocal := faceSet_local_incidence_equation S
  have hsum :
      (∑ e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S,
        (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card) = 4 * S.card := by
    omega
  rw [Finset.sum_add_distrib, hsum, (faceSet_boundary_indicator_sum S)] at hlocal
  exact hlocal
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
