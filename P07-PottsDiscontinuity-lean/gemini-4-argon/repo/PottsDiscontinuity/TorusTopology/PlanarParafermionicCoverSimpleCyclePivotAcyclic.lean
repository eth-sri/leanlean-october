module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenSubgraphOfCycle
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetPivotRemoval
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionCarrierTransport
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFaceIndecomposable

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

private theorem selectedIncident_mem {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (e : Sym2 (ParafermionicCoverBoxVertex n))
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces S e ↔
      i ∈ S ∧ e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  classical
  simp [parafermionicCoverFiniteFaceSelectedIncidentFaces,
    parafermionicCoverFiniteFaceIncidentFaces, and_comm]

private theorem no_three_incident {n : ℕ}
    (e : Sym2 (ParafermionicCoverBoxVertex n))
    (i j k : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hj : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hk : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet) : False := by
  classical
  have hsub : ({i, j, k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)) ⊆
      parafermionicCoverFiniteFaceIncidentFaces e := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl <;> assumption
  have hthree : ({i, j, k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)).card = 3 := by
    simp [hij, hik, hjk]
  have hcard := Finset.card_le_card hsub
  have hbound := parafermionicCoverFiniteFaceIncidentFaces_card_le_two e
  omega

private theorem exists_boundary_pivot {n : ℕ}
    (T : Finset (ParafermionicCoverFiniteFaceTopIndex n)) (hT : T.Nonempty) :
    ∃ i ∈ T, parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet := by
  classical
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image T
    (parafermionicCoverFiniteFaceTopRank n) ⟨i0, hi0⟩
  refine ⟨i, hi, (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one T _).2 ?_⟩
  let e := parafermionicCoverFiniteFaceTopPivot n i
  have hiEdge : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
    simpa [e, parafermionicCoverFiniteFaceTopPivot, parafermionicCoverFiniteFaceTopEdgeBox] using
      parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph i.1 i.2
  have hsel : i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces T e :=
    (selectedIncident_mem T e i).2 ⟨hi, hiEdge⟩
  have hsub : parafermionicCoverFiniteFaceSelectedIncidentFaces T e ⊆ {i} := by
    intro j hj
    obtain ⟨hjT, hjEdge⟩ := (selectedIncident_mem T e j).1 hj
    rcases parafermionicCoverFiniteFacePivot_boundary_classification j i hjEdge with heq | hlt
    · simp [heq.symm]
    · exact (not_lt_of_ge (hmax j hjT) hlt).elim
  have hle := Finset.card_le_card hsub
  have hpos := Finset.card_pos.2 ⟨i, hsel⟩
  simp only [Finset.card_singleton] at hle
  dsimp [e] at hle hpos
  omega

private theorem contains_boundary_supported_faces
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hsub : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport
        (parafermionicCoverSimpleCycleFillingSet hn p hp) :
          Set (Sym2 (ParafermionicCoverBoxVertex n)))) :
    T ⊆ parafermionicCoverSimpleCycleFillingSet hn p hp := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  intro i₀ hi₀T
  by_contra hi₀S
  let U := T \ S
  have hi₀U : i₀ ∈ U := Finset.mem_sdiff.2 ⟨hi₀T, hi₀S⟩
  have hboundaryS : parafermionicCoverFiniteFaceSetBoundaryGraph S = p.toSubgraph.spanningCoe :=
    parafermionicCoverSimpleCycleFillingSet_boundary_eq hn p hp
  have hU_le_S : parafermionicCoverFiniteFaceSetBoundaryGraph U ≤
      parafermionicCoverFiniteFaceSetBoundaryGraph S := by
    intro a b hab
    let e := s(a, b)
    have heU : e ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph U).edgeSet := hab
    have hcardU := (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one U e).1 heU
    obtain ⟨j, hj_sel⟩ := Finset.card_pos.1 (by omega : 0 < (parafermionicCoverFiniteFaceSelectedIncidentFaces U e).card)
    obtain ⟨hjU, hjEdge⟩ := (selectedIncident_mem U e j).1 hj_sel
    obtain ⟨hjT, hjS⟩ := Finset.mem_sdiff.1 hjU
    have hexS : ∃ k ∈ S, e ∈ (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet := by
      by_cases heT : e ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet
      · obtain ⟨_, k, hk_sel⟩ := Finset.mem_filter.1 (hsub heT)
        obtain ⟨hkS, hkEdge⟩ := (selectedIncident_mem S e k).1 hk_sel
        exact ⟨k, hkS, hkEdge⟩
      · have hcardT_ne : (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card ≠ 1 :=
          fun h1 => heT ((parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one T e).2 h1)
        have hj_selT : j ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces T e :=
          (selectedIncident_mem T e j).2 ⟨hjT, hjEdge⟩
        have hposT : 0 < (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card :=
          Finset.card_pos.2 ⟨j, hj_selT⟩
        obtain ⟨k, hk_selT, hkj⟩ :=
          Finset.exists_mem_ne (s := parafermionicCoverFiniteFaceSelectedIncidentFaces T e) (by omega) j
        obtain ⟨hkT, hkEdge⟩ := (selectedIncident_mem T e k).1 hk_selT
        have hkS : k ∈ S := by
          by_contra hkNotS
          have hk_selU : k ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces U e :=
            (selectedIncident_mem U e k).2 ⟨Finset.mem_sdiff.2 ⟨hkT, hkNotS⟩, hkEdge⟩
          exact hkj (Finset.card_le_one.1 hcardU.le k hk_selU j hj_sel)
        exact ⟨k, hkS, hkEdge⟩
    obtain ⟨k, hkS, hkEdge⟩ := hexS
    have hkj : j ≠ k := fun heq => hjS (heq ▸ hkS)
    have hcardS : (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).card = 1 := by
      have hk_selS : k ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces S e :=
        (selectedIncident_mem S e k).2 ⟨hkS, hkEdge⟩
      have hsubS : parafermionicCoverFiniteFaceSelectedIncidentFaces S e ⊆ {k} := by
        intro m hm
        obtain ⟨hmS, hmEdge⟩ := (selectedIncident_mem S e m).1 hm
        have hmk : m = k := by
          by_contra hne
          have hjm : j ≠ m := fun heq => hjS (heq ▸ hmS)
          exact no_three_incident e j k m hkj hjm (Ne.symm hne) hjEdge hkEdge hmEdge
        simp [hmk]
      have hle := Finset.card_le_card hsubS
      have hpos := Finset.card_pos.2 ⟨k, hk_selS⟩
      simp only [Finset.card_singleton] at hle
      omega
    exact (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one S e).2 hcardS
  have heven := parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree U
  have hcyclecase := evenSubgraphOfCycle_eq_bot_or_cycle p hp
    (parafermionicCoverFiniteFaceSetBoundaryGraph U) (hboundaryS ▸ hU_le_S) heven
  have hUne : parafermionicCoverFiniteFaceSetBoundaryGraph U ≠ ⊥ :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff U).2 ⟨i₀, hi₀U⟩
  rcases hcyclecase with hbot | hwhole
  · exact hUne hbot
  · have hUS : parafermionicCoverFiniteFaceSetBoundaryGraph U =
        parafermionicCoverFiniteFaceSetBoundaryGraph S := hwhole.trans hboundaryS.symm
    have hlists := parafermionicCoverFiniteFaceChain_toFinset_unique
      U.toList S.toList U.nodup_toList S.nodup_toList (by
        simpa [parafermionicCoverFiniteFaceSetBoundaryGraph] using hUS)
    have hEq : U = S := by simpa only [Finset.toList_toFinset] using hlists
    exact hi₀S (by simpa [S, ← hEq] using hi₀U)

/-- The graph formed by a named actual simple-cycle filling is acyclic after
deleting precisely that filling's actual top pivots. -/
theorem parafermionicCoverSimpleCyclePivotAcyclic
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (parafermionicCoverFiniteFaceSetWithoutPivotsGraph
      (parafermionicCoverSimpleCycleFillingSet hn p hp)).IsAcyclic := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let R := parafermionicCoverFiniteFaceSetWithoutPivotsGraph S
  let U := parafermionicCoverFiniteFaceUnionGraph S
  have hRleU : R ≤ U := SimpleGraph.deleteEdges_le _
  have hRleBox : R ≤ parafermionicCoverBoxGraph n :=
    le_trans hRleU (parafermionicCoverFiniteFaceUnionGraph_le_boxGraph S)
  intro v q hq
  let qbox := q.mapLe hRleBox
  have hqbox : qbox.IsCycle := hq.mapLe hRleBox
  let T := parafermionicCoverSimpleCycleFillingSet hn qbox hqbox
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hn qbox hqbox
  have hTne : T.Nonempty := by simpa [T] using hspec.2.1
  have hsupport : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport S : Set
        (Sym2 (ParafermionicCoverBoxVertex n))) := by
    intro e he
    rw [parafermionicCoverSimpleCycleFillingSet_boundary_eq hn qbox hqbox,
      SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph] at he
    have heq : e ∈ q.edges := by simpa [qbox] using he
    have hRedge : e ∈ R.edgeSet := q.edges_subset_edgeSet heq
    exact (parafermionicCoverFiniteFaceUnionGraph_edgeSet_eq_support S).le
      (SimpleGraph.edgeSet_mono hRleU hRedge)
  have hTS : T ⊆ S := contains_boundary_supported_faces hn p hp T hsupport
  obtain ⟨i, hiT, hipivot⟩ := exists_boundary_pivot T hTne
  have hipivotP : parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetPivots S : Set
        (Sym2 (ParafermionicCoverBoxVertex n))) :=
    Finset.mem_image.mpr ⟨i, hTS hiT, rfl⟩
  rw [parafermionicCoverSimpleCycleFillingSet_boundary_eq hn qbox hqbox,
    SimpleGraph.Subgraph.edgeSet_spanningCoe,
    SimpleGraph.Walk.edgeSet_toSubgraph] at hipivot
  have hipivotR : parafermionicCoverFiniteFaceTopPivot n i ∈ R.edgeSet :=
    q.edges_subset_edgeSet (by simpa [qbox] using hipivot)
  change parafermionicCoverFiniteFaceTopPivot n i ∈
    (U.deleteEdges (parafermionicCoverFiniteFaceSetPivots S : Set _)).edgeSet at hipivotR
  rw [SimpleGraph.edgeSet_deleteEdges] at hipivotR
  exact hipivotR.2 hipivotP

end PottsDiscontinuity.TorusTopology.Planar.Medial
