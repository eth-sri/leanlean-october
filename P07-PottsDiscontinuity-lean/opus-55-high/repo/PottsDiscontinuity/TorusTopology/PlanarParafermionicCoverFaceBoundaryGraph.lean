/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace/import relocation; the face cycle is chosen from unique existence, fixed by its complete ordered vertex list. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaceCycles
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopEdges
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable (n : ℕ) (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
include hf
theorem coverFace_box_mem  :
    f ∈ parafermionicCoverBoxFinset n :=
  (Finset.mem_filter.mp hf).1

 theorem coverFace_base_mem  :
    f ∈ parafermionicCoverBoxVertices n := by
  have h := parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
    (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])
  simp_all
end

 section
variable {n : ℕ} (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
include hf
theorem existsUniqueFaceActualCycle  :
    ∃! w : (parafermionicCoverBoxGraph n).Walk ⟨f, coverFace_base_mem n f hf⟩
        ⟨f, coverFace_base_mem n f hf⟩,
      w.IsCycle ∧ w.length = 4 ∧ w.support.map Subtype.val =
        [f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f] := by
  obtain ⟨w,hw⟩ := parafermionicCoverFiniteOrdinaryFace_has_cycle n f
    (coverFace_box_mem n f hf) hf
  refine ⟨w,hw,?_⟩
  intro q hq
  apply SimpleGraph.Walk.ext_support
  apply Function.Injective.list_map Subtype.val_injective
  simp_all

 def coverFaceActualCycle  :
    (parafermionicCoverBoxGraph n).Walk ⟨f, coverFace_base_mem n f hf⟩
      ⟨f, coverFace_base_mem n f hf⟩ :=
  Classical.choose (existsUniqueFaceActualCycle f hf).exists

theorem coverFaceActualCycle_spec  :
    (coverFaceActualCycle f hf).IsCycle ∧
      (coverFaceActualCycle f hf).length = 4 ∧
      (coverFaceActualCycle f hf).support.map Subtype.val =
        [f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
          parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f] :=
  by simpa only [coverFaceActualCycle] using Classical.choose_spec (existsUniqueFaceActualCycle f hf).exists
end

 def coverFaceB0 {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) : ParafermionicCoverBoxVertex n :=
  ⟨f, coverFace_base_mem n f hf⟩

 section
variable {n : ℕ} (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
def coverFaceB1  : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
    (parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
      (e := (f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
      (by simp [parafermionicCoverFiniteFaceDarts])).2⟩

 def coverFaceB2  : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩

 def coverFaceB3  : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩

@[irreducible] def parafermionicCoverFiniteFaceBoundaryGraph  :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  (coverFaceActualCycle f hf).toSubgraph.spanningCoe

theorem parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph  :
    parafermionicCoverFiniteFaceBoundaryGraph f hf ≤ parafermionicCoverBoxGraph n :=
  by
    unfold parafermionicCoverFiniteFaceBoundaryGraph
    exact (coverFaceActualCycle f hf).toSubgraph.spanningCoe_le

theorem parafermionicCoverFiniteFaceBoundaryGraph_edgeSet  :
    (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet =
      {s(coverFaceB0 f hf, coverFaceB1 f hf),
       s(coverFaceB1 f hf, coverFaceB2 f hf),
       s(coverFaceB2 f hf, coverFaceB3 f hf),
       s(coverFaceB3 f hf, coverFaceB0 f hf)} := by
  have hsup := coverFaceActualCycle_spec f hf
  have hs : (coverFaceActualCycle f hf).support =
      [coverFaceB0 f hf, coverFaceB1 f hf, coverFaceB2 f hf, coverFaceB3 f hf, coverFaceB0 f hf] := by
    apply Function.Injective.list_map Subtype.val_injective
    tauto
  rw [parafermionicCoverFiniteFaceBoundaryGraph, SimpleGraph.Subgraph.edgeSet_spanningCoe,
    SimpleGraph.Walk.edgeSet_toSubgraph]
  change (fun e => e ∈ (coverFaceActualCycle f hf).edges) = _
  rw [SimpleGraph.Walk.edges_eq_zipWith_support, hs]
  ext e
  change e ∈ [s(coverFaceB0 f hf, coverFaceB1 f hf),
      s(coverFaceB1 f hf, coverFaceB2 f hf),
      s(coverFaceB2 f hf, coverFaceB3 f hf),
      s(coverFaceB3 f hf, coverFaceB0 f hf)] ↔
    e ∈ ({s(coverFaceB0 f hf, coverFaceB1 f hf),
      s(coverFaceB1 f hf, coverFaceB2 f hf),
      s(coverFaceB2 f hf, coverFaceB3 f hf),
      s(coverFaceB3 f hf, coverFaceB0 f hf)} : Set (Sym2 (ParafermionicCoverBoxVertex n)))
  simp

theorem parafermionicCoverFiniteFaceBoundaryGraph_actualEdgeSet  :
    Sym2.map Subtype.val '' (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet =
      {parafermionicCoverFiniteFaceBottomEdge f,
       parafermionicCoverFiniteFaceRightEdge f,
       parafermionicCoverFiniteFaceTopEdge f,
       parafermionicCoverFiniteFaceLeftEdge f} := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  aesop

def parafermionicCoverFiniteFaceTopEdgeBox  :
    Sym2 (ParafermionicCoverBoxVertex n) :=
  s(⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩,
    ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
      (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩)

theorem parafermionicCoverFiniteFaceTopEdgeBox_mem_boundaryGraph  :
    parafermionicCoverFiniteFaceTopEdgeBox f hf ∈
      (parafermionicCoverFiniteFaceBoundaryGraph f hf).edgeSet := by
  simp [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet, parafermionicCoverFiniteFaceTopEdgeBox, coverFaceB2, coverFaceB3]


@[irreducible] def parafermionicCoverFiniteFaceBoundaryDegree (v : ParafermionicCoverBoxVertex n) : ℕ :=
  (parafermionicCoverFiniteFaceBoundaryGraph f hf).neighborSet v |>.ncard
end

theorem eulerian_even_neighbor_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u : V} (q : G.Walk u u)
    (hq : q.IsEulerian) (v : V) : Even (G.neighborSet v).ncard := by
  have hdegree : Even (G.degree v) :=
    (hq.even_degree_iff).2 (by simp)
  rw [← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] at hdegree
  exact hdegree

theorem parafermionicCoverFiniteFaceBoundaryGraph_even_degree {n : ℕ} (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even (parafermionicCoverFiniteFaceBoundaryDegree f hf v) := by
  classical
  intro v
  unfold parafermionicCoverFiniteFaceBoundaryDegree
  let H := parafermionicCoverFiniteFaceBoundaryGraph f hf
  let w := coverFaceActualCycle f hf
  have hH : H = w.toSubgraph.spanningCoe := by
    change parafermionicCoverFiniteFaceBoundaryGraph f hf =
      (coverFaceActualCycle f hf).toSubgraph.spanningCoe
    unfold parafermionicCoverFiniteFaceBoundaryGraph
    rfl
  let q := w.transfer H (by
    simp_all)
  have hqtrail : q.IsTrail := by
    simpa [q] using (coverFaceActualCycle_spec f hf).1.isTrail
  have hqedges : q.edgeSet = H.edgeSet := by
    change (w.transfer H _).edgeSet = H.edgeSet
    simp_all
  exact eulerian_even_neighbor_ncard H q (hqtrail.isEulerian_iff.mpr hqedges) v

end PottsDiscontinuity.TorusTopology.Planar.Medial
