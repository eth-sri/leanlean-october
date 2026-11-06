/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFaceConnectivity

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

/-- The union of the actual boundary graphs of a finite selected face family. -/
def parafermionicCoverFiniteFaceUnionGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    SimpleGraph (ParafermionicCoverBoxVertex n) where
  Adj v w := ∃ i, i ∈ S ∧
    (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w
  symm := ⟨fun _ _ ⟨i, hi, hadj⟩ => ⟨i, hi, hadj.symm⟩⟩
  loopless := ⟨fun v ⟨i, _, hadj⟩ =>
    (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).loopless.irrefl v hadj⟩

/-- The vertices incident to an actual edge of the selected-face union. -/
def parafermionicCoverFiniteFaceUnionCarrier {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Set (ParafermionicCoverBoxVertex n) :=
  {v | ∃ w, (parafermionicCoverFiniteFaceUnionGraph S).Adj v w}

theorem parafermionicCoverFiniteFaceUnionGraph_le_boxGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    parafermionicCoverFiniteFaceUnionGraph S ≤ parafermionicCoverBoxGraph n :=
  fun _ _ ⟨i, _, hface⟩ => parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph i.1 i.2 hface

def coverUnionFaceVertex0 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨i.1, (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
    (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
      simp [parafermionicCoverFiniteFaceDarts])).1⟩

def coverUnionFaceVertex1 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
      (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
        simp [parafermionicCoverFiniteFaceDarts])).2⟩

def coverUnionFaceVertex2 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).1⟩

def coverUnionFaceVertex3 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLeftLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).2⟩

private theorem coverUnionFace_edge01 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  change s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i) ∈
    {s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i),
     s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i),
     s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i),
     s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i)}
  simp

private theorem coverUnionFace_edge12 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  change s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i) ∈
    {s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i),
     s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i),
     s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i),
     s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i)}
  simp

private theorem coverUnionFace_edge23 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  change s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i) ∈
    {s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i),
     s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i),
     s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i),
     s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i)}
  simp

private theorem coverUnionFace_edge30 {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  change s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i) ∈
    {s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i),
     s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i),
     s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i),
     s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i)}
  simp

def coverUnionFaceCarrier {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    Set (ParafermionicCoverBoxVertex n) :=
  {v | ∃ w, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w}

private theorem coverUnionFaceCarrier_eq_four {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    coverUnionFaceCarrier i =
      {coverUnionFaceVertex0 i, coverUnionFaceVertex1 i,
       coverUnionFaceVertex2 i, coverUnionFaceVertex3 i} := by
  classical
  ext v
  refine ⟨?_, ?_⟩
  · rintro ⟨w, hvw⟩
    have he := (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mpr hvw
    rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet] at he
    rcases he with he | he | he | he <;>
      rcases Sym2.eq_iff.mp he with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl (Subtype.ext rfl)
    · exact Or.inr (Or.inl (Subtype.ext rfl))
    · exact Or.inr (Or.inl (Subtype.ext rfl))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext rfl)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext rfl)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext rfl)))
    · exact Or.inl (Subtype.ext rfl)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨coverUnionFaceVertex1 i, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (coverUnionFace_edge01 i)⟩
    · exact ⟨coverUnionFaceVertex0 i, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (coverUnionFace_edge01 i).symm⟩
    · exact ⟨coverUnionFaceVertex1 i, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (coverUnionFace_edge12 i).symm⟩
    · exact ⟨coverUnionFaceVertex0 i, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (coverUnionFace_edge30 i)⟩

private theorem coverUnionFaceCarrier_subset_unionCarrier {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    {i : ParafermionicCoverFiniteFaceTopIndex n} (hi : i ∈ S) :
    coverUnionFaceCarrier i ⊆ parafermionicCoverFiniteFaceUnionCarrier S :=
  fun _ ⟨w, hvw⟩ => ⟨w, i, hi, hvw⟩

private theorem coverUnionFace_localReach {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    {i : ParafermionicCoverFiniteFaceTopIndex n} (hi : i ∈ S)
    {v w : ParafermionicCoverBoxVertex n}
    (hv : v ∈ coverUnionFaceCarrier i)
    (hw : w ∈ coverUnionFaceCarrier i) :
    ((parafermionicCoverFiniteFaceUnionGraph S).induce
      (parafermionicCoverFiniteFaceUnionCarrier S)).Reachable
      ⟨v, coverUnionFaceCarrier_subset_unionCarrier S hi hv⟩
      ⟨w, coverUnionFaceCarrier_subset_unionCarrier S hi hw⟩ := by
  classical
  let H := (parafermionicCoverFiniteFaceUnionGraph S).induce
    (parafermionicCoverFiniteFaceUnionCarrier S)
  let b0 := coverUnionFaceVertex0 i
  let b1 := coverUnionFaceVertex1 i
  let b2 := coverUnionFaceVertex2 i
  let b3 := coverUnionFaceVertex3 i
  have hb0c := coverUnionFaceCarrier_subset_unionCarrier S hi
    (by rw [coverUnionFaceCarrier_eq_four]; simp [b0] : b0 ∈ coverUnionFaceCarrier i)
  have hb1c := coverUnionFaceCarrier_subset_unionCarrier S hi
    (by rw [coverUnionFaceCarrier_eq_four]; simp [b1] : b1 ∈ coverUnionFaceCarrier i)
  have hb2c := coverUnionFaceCarrier_subset_unionCarrier S hi
    (by rw [coverUnionFaceCarrier_eq_four]; simp [b2] : b2 ∈ coverUnionFaceCarrier i)
  have hb3c := coverUnionFaceCarrier_subset_unionCarrier S hi
    (by rw [coverUnionFaceCarrier_eq_four]; simp [b3] : b3 ∈ coverUnionFaceCarrier i)
  have h01 : H.Adj ⟨b0, hb0c⟩ ⟨b1, hb1c⟩ :=
    ⟨i, hi, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (coverUnionFace_edge01 i)⟩
  have h12 : H.Adj ⟨b1, hb1c⟩ ⟨b2, hb2c⟩ :=
    ⟨i, hi, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (coverUnionFace_edge12 i)⟩
  have h30 : H.Adj ⟨b3, hb3c⟩ ⟨b0, hb0c⟩ :=
    ⟨i, hi, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (coverUnionFace_edge30 i)⟩
  have hreach {u : ParafermionicCoverBoxVertex n} (hu : u ∈ coverUnionFaceCarrier i) :
      H.Reachable ⟨b0, hb0c⟩ ⟨u, coverUnionFaceCarrier_subset_unionCarrier S hi hu⟩ := by
    have h := hu; rw [coverUnionFaceCarrier_eq_four] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact Reachable.refl _
    · exact ⟨Walk.cons h01 Walk.nil⟩
    · exact ⟨Walk.cons h01 (Walk.cons h12 Walk.nil)⟩
    · exact ⟨Walk.cons h30.symm Walk.nil⟩
  exact (hreach hv).symm.trans (hreach hw)

private theorem coverUnionFaceCarriers_shareVertex_of_edge {n : ℕ}
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    {e : Sym2 (ParafermionicCoverBoxVertex n)}
    (hei : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hej : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet) :
    ∃ x, x ∈ coverUnionFaceCarrier i ∧ x ∈ coverUnionFaceCarrier j := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    exact ⟨x, ⟨y, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp hei⟩,
      ⟨y, (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).mem_edgeSet.mp hej⟩⟩

private theorem coverUnionFaceRel_reachable {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    {i j : {f : ParafermionicCoverFiniteFaceTopIndex n // f ∈ S}}
    (hpath : Relation.ReflTransGen
      ((parafermionicCoverFiniteFaceAdjacencyGraph n).induce
        (↑S : Set (ParafermionicCoverFiniteFaceTopIndex n))).Adj i j)
    {v w : ParafermionicCoverBoxVertex n}
    (hv : v ∈ coverUnionFaceCarrier i.1)
    (hw : w ∈ coverUnionFaceCarrier j.1) :
    ((parafermionicCoverFiniteFaceUnionGraph S).induce
      (parafermionicCoverFiniteFaceUnionCarrier S)).Reachable
      ⟨v, coverUnionFaceCarrier_subset_unionCarrier S i.2 hv⟩
      ⟨w, coverUnionFaceCarrier_subset_unionCarrier S j.2 hw⟩ := by
  classical
  revert v w
  induction hpath with
  | refl => exact fun hv hw => coverUnionFace_localReach S i.2 hv hw
  | @tail b c _ hbc ih =>
    intro v w hv hw
    rcases (parafermionicCoverFiniteFaceAdjacencyGraph_adj_iff b.1 c.1).mp (induce_adj.mp hbc) with
      ⟨_, _, hbe, hce⟩
    obtain ⟨x, hxb, hxc⟩ := coverUnionFaceCarriers_shareVertex_of_edge b.1 c.1 hbe hce
    exact (ih hv hxb).trans (coverUnionFace_localReach S c.2 hxc hw)

theorem parafermionicCoverSimpleCycleFaceUnionCarrier_connected
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ((parafermionicCoverFiniteFaceUnionGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).induce
      (parafermionicCoverFiniteFaceUnionCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp))).Connected := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  have hfaces := parafermionicCoverSimpleCycleFillingSet_induce_faceAdjacency_connected hn p hp
  rw [connected_iff_exists_forall_reachable] at hfaces ⊢
  obtain ⟨a, ha⟩ := hfaces
  have hbLocal : coverUnionFaceVertex0 a.1 ∈ coverUnionFaceCarrier a.1 := by
    rw [coverUnionFaceCarrier_eq_four]; simp
  refine ⟨⟨coverUnionFaceVertex0 a.1, coverUnionFaceCarrier_subset_unionCarrier S a.2 hbLocal⟩, ?_⟩
  rintro ⟨z, w, i, hi, hiz⟩
  exact coverUnionFaceRel_reachable S ((reachable_iff_reflTransGen a ⟨i, hi⟩).mp (ha ⟨i, hi⟩))
    hbLocal ⟨w, hiz⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
