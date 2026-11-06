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

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
/-- The union of the actual boundary graphs of a finite selected face family. -/
def parafermionicCoverFiniteFaceUnionGraph  :
    SimpleGraph (ParafermionicCoverBoxVertex n) where
  Adj v w := ∃ i, i ∈ S ∧
    (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w
  symm := by
    constructor
    tauto
  loopless := by
    constructor
    grind

/-- The vertices incident to an actual edge of the selected-face union. -/
def parafermionicCoverFiniteFaceUnionCarrier  :
    Set (ParafermionicCoverBoxVertex n) :=
  {v | ∃ w, (parafermionicCoverFiniteFaceUnionGraph S).Adj v w}

theorem parafermionicCoverFiniteFaceUnionGraph_le_boxGraph  :
    parafermionicCoverFiniteFaceUnionGraph S ≤ parafermionicCoverBoxGraph n := by
  intro v w hadj
  rcases hadj with ⟨i, hi, hface⟩
  exact parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph i.1 i.2 hface
end

section
variable {n : ℕ}
def coverUnionFaceVertex0 (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨i.1, (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
    (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
      simp [parafermionicCoverFiniteFaceDarts])).1⟩

def coverUnionFaceVertex1 (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
      (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
        simp [parafermionicCoverFiniteFaceDarts])).2⟩

def coverUnionFaceVertex2 (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).1⟩

def coverUnionFaceVertex3 (i : ParafermionicCoverFiniteFaceTopIndex n) : ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLeftLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).2⟩
end

section
variable {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n)
theorem coverUnionFace_edge01  :
    s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  tauto

theorem coverUnionFace_edge12  :
    s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  tauto


theorem coverUnionFace_edge30  :
    s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  tauto
end

section
variable {n : ℕ}
def coverUnionFaceCarrier (i : ParafermionicCoverFiniteFaceTopIndex n) :
    Set (ParafermionicCoverBoxVertex n) :=
  {v | ∃ w, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w}

theorem coverUnionFaceCarrier_eq_four (i : ParafermionicCoverFiniteFaceTopIndex n) :
    coverUnionFaceCarrier i =
      {coverUnionFaceVertex0 i, coverUnionFaceVertex1 i,
       coverUnionFaceVertex2 i, coverUnionFaceVertex3 i} := by
  ext v
  constructor
  · rintro ⟨w, hvw⟩
    have he : s(v,w) ∈
        (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet :=
      by simp_all
    rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet] at he
    rcases he with he | he | he | he
    · rcases Sym2.eq_iff.mp he with ⟨hv, _⟩ | ⟨hv, _⟩
      · tauto
      tauto
    · rcases Sym2.eq_iff.mp he with ⟨hv, _⟩ | ⟨hv, _⟩
      · tauto
      tauto
    · rcases Sym2.eq_iff.mp he with ⟨hv, _⟩ | ⟨hv, _⟩
      · tauto
      tauto
    · rcases Sym2.eq_iff.mp he with ⟨hv, _⟩ | ⟨hv, _⟩
      · tauto
      tauto
  · intro hv
    rcases hv with hv | hv | hv | hv
    · subst v
      refine ⟨coverUnionFaceVertex1 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        (coverUnionFace_edge01 i)
    · subst v
      refine ⟨coverUnionFaceVertex0 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        ((coverUnionFace_edge01 i).symm)
    · subst v
      refine ⟨coverUnionFaceVertex1 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        ((coverUnionFace_edge12 i).symm)
    · subst v
      refine ⟨coverUnionFaceVertex0 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        (coverUnionFace_edge30 i)
end

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) {i : ParafermionicCoverFiniteFaceTopIndex n} (hi : i ∈ S)
include hi
theorem coverUnionFaceCarrier_subset_unionCarrier  :
    coverUnionFaceCarrier i ⊆ parafermionicCoverFiniteFaceUnionCarrier S := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  exact ⟨w, i, hi, hvw⟩

theorem coverUnionFace_localReach {v w : ParafermionicCoverBoxVertex n}
    (hv : v ∈ coverUnionFaceCarrier i)
    (hw : w ∈ coverUnionFaceCarrier i) :
    ((parafermionicCoverFiniteFaceUnionGraph S).induce
      (parafermionicCoverFiniteFaceUnionCarrier S)).Reachable
      ⟨v, coverUnionFaceCarrier_subset_unionCarrier S hi hv⟩
      ⟨w, coverUnionFaceCarrier_subset_unionCarrier S hi hw⟩ := by
  let H := (parafermionicCoverFiniteFaceUnionGraph S).induce
    (parafermionicCoverFiniteFaceUnionCarrier S)
  let b0 := coverUnionFaceVertex0 i
  let b1 := coverUnionFaceVertex1 i
  let b2 := coverUnionFaceVertex2 i
  let b3 := coverUnionFaceVertex3 i
  have hb0 : b0 ∈ coverUnionFaceCarrier i := by
    rw [coverUnionFaceCarrier_eq_four]
    tauto
  have hb1 : b1 ∈ coverUnionFaceCarrier i := by
    rw [coverUnionFaceCarrier_eq_four]
    tauto
  have hb2 : b2 ∈ coverUnionFaceCarrier i := by
    rw [coverUnionFaceCarrier_eq_four]
    tauto
  have hb3 : b3 ∈ coverUnionFaceCarrier i := by
    rw [coverUnionFaceCarrier_eq_four]
    tauto
  have hb0c := coverUnionFaceCarrier_subset_unionCarrier S hi hb0
  have hb1c := coverUnionFaceCarrier_subset_unionCarrier S hi hb1
  have hb2c := coverUnionFaceCarrier_subset_unionCarrier S hi hb2
  have hb3c := coverUnionFaceCarrier_subset_unionCarrier S hi hb3
  have h01 : H.Adj ⟨b0, hb0c⟩ ⟨b1, hb1c⟩ :=
    ⟨i, hi,
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        (by simpa using coverUnionFace_edge01 i)⟩
  have h12 : H.Adj ⟨b1, hb1c⟩ ⟨b2, hb2c⟩ :=
    ⟨i, hi,
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        (by simpa using coverUnionFace_edge12 i)⟩
  have h30 : H.Adj ⟨b3, hb3c⟩ ⟨b0, hb0c⟩ :=
    ⟨i, hi,
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        (by simpa using coverUnionFace_edge30 i)⟩
  have hvfour : v = b0 ∨ v = b1 ∨ v = b2 ∨ v = b3 := by
    rw [coverUnionFaceCarrier_eq_four] at hv
    tauto
  have hwfour : w = b0 ∨ w = b1 ∨ w = b2 ∨ w = b3 := by
    rw [coverUnionFaceCarrier_eq_four] at hw
    tauto
  have hbasev : H.Reachable ⟨b0, hb0c⟩ ⟨v, coverUnionFaceCarrier_subset_unionCarrier S hi hv⟩ := by
    rcases hvfour with hv0 | hv1 | hv2 | hv3
    · simp_all
    · subst v; exact ⟨Walk.cons h01 Walk.nil⟩
    · subst v; exact ⟨Walk.cons h01 (Walk.cons h12 Walk.nil)⟩
    · subst v; exact ⟨Walk.cons h30.symm Walk.nil⟩
  have hbasew : H.Reachable ⟨b0, hb0c⟩ ⟨w, coverUnionFaceCarrier_subset_unionCarrier S hi hw⟩ := by
    rcases hwfour with hw0 | hw1 | hw2 | hw3
    · simp_all
    · subst w; exact ⟨Walk.cons h01 Walk.nil⟩
    · subst w; exact ⟨Walk.cons h01 (Walk.cons h12 Walk.nil)⟩
    · subst w; exact ⟨Walk.cons h30.symm Walk.nil⟩
  exact hbasev.symm.trans hbasew
end

section
variable {n : ℕ}
theorem coverUnionFaceCarriers_shareVertex_of_edge (i j : ParafermionicCoverFiniteFaceTopIndex n)
    {e : Sym2 (ParafermionicCoverBoxVertex n)}
    (hei : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hej : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet) :
    ∃ x, x ∈ coverUnionFaceCarrier i ∧ x ∈ coverUnionFaceCarrier j := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      refine ⟨x, ⟨y, ?_⟩, ⟨y, ?_⟩⟩ <;> simp_all

theorem coverUnionFaceRel_reachable (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
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
  revert v w
  induction hpath with
  | refl =>
      intro v w hv hw
      exact coverUnionFace_localReach S i.2 hv hw
  | @tail b c hab hbc ih =>
      intro v w hv hw
      rcases (parafermionicCoverFiniteFaceAdjacencyGraph_adj_iff b.1 c.1).mp (by tauto) with
        ⟨_, e, hbe, hce⟩
      obtain ⟨x, hxb, hxc⟩ := coverUnionFaceCarriers_shareVertex_of_edge b.1 c.1 hbe hce
      have hleft := ih hv hxb
      exact hleft.trans (coverUnionFace_localReach S c.2 hxc hw)

theorem parafermionicCoverSimpleCycleFaceUnionCarrier_connected
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ((parafermionicCoverFiniteFaceUnionGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).induce
      (parafermionicCoverFiniteFaceUnionCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp))).Connected := by
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let F := parafermionicCoverFiniteFaceAdjacencyGraph n
  let H := F.induce (↑S : Set (ParafermionicCoverFiniteFaceTopIndex n))
  have hfaces :=
    parafermionicCoverSimpleCycleFillingSet_induce_faceAdjacency_connected hn p hp
  have hanchor : ∃ a, ∀ w, H.Reachable a w := by
    rw [connected_iff_exists_forall_reachable] at hfaces
    omega
  obtain ⟨a, ha⟩ := hanchor
  let b := coverUnionFaceVertex0 a.1
  have hbLocal : b ∈ coverUnionFaceCarrier a.1 := by
    rw [coverUnionFaceCarrier_eq_four]
    tauto
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨b, (coverUnionFaceCarrier_subset_unionCarrier S a.2 hbLocal)⟩, ?_⟩
  intro z
  rcases z with ⟨z, hz⟩
  rcases hz with ⟨w, i, hi, hiz⟩
  have hzLocal : z ∈ coverUnionFaceCarrier i := by tauto
  have hfacePath : H.Reachable a ⟨i, hi⟩ := by tauto
  rcases hfacePath with ⟨q⟩
  have hrt :=
    (reachable_iff_reflTransGen a ⟨i, hi⟩).mp ⟨q⟩
  exact (coverUnionFaceRel_reachable S hrt hbLocal hzLocal)
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
