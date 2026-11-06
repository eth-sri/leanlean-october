/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

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
  symm := by
    constructor
    intro v w h
    rcases h with ⟨i, hi, hadj⟩
    exact ⟨i, hi, hadj.symm⟩
  loopless := by
    constructor
    all_goals grind

/-- The vertices incident to an actual edge of the selected-face union. -/
def parafermionicCoverFiniteFaceUnionCarrier {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))  :=
  {v | ∃ w, (parafermionicCoverFiniteFaceUnionGraph S).Adj v w}

theorem parafermionicCoverFiniteFaceUnionGraph_le_boxGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    parafermionicCoverFiniteFaceUnionGraph S ≤ parafermionicCoverBoxGraph n := by
  intro v w hadj
  rcases hadj with ⟨i, hi, hface⟩
  exact parafermionicCoverFiniteFaceBoundaryGraph_le_boxGraph i.1 i.2 hface

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

section

variable {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n)


private theorem coverUnionFace_edge01  :
    s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  change s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i) ∈
    {s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i),
     s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i),
     s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i),
     s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i)}
  simp

private theorem coverUnionFace_edge12  :
    s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  change s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i) ∈
    {s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i),
     s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i),
     s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i),
     s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i)}
  simp



private theorem coverUnionFace_edge30  :
    s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  change s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i) ∈
    {s(coverUnionFaceVertex0 i, coverUnionFaceVertex1 i),
     s(coverUnionFaceVertex1 i, coverUnionFaceVertex2 i),
     s(coverUnionFaceVertex2 i, coverUnionFaceVertex3 i),
     s(coverUnionFaceVertex3 i, coverUnionFaceVertex0 i)}
  simp

end

def coverUnionFaceCarrier {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n)  :=
  {v | ∃ w, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w}

section

variable {n : ℕ}
include n

private theorem coverUnionFaceCarrier_eq_four 
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    coverUnionFaceCarrier i =
      {coverUnionFaceVertex0 i, coverUnionFaceVertex1 i,
       coverUnionFaceVertex2 i, coverUnionFaceVertex3 i} := by
  
  ext v
  constructor
  · rintro ⟨w, hvw⟩
    have he  :=
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mpr hvw
    rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet] at he
    
    rcases he with he | he | he | he
    · aesop
    · rcases Sym2.eq_iff.mp he with ⟨hv, _⟩ | ⟨hv, _⟩
      · aesop
      · aesop
    · rcases Sym2.eq_iff.mp he with ⟨hv, _⟩ | ⟨hv, _⟩
      · aesop
      · aesop
    · aesop
  · intro hv
    
    rcases hv with hv | hv | hv | hv
    · subst v
      refine ⟨coverUnionFaceVertex1 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        (coverUnionFace_edge01 i)
    · subst v
      refine ⟨coverUnionFaceVertex0 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
         (coverUnionFace_edge01 i).symm 
    · subst v
      refine ⟨coverUnionFaceVertex1 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
         (coverUnionFace_edge12 i).symm 
    · subst v
      refine ⟨coverUnionFaceVertex0 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp
        (coverUnionFace_edge30 i)

section

variable (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) {i : ParafermionicCoverFiniteFaceTopIndex n} (hi : i ∈ S)
include hi

private theorem coverUnionFaceCarrier_subset_unionCarrier 
     :
    coverUnionFaceCarrier i ⊆ parafermionicCoverFiniteFaceUnionCarrier S := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  exact ⟨w, i, hi, hvw⟩

private theorem coverUnionFace_localReach 
    
    {v w : ParafermionicCoverBoxVertex n}
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
    simp [b0]
  have hb1 : b1 ∈ coverUnionFaceCarrier i := by
    rw [coverUnionFaceCarrier_eq_four]
    simp [b1]
  have hb2 : b2 ∈ coverUnionFaceCarrier i := by
    rw [coverUnionFaceCarrier_eq_four]
    simp [b2]
  have hb3 : b3 ∈ coverUnionFaceCarrier i := by
    rw [coverUnionFaceCarrier_eq_four]
    simp [b3]
  have hb0c := coverUnionFaceCarrier_subset_unionCarrier S hi hb0
  have hb1c := coverUnionFaceCarrier_subset_unionCarrier S hi hb1
  
  
  have h01 : H.Adj ⟨b0, hb0c⟩ ⟨b1, hb1c⟩ := by
    solve_by_elim [_root_.PottsDiscontinuity.TorusTopology.Planar.Medial.parafermionicCoverFiniteFaceUnionGraph._proof_6,
      _root_.PottsDiscontinuity.TorusTopology.Planar.Medial.coverUnionFace_edge01, _root_.Exists.intro, _root_.And.intro]
  have h12 : H.Adj ⟨b1, hb1c⟩ ⟨b2,  coverUnionFaceCarrier_subset_unionCarrier S hi hb2 ⟩ := by
    solve_by_elim [_root_.PottsDiscontinuity.TorusTopology.Planar.Medial.parafermionicCoverFiniteFaceUnionGraph._proof_6,
      _root_.PottsDiscontinuity.TorusTopology.Planar.Medial.coverUnionFace_edge12, _root_.Exists.intro, _root_.And.intro]
  
  have h30 : H.Adj ⟨b3,  coverUnionFaceCarrier_subset_unionCarrier S hi hb3 ⟩ ⟨b0, hb0c⟩ := by
    solve_by_elim [_root_.PottsDiscontinuity.TorusTopology.Planar.Medial.parafermionicCoverFiniteFaceUnionGraph._proof_6,
      _root_.PottsDiscontinuity.TorusTopology.Planar.Medial.coverUnionFace_edge30, _root_.Exists.intro, _root_.And.intro]
  have hvfour : v = b0 ∨ v = b1 ∨ v = b2 ∨ v = b3 := by
    have h := hv
    rw [coverUnionFaceCarrier_eq_four] at h
    aesop
  have hwfour : w = b0 ∨ w = b1 ∨ w = b2 ∨ w = b3 := by
    have h := hw
    rw [coverUnionFaceCarrier_eq_four] at h
    aesop
  have hbasev : H.Reachable ⟨b0, hb0c⟩ ⟨v, coverUnionFaceCarrier_subset_unionCarrier S hi hv⟩ := by
    rcases hvfour with hv0 | hv1 | hv2 | hv3
    · subst v; exact Reachable.refl _
    · subst v; exact ⟨Walk.cons h01 Walk.nil⟩
    · subst v; exact ⟨Walk.cons h01 (Walk.cons h12 Walk.nil)⟩
    · subst v; exact ⟨Walk.cons h30.symm Walk.nil⟩
  
  exact hbasev.symm.trans (by
                             rcases hwfour with hw0 | hw1 | hw2 | hw3
                             · subst w; exact Reachable.refl _
                             · subst w; exact ⟨Walk.cons h01 Walk.nil⟩
                             · subst w; exact ⟨Walk.cons h01 (Walk.cons h12 Walk.nil)⟩
                             · subst w; exact ⟨Walk.cons h30.symm Walk.nil⟩)

end

private theorem coverUnionFaceCarriers_shareVertex_of_edge 
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    {e : Sym2 (ParafermionicCoverBoxVertex n)}
    (hei : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hej : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet) :
    ∃ x, x ∈ coverUnionFaceCarrier i ∧ x ∈ coverUnionFaceCarrier j := by
  induction e using Sym2.inductionOn with
  | hf x y =>
      refine ⟨x, ⟨y, ?_⟩, ⟨y, ?_⟩⟩
      all_goals simp_all

private theorem coverUnionFaceRel_reachable 
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
  
  revert v w
  induction hpath with
  | refl =>
      intro v w hv hw
      exact coverUnionFace_localReach S i.2 hv hw
  | @tail b c hab hbc ih =>
      intro v w hv hw
      
      rcases (parafermionicCoverFiniteFaceAdjacencyGraph_adj_iff b.1 c.1).mp ((induce_adj).mp hbc) with
        ⟨_, e, hbe, hce⟩
      obtain ⟨x, hxb, hxc⟩ := coverUnionFaceCarriers_shareVertex_of_edge b.1 c.1 hbe hce
      
      
      exact (ih hv hxb).trans (coverUnionFace_localReach S c.2 hxc hw)

theorem parafermionicCoverSimpleCycleFaceUnionCarrier_connected
     (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ((parafermionicCoverFiniteFaceUnionGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).induce
      (parafermionicCoverFiniteFaceUnionCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp))).Connected := by
  
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  
  let H := (parafermionicCoverFiniteFaceAdjacencyGraph n).induce  ↑S 
  
  
  have hfaces : H.Connected := parafermionicCoverSimpleCycleFillingSet_induce_faceAdjacency_connected hn p hp
  
  obtain ⟨a, ha⟩ :=  by
                       rw [connected_iff_exists_forall_reachable] at hfaces
                       exact hfaces 
  let b := coverUnionFaceVertex0 a.1
  have hbLocal : b ∈ coverUnionFaceCarrier a.1 := by
    rw [coverUnionFaceCarrier_eq_four]
    simp [b, coverUnionFaceVertex0, coverUnionFaceVertex1,
      coverUnionFaceVertex2, coverUnionFaceVertex3]
  
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨b,  coverUnionFaceCarrier_subset_unionCarrier S a.2 hbLocal ⟩, ?_⟩
  intro z
  rcases z with ⟨z, hz⟩
  rcases hz with ⟨w, i, hi, hiz⟩
  
  
  rcases  ha ⟨i, hi⟩  with ⟨q⟩
  
  
  exact  coverUnionFaceRel_reachable S ((reachable_iff_reflTransGen a ⟨i, hi⟩).mp ⟨q⟩) hbLocal (⟨w, hiz⟩) 

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
