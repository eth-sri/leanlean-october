/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverBoxConnectivity
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopEdges

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The actual finite cover graph after deleting every retained ordinary face's
positively oriented top edge. -/
def parafermionicCoverBoxGraphWithoutFaceTops (n : ℕ) :
    SimpleGraph (ParafermionicCoverBoxVertex n) where
  Adj u v := (parafermionicCoverBoxGraph n).Adj u v ∧
    ∀ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge f ≠ s(u.1,v.1)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    all_goals grind⟩
  loopless := ⟨by
    simp_all⟩

private theorem parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top
    (n : ℕ) {u v : ParafermionicCoverBoxVertex n}
    (h : (parafermionicCoverBoxGraph n).Adj u v)
    (hnot : ∀ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge f ≠ s(u.1,v.1)) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj u v := ⟨h,hnot⟩

private theorem topEdge_ne_of_same_base_x
    {u v : ParafermionicCoverVertex}
    (hux : u.1.1 = v.1.1) (f : ParafermionicCoverVertex) :
    parafermionicCoverFiniteFaceTopEdge f ≠ s(u,v) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  all_goals aesop

theorem parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x
    (n : ℕ) {u v : ParafermionicCoverBoxVertex n}
    (h : (parafermionicCoverBoxGraph n).Adj u v)
    (hux : u.1.1.1 = v.1.1.1) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj u v := by
  simp_all [parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top, topEdge_ne_of_same_base_x]

def coverFacePoint (n : ℕ) (v : ParafermionicCoverVertex)
    (hv : v ∈ parafermionicCoverBoxVertices n) : ParafermionicCoverBoxVertex n :=
  ⟨v,hv⟩

 theorem coverFace_bottom_endpoints_mem (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    f ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2 ∈ parafermionicCoverBoxVertices n :=
  parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
    (e := Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
    (by simp [parafermionicCoverFiniteFaceDarts])

def coverFaceS (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)  :=
  coverFacePoint n f (coverFace_bottom_endpoints_mem n f hf).1

def coverFaceR (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)  :=
  coverFacePoint n (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)
    (coverFace_bottom_endpoints_mem n f hf).2

def coverFaceU (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)  :=
  coverFacePoint n (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1

def coverFaceL (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)  :=
  coverFacePoint n (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2

section

variable (n : ℕ) (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
include n f hf

private theorem coverFace_bottom_adj_of_not_removed 
    (hnot : ∀ g ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge g ≠
        s(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj (coverFaceS n f hf)
      (coverFaceR n f hf) := by
  apply parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top n
  · 
    have hmem : Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2) ∈
        parafermionicCoverFiniteFaceDarts f := by
      simp [parafermionicCoverFiniteFaceDarts]
    exact parafermionicCoverFiniteFaceDart_adjacent n f hf hmem
  · intro g hg he
    exact hnot g hg he



private theorem coverFace_top_reachable  :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable
      (coverFaceU n f hf) (coverFaceL n f hf) := by
  let rank (g : ParafermionicCoverVertex) := (g.1.2 +  n ).toNat
  have H : ∀ m g (hrank : rank g ≤ m)
      hg,
      (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable
        (coverFaceU n g hg) (coverFaceL n g hg) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g hrank hg
      
      rcases g with ⟨⟨x,y⟩,k⟩
      
      let U := coverFaceU n ((x,y),k) hg
      let L := coverFaceL n ((x,y),k) hg
      let R := coverFaceR n ((x,y),k) hg
      let S := coverFaceS n ((x,y),k) hg
      have hU_R : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable U R := by
        have hadj : (parafermionicCoverBoxGraph n).Adj R U := by
          
          have hm : Prod.mk (parafermionicCoverFaceRightLift x y k)
              (parafermionicCoverFaceRightUpLift x y k) ∈
              parafermionicCoverFiniteFaceDarts ((x,y),k) := by
            simp [parafermionicCoverFiniteFaceDarts]
          exact parafermionicCoverFiniteFaceDart_adjacent n ((x,y),k) hg hm
        have hx : R.1.1.1 = U.1.1.1 := by rfl
        exact (parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x n hadj hx).symm.reachable
      have hS_L : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable S L := by
        have hadj : (parafermionicCoverBoxGraph n).Adj L S := by
          
          have hm : Prod.mk (parafermionicCoverFaceRightUpLeftLift x y k) ((x,y),k) ∈
              parafermionicCoverFiniteFaceDarts ((x,y),k) := by
            simp [parafermionicCoverFiniteFaceDarts]
          exact parafermionicCoverFiniteFaceDart_adjacent n ((x,y),k) hg hm
        have hx : L.1.1.1 = S.1.1.1 := by rfl
        exact (parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x n hadj hx).symm.reachable
      by_cases hremoved : ∃ g' ∈ parafermionicCoverFiniteOrdinaryFaces n,
          parafermionicCoverFiniteFaceTopEdge g' = s(((x,y),k),
            parafermionicCoverFaceRightLift x y k)
      · obtain ⟨g',hg',hedge⟩ := hremoved
        have hlow : g'.1.2 < y := by
          by_contra h
          have hle : y ≤ g'.1.2 := by omega
          exact (parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le hg hg' hle)
            (by simp_all [parafermionicCoverFiniteFaceBottomEdge])
        
        have hgNonneg : 0 ≤ g'.1.2 +  n  := by
          have hc := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n g').mp hg'
          omega
        have hrankLower : rank g' < rank ((x,y),k) := by
          dsimp [rank]
          all_goals simp_all
        have hlt  := lt_of_lt_of_le hrankLower hrank
        have hreachg := ih (rank g') hlt g' (Nat.le_refl _) hg'
        have hbridge : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable R S := by
                                                                                        exact Or.casesOn (Sym2.eq_iff.mp hedge)
                                                                                                (fun h =>
                                                                                                  And.casesOn h fun hU hL =>
                                                                                                    Eq.mp (congr (congrArg (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable (Subtype.ext hL)) (Subtype.ext hU))
                                                                                                      (SimpleGraph.Reachable.symm hreachg))
                                                                                                fun h =>
                                                                                                And.casesOn h fun hU hL =>
                                                                                                  Eq.mp (congr (congrArg (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable (Subtype.ext hU)) (Subtype.ext hL))
                                                                                                    hreachg
        exact hU_R.trans (hbridge.trans hS_L)
      · have hbottom  :=
          coverFace_bottom_adj_of_not_removed n ((x,y),k) hg (by
            simp_all)
        exact hU_R.trans (hbottom.symm.reachable.trans hS_L)
  exact H (rank f) f le_rfl hf

end

theorem parafermionicCoverBoxGraphWithoutFaceTops_connected
    (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Connected := by
  
  
  have horigin : (( 0 , 0 ), 0 ) ∈ parafermionicCoverBoxVertices n := by
    rw [parafermionicCoverBoxVertices_mem]
    norm_num
  let v : ParafermionicCoverBoxVertex n := ⟨((0,0),0), horigin⟩
  let : Nonempty (ParafermionicCoverBoxVertex n) := ⟨v⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨w⟩ := parafermionicCoverBoxGraph_connected n hn u v
  induction w with
  | nil => exact .rfl
  | @cons a b c hab w ih =>
      have hstep : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable a b := by
        by_cases htop : ∃ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
            parafermionicCoverFiniteFaceTopEdge f = s(a.1,b.1)
        · obtain ⟨f,hf,he⟩ := htop
          rcases Sym2.eq_iff.mp he with ⟨hU,hL⟩ | ⟨hU,hL⟩
          · have hU' : coverFaceU n f hf = a := Subtype.ext hU
            have hL' : coverFaceL n f hf = b := Subtype.ext hL
            simpa [hU',hL'] using coverFace_top_reachable n f hf
          · have hU' : coverFaceU n f hf = b := Subtype.ext hU
            have hL' : coverFaceL n f hf = a := Subtype.ext hL
            simpa [hU',hL'] using (coverFace_top_reachable n f hf).symm
        · 
          exact (parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top n hab (by
                     simp_all)).reachable
      exact hstep.trans ih

end PottsDiscontinuity.TorusTopology.Planar.Medial
