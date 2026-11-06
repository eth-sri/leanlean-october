/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverBoxConnectivity
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceTopEdges

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable (n : ℕ)
/-- The actual finite cover graph after deleting every retained ordinary face's
positively oriented top edge. -/
def parafermionicCoverBoxGraphWithoutFaceTops  :
    SimpleGraph (ParafermionicCoverBoxVertex n) where
  Adj u v := (parafermionicCoverBoxGraph n).Adj u v ∧
    ∀ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge f ≠ s(u.1,v.1)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    grind⟩
  loopless := ⟨by
    simp⟩

theorem parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top
    {u v : ParafermionicCoverBoxVertex n}
    (h : (parafermionicCoverBoxGraph n).Adj u v)
    (hnot : ∀ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge f ≠ s(u.1,v.1)) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj u v := by tauto
end

theorem topEdge_ne_of_same_base_x
    {u v : ParafermionicCoverVertex}
    (hux : u.1.1 = v.1.1) (f : ParafermionicCoverVertex) :
    parafermionicCoverFiniteFaceTopEdge f ≠ s(u,v) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> aesop

section
variable (n : ℕ)
theorem parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x
    {u v : ParafermionicCoverBoxVertex n}
    (h : (parafermionicCoverBoxGraph n).Adj u v)
    (hux : u.1.1.1 = v.1.1.1) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj u v := by
  simp_all [parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top, topEdge_ne_of_same_base_x]

def coverFacePoint (v : ParafermionicCoverVertex)
    (hv : v ∈ parafermionicCoverBoxVertices n) : ParafermionicCoverBoxVertex n :=
  ⟨v,hv⟩
end

 section
variable (n : ℕ) (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
include hf
theorem coverFace_bottom_endpoints_mem  :
    f ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2 ∈ parafermionicCoverBoxVertices n :=
  parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
    (e := Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2))
    (by simp [parafermionicCoverFiniteFaceDarts])

def coverFaceS  : ParafermionicCoverBoxVertex n :=
  coverFacePoint n f (coverFace_bottom_endpoints_mem n f hf).1

def coverFaceR  : ParafermionicCoverBoxVertex n :=
  coverFacePoint n (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)
    (coverFace_bottom_endpoints_mem n f hf).2

def coverFaceU  : ParafermionicCoverBoxVertex n :=
  coverFacePoint n (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1

def coverFaceL  : ParafermionicCoverBoxVertex n :=
  coverFacePoint n (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2

theorem coverFace_bottom_adj_of_not_removed (hnot : ∀ g ∈ parafermionicCoverFiniteOrdinaryFaces n,
      parafermionicCoverFiniteFaceTopEdge g ≠
        s(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Adj (coverFaceS n f hf)
      (coverFaceR n f hf) := by
  apply parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top n
  · have hmem : Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2) ∈
        parafermionicCoverFiniteFaceDarts f := by
      simp [parafermionicCoverFiniteFaceDarts]
    exact parafermionicCoverFiniteFaceDart_adjacent n f hf hmem
  tauto
end


section
variable (n : ℕ)
theorem coverFace_top_reachable (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable
      (coverFaceU n f hf) (coverFaceL n f hf) := by
  let rank (g : ParafermionicCoverVertex) := (g.1.2 + (n : ℤ)).toNat
  have H : ∀ m (g : ParafermionicCoverVertex) (hrank : rank g ≤ m)
      (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n),
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
        exact (parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x n hadj (by rfl)).symm.reachable
      have hS_L : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable S L := by
        have hadj : (parafermionicCoverBoxGraph n).Adj L S := by
          have hm : Prod.mk (parafermionicCoverFaceRightUpLeftLift x y k) ((x,y),k) ∈
              parafermionicCoverFiniteFaceDarts ((x,y),k) := by
            simp [parafermionicCoverFiniteFaceDarts]
          exact parafermionicCoverFiniteFaceDart_adjacent n ((x,y),k) hg hm
        exact (parafermionicCoverBoxGraphWithoutFaceTops_adj_of_same_base_x n hadj (by rfl)).symm.reachable
      by_cases hremoved : ∃ g' ∈ parafermionicCoverFiniteOrdinaryFaces n,
          parafermionicCoverFiniteFaceTopEdge g' = s(((x,y),k),
            parafermionicCoverFaceRightLift x y k)
      · obtain ⟨g',hg',hedge⟩ := hremoved
        have hlow : g'.1.2 < y := by
          by_contra h
          have hle : y ≤ g'.1.2 := by omega
          exact (parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le hg hg' hle)
            (by simp_all [parafermionicCoverFiniteFaceBottomEdge])
        have hgNonneg : 0 ≤ g'.1.2 + (n : ℤ) := by
          have hc := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n g').mp hg'
          omega
        have hrankLower : rank g' < rank ((x,y),k) := by
          dsimp [rank]
          omega
        have hreachg := ih (rank g') (by omega) g' (Nat.le_refl _) hg'
        have hbridge : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable R S := by
          rcases Sym2.eq_iff.mp hedge with ⟨hU,hL⟩ | ⟨hU,hL⟩
          · have hU' : coverFaceU n g' hg' = S := by
              apply Subtype.ext
              tauto
            have hL' : coverFaceL n g' hg' = R := by
              apply Subtype.ext
              tauto
            simpa [U,L,R,S,hU',hL'] using hreachg.symm
          · have hU' : coverFaceU n g' hg' = R := by
              apply Subtype.ext
              tauto
            have hL' : coverFaceL n g' hg' = S := by
              apply Subtype.ext
              tauto
            simp_all
        exact hU_R.trans (hbridge.trans hS_L)
      · have hbottom :=
          coverFace_bottom_adj_of_not_removed n ((x,y),k) hg (by
            simp_all)
        exact hU_R.trans (hbottom.symm.reachable.trans hS_L)
  tauto

theorem parafermionicCoverBoxGraphWithoutFaceTops_connected
    (hn : 1 ≤ n) :
    (parafermionicCoverBoxGraphWithoutFaceTops n).Connected := by
  have horigin : (((0:ℤ),(0:ℤ)),(0:ℤ)) ∈ parafermionicCoverBoxVertices n := by
    rw [parafermionicCoverBoxVertices_mem]
    norm_num
  let v : ParafermionicCoverBoxVertex n := ⟨((0,0),0), horigin⟩
  let : Nonempty (ParafermionicCoverBoxVertex n) := by tauto
  refine ⟨?_⟩
  intro u v
  obtain ⟨w⟩ := parafermionicCoverBoxGraph_connected n hn u v
  induction w with
  | nil => rfl
  | @cons a b c hab w ih =>
      have hstep : (parafermionicCoverBoxGraphWithoutFaceTops n).Reachable a b := by
        by_cases htop : ∃ f ∈ parafermionicCoverFiniteOrdinaryFaces n,
            parafermionicCoverFiniteFaceTopEdge f = s(a.1,b.1)
        · obtain ⟨f,hf,he⟩ := htop
          rcases Sym2.eq_iff.mp he with ⟨hU,hL⟩ | ⟨hU,hL⟩
          · have hU' : coverFaceU n f hf = a := by
              apply Subtype.ext
              tauto
            have hL' : coverFaceL n f hf = b := by
              apply Subtype.ext
              tauto
            simpa [hU',hL'] using coverFace_top_reachable n f hf
          · have hU' : coverFaceU n f hf = b := by
              apply Subtype.ext
              tauto
            have hL' : coverFaceL n f hf = a := by
              apply Subtype.ext
              tauto
            simpa [hU',hL'] using (coverFace_top_reachable n f hf).symm
        · have hadj :=
            parafermionicCoverBoxGraphWithoutFaceTops_adj_of_not_top n hab (by
              simp_all)
          exact hadj.reachable
      exact hstep.trans ih
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
