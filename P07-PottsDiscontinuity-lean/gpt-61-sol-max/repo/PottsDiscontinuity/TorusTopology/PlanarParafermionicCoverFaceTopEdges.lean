/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaceIncidence

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- The actual upper edge of the positively oriented lifted face, as an
unordered edge of the ambient cover graph. -/
def parafermionicCoverFiniteFaceTopEdge (f : ParafermionicCoverVertex)  :=
  s(parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
    parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)

section

variable (n : ℕ) (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
include hf

theorem parafermionicCoverFiniteFaceTopEdge_endpoints_mem
     :
     parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2  ∈ parafermionicCoverBoxVertices n ∧
     parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2  ∈
      parafermionicCoverBoxVertices n := parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
                                     (e := Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
                                       (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])

theorem parafermionicCoverFiniteFaceTopEdge_adjacent
     :
    (parafermionicCoverBoxGraph n).Adj
      ⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩
      ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩ := by
  
  exact parafermionicCoverFiniteFaceDart_adjacent n f hf
    (e := Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])


theorem parafermionicCoverFiniteFaceTopEdge_mem_edgeSet
     :
    s(⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩,
      ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩) ∈
      (parafermionicCoverBoxGraph n).edgeSet := by
  simpa  using
    parafermionicCoverFiniteFaceTopEdge_adjacent n f hf

end


private theorem coverFaceLeftLift_of_not_branch (x y k : ℤ)
    (h : (x,y) ≠ (0,-1)) :
    parafermionicCoverFaceRightUpLeftLift x y k = ((x,y+1),k) := by
  rw [parafermionicCoverFaceRightUpLeftLift_formula]
  grind

theorem parafermionicCoverFiniteFaceTopEdge_injective (n : ℕ)
    {f g : ParafermionicCoverVertex}
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (he : parafermionicCoverFiniteFaceTopEdge f =
      parafermionicCoverFiniteFaceTopEdge g) : f = g := by
  rcases f with ⟨⟨x,y⟩,k⟩
  
  simp only [parafermionicCoverFiniteFaceTopEdge, Sym2.eq_iff] at he
  rcases he with ⟨hu,hl⟩ | ⟨hu,hl⟩
  · simp_all
  · 
    have hx1 := congrArg Prod.fst (congrArg (fun z  => z.1) hu)
    have hx2 := congrArg Prod.fst (congrArg (fun z  => z.1) hl)
    simp at hx1 hx2
    omega


def parafermionicCoverFiniteFaceBottomEdge (f : ParafermionicCoverVertex)  :=
  s(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)

def parafermionicCoverFiniteFaceRightEdge (f : ParafermionicCoverVertex)  :=
  s(parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
    parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)

def parafermionicCoverFiniteFaceLeftEdge (f : ParafermionicCoverVertex)  :=
  s(parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f)

section

variable {n : ℕ} {f g : ParafermionicCoverVertex} (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
include hf hg

theorem parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le
    
    (hheight : f.1.2 ≤ g.1.2) :
    parafermionicCoverFiniteFaceBottomEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  
  rcases g with ⟨⟨x',y'⟩,k'⟩
  
  
  rcases  (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x',y'),k')).mp hg  with ⟨_,_,_,_,_,_,hnot',_⟩
  
  intro he
  simp only [parafermionicCoverFiniteFaceBottomEdge, parafermionicCoverFiniteFaceTopEdge, parafermionicCoverFaceRightLift_formula, parafermionicCoverFaceRightUpLift_formula] at he
  grind



theorem parafermionicCoverFiniteFaceRightEdge_ne_topEdge
     :
    parafermionicCoverFiniteFaceRightEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  simp_all [parafermionicCoverFiniteFaceRightEdge, parafermionicCoverFiniteFaceTopEdge]

theorem parafermionicCoverFiniteFaceLeftEdge_ne_topEdge
     :
    parafermionicCoverFiniteFaceLeftEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  
  
  rcases  (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hf  with ⟨_,_,_,_,_,_,hnot,_⟩
  rcases  (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x',y'),k')).mp hg  with ⟨_,_,_,_,_,_,hnot',_⟩
  
  
  intro he
  simp only [parafermionicCoverFiniteFaceLeftEdge,
    parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightUpLift_formula,
     coverFaceLeftLift_of_not_branch x y k hnot , coverFaceLeftLift_of_not_branch x' y' k' hnot' , Sym2.eq_iff] at he
  grind

end


end PottsDiscontinuity.TorusTopology.Planar.Medial
