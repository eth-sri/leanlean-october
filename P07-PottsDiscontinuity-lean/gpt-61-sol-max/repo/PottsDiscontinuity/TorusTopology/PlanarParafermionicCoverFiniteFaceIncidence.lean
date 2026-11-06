/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial



/-- The four positively ordered directed edge occurrences in the literal lift
of an ordinary face. -/
def parafermionicCoverFiniteFaceDarts (f : ParafermionicCoverVertex) :
    Finset (ParafermionicCoverVertex × ParafermionicCoverVertex) :=
  { Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2),
    Prod.mk (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2),
    Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2),
    Prod.mk (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2) f }

section

variable (n : ℕ) (f : ParafermionicCoverVertex) (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) {e : ParafermionicCoverVertex × ParafermionicCoverVertex} (he : e ∈ parafermionicCoverFiniteFaceDarts f)
include hf he

theorem parafermionicCoverFiniteFaceDart_endpoints_mem
     :
    e.1 ∈ parafermionicCoverBoxVertices n ∧
      e.2 ∈ parafermionicCoverBoxVertices n := by
  rcases f with ⟨⟨x,y⟩,k⟩
  
  rcases  (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hf  with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
  
  
  rcases  (parafermionicCoverFaceIntermediateBounds_iff n ((x,y),k)).2
            ⟨hxlo,by omega,hylo,by omega,hklo,hkhi,hnot,hseam⟩  with ⟨_,_,hR,hU,hL⟩
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert] at he
  grind

theorem parafermionicCoverFiniteFaceDart_adjacent
     :
    (parafermionicCoverGraph).Adj e.1 e.2 := by
  rcases f with ⟨⟨x,y⟩,k⟩
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with he | he | he | he
  · subst e
    exact (parafermionicCoverFaceLift_steps_adj x y k).1
  · subst e
    exact (parafermionicCoverFaceLift_steps_adj x y k).2.1
  · subst e
    exact (parafermionicCoverFaceLift_steps_adj x y k).2.2.1
  · subst e
    
    
    rw [← parafermionicCoverFaceLiftEndpoint_eq_start_of_not_branch x y k (by
                                                                             have hcrit := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hf
                                                                             simp_all)]
    exact (parafermionicCoverFaceLift_steps_adj x y k).2.2.2

end


/-- A positively directed lifted edge in two retained ordinary face boundaries
has only one lower-left face occurrence. -/
theorem parafermionicCoverFiniteFaceDart_unique
    (n : ℕ) {f g : ParafermionicCoverVertex}
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
    {e : ParafermionicCoverVertex × ParafermionicCoverVertex}
    (he : e ∈ parafermionicCoverFiniteFaceDarts f)
    (he' : e ∈ parafermionicCoverFiniteFaceDarts g) : f = g := by
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  
  
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
    Finset.mem_singleton, parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula] at he he'
  rcases he with h1 | h2 | h3 | h4 <;>
    rcases he' with h1' | h2' | h3' | h4' <;>
    simp_all <;> omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
