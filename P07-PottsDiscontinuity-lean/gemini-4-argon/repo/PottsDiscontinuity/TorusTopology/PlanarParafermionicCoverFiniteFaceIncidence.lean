module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def parafermionicCoverFiniteFaceDarts (f : ParafermionicCoverVertex) :
    Finset (ParafermionicCoverVertex × ParafermionicCoverVertex) :=
  { Prod.mk f (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2),
    Prod.mk (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2),
    Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2),
    Prod.mk (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2) f }

theorem parafermionicCoverFiniteFaceDart_endpoints_mem
    (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    {e : ParafermionicCoverVertex × ParafermionicCoverVertex}
    (he : e ∈ parafermionicCoverFiniteFaceDarts f) :
    e.1 ∈ parafermionicCoverBoxVertices n ∧
      e.2 ∈ parafermionicCoverBoxVertices n := by
  have hbounds := (parafermionicCoverFaceIntermediateBounds_iff n f).2
    ((parafermionicCoverFiniteOrdinaryFaces_mem_iff n f).1 hf)
  rcases hbounds with ⟨hstart, hR, hU, hL⟩
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hstart, hR⟩
  · exact ⟨hR, hU⟩
  · exact ⟨hU, hL⟩
  · exact ⟨hL, hstart⟩

theorem parafermionicCoverFiniteFaceDart_adjacent
    (n : ℕ) (f : ParafermionicCoverVertex)
    (_hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    {e : ParafermionicCoverVertex × ParafermionicCoverVertex}
    (he : e ∈ parafermionicCoverFiniteFaceDarts f) :
    parafermionicCoverGraph.Adj e.1 e.2 := by
  rcases f with ⟨⟨x, y⟩, k⟩
  have hsteps := parafermionicCoverFaceLift_steps_adj x y k
  rw [parafermionicCoverFaceLiftEndpoint_eq_start] at hsteps
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hsteps.1
  · exact hsteps.2.1
  · exact hsteps.2.2.1
  · exact hsteps.2.2.2

theorem parafermionicCoverFiniteFaceDart_unique
    (n : ℕ) {f g : ParafermionicCoverVertex}
    (_hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (_hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
    {e : ParafermionicCoverVertex × ParafermionicCoverVertex}
    (he : e ∈ parafermionicCoverFiniteFaceDarts f)
    (he' : e ∈ parafermionicCoverFiniteFaceDarts g) : f = g := by
  rcases f with ⟨⟨x, y⟩, k⟩
  rcases g with ⟨⟨x', y'⟩, k'⟩
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
    Finset.mem_singleton, parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula] at he he'
  rcases he with h1 | h2 | h3 | h4 <;>
    rcases he' with h1' | h2' | h3' | h4' <;>
    simp_all <;> omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
