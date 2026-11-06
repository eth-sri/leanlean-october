module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaceIncidence

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def parafermionicCoverFiniteFaceTopEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
    parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)

theorem parafermionicCoverFiniteFaceTopEdge_endpoints_mem
    (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2) ∈ parafermionicCoverBoxVertices n ∧
    (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2) ∈
      parafermionicCoverBoxVertices n :=
  parafermionicCoverFiniteFaceDart_endpoints_mem n f hf
    (e := Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])

theorem parafermionicCoverFiniteFaceTopEdge_adjacent
    (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    (parafermionicCoverBoxGraph n).Adj
      ⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩
      ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩ :=
  parafermionicCoverFiniteFaceDart_adjacent n f hf
    (e := Prod.mk (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)
      (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2)) (by simp [parafermionicCoverFiniteFaceDarts])

theorem parafermionicCoverFiniteFaceTopEdge_mem_edgeSet
    (n : ℕ) (f : ParafermionicCoverVertex)
    (hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    s(⟨parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).1⟩,
      ⟨parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2,
        (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n f hf).2⟩) ∈
      (parafermionicCoverBoxGraph n).edgeSet := by
  simpa [SimpleGraph.mem_edgeSet] using
    parafermionicCoverFiniteFaceTopEdge_adjacent n f hf

theorem parafermionicCoverFiniteFaceTopEdge_injective (n : ℕ)
    {f g : ParafermionicCoverVertex}
    (_hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (_hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (he : parafermionicCoverFiniteFaceTopEdge f =
      parafermionicCoverFiniteFaceTopEdge g) : f = g := by
  rcases f with ⟨⟨x, y⟩, k⟩
  rcases g with ⟨⟨x', y'⟩, k'⟩
  simp only [parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula, Sym2.eq_iff, Prod.mk.injEq] at he
  rcases he with ⟨⟨⟨hx, hy⟩, hk⟩, _⟩ | ⟨⟨⟨hx, hy⟩, _⟩, ⟨⟨hx', _⟩, _⟩⟩
  · ext <;> dsimp <;> omega
  · omega

def parafermionicCoverFiniteFaceBottomEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2)

def parafermionicCoverFiniteFaceRightEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
    parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2)

def parafermionicCoverFiniteFaceLeftEdge (f : ParafermionicCoverVertex) :
    Sym2 ParafermionicCoverVertex :=
  s(parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f)

theorem parafermionicCoverFiniteFaceBottomEdge_ne_topEdge_of_height_le
    {n : ℕ} {f g : ParafermionicCoverVertex}
    (_hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (_hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (hheight : f.1.2 ≤ g.1.2) :
    parafermionicCoverFiniteFaceBottomEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  rcases f with ⟨⟨x, y⟩, k⟩
  rcases g with ⟨⟨x', y'⟩, k'⟩
  dsimp at hheight
  intro he
  simp only [parafermionicCoverFiniteFaceBottomEdge, parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightLift_formula, parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula, Sym2.eq_iff, Prod.mk.injEq] at he
  rcases he with ⟨⟨_, hy⟩, _⟩ | ⟨⟨_, hy⟩, _⟩ <;> omega

theorem parafermionicCoverFiniteFaceRightEdge_ne_topEdge
    {n : ℕ} {f g : ParafermionicCoverVertex}
    (_hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (_hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    parafermionicCoverFiniteFaceRightEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  rcases f with ⟨⟨x, y⟩, k⟩
  rcases g with ⟨⟨x', y'⟩, k'⟩
  intro he
  simp only [parafermionicCoverFiniteFaceRightEdge, parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightLift_formula, parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula, Sym2.eq_iff, Prod.mk.injEq] at he
  rcases he with ⟨⟨_, hy⟩, ⟨_, hy'⟩, _⟩ | ⟨⟨_, hy⟩, ⟨_, hy'⟩, _⟩ <;> omega

theorem parafermionicCoverFiniteFaceLeftEdge_ne_topEdge
    {n : ℕ} {f g : ParafermionicCoverVertex}
    (_hf : f ∈ parafermionicCoverFiniteOrdinaryFaces n)
    (_hg : g ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    parafermionicCoverFiniteFaceLeftEdge f ≠
      parafermionicCoverFiniteFaceTopEdge g := by
  rcases f with ⟨⟨x, y⟩, k⟩
  rcases g with ⟨⟨x', y'⟩, k'⟩
  intro he
  simp only [parafermionicCoverFiniteFaceLeftEdge, parafermionicCoverFiniteFaceTopEdge,
    parafermionicCoverFaceRightUpLift_formula, parafermionicCoverFaceRightUpLeftLift_formula,
    Sym2.eq_iff, Prod.mk.injEq] at he
  rcases he with ⟨⟨_, hy⟩, ⟨_, hy'⟩, _⟩ | ⟨⟨_, hy⟩, ⟨_, hy'⟩, _⟩ <;> omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
