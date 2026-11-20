/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.LatticeCellBoundary
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace PottsDiscontinuity.FK
open Medial Medial.LatticeAxis

/-- A normalized bond is uniquely determined by its unoriented edge. -/
private theorem boundaryAdj_bond (S : Finset LatticeVertex) (e : LatticeBond) :
    (latticeCellBoundaryGraph S).Adj e.source e.target ↔
      (e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S) := by
  rw [latticeCellBoundaryGraph_adj_iff]
  refine ⟨?_, fun h => ⟨e.adjacent, e, rfl, h⟩⟩
  rintro ⟨_, f, hf, h⟩
  exact LatticeBond.toSym2_injective (show f.toSym2 = e.toSym2 from hf) ▸ h

section

variable (S : Finset LatticeVertex) (x y : ℤ)

private theorem boundaryAdj_right :
    (latticeCellBoundaryGraph S).Adj (x,y) (x+1,y) ↔
      ((x,y) ∈ S) ≠ ((x,y-1) ∈ S) :=
  boundaryAdj_bond S ⟨(x,y), horizontal⟩

private theorem boundaryAdj_up :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y+1) ↔
      ((x,y) ∈ S) ≠ ((x-1,y) ∈ S) :=
  boundaryAdj_bond S ⟨(x,y), vertical⟩

private theorem boundaryAdj_left :
    (latticeCellBoundaryGraph S).Adj (x,y) (x-1,y) ↔
      ((x-1,y) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  rw [SimpleGraph.adj_comm]
  simpa using boundaryAdj_right S (x-1) y

theorem boundaryAdj_down :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y-1) ↔
      ((x,y-1) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  rw [SimpleGraph.adj_comm]
  simpa using boundaryAdj_up S x (y-1)

end

def latticeFourNeighbors (v : LatticeVertex) : Finset LatticeVertex :=
  {(v.1+1,v.2), (v.1-1,v.2), (v.1,v.2+1), (v.1,v.2-1)}

section

variable (S : Finset LatticeVertex) (v : LatticeVertex)

noncomputable def boundaryNeighborFinset :
    Finset LatticeVertex := by
  classical
  exact (latticeFourNeighbors v).filter fun w => (latticeCellBoundaryGraph S).Adj v w

private theorem latticeBoundary_neighborSet_eq :
    (latticeCellBoundaryGraph S).neighborSet v =
      (latticeFourNeighbors v : Set LatticeVertex) ∩
        {w | (latticeCellBoundaryGraph S).Adj v w} := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborSet, Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · intro hGraph
    have hsq := latticeCellBoundaryGraph_le S hGraph
    rcases v with ⟨x,y⟩
    grind [latticeFourNeighbors, squareLattice_adj_iff]
  simp

theorem latticeBoundary_neighborSet_eq_finset :
    (latticeCellBoundaryGraph S).neighborSet v = (boundaryNeighborFinset S v : Set LatticeVertex) := by
  classical
  rw [latticeBoundary_neighborSet_eq]
  ext w
  simp [boundaryNeighborFinset]

end

theorem latticeCellBoundaryGraph_even_degree (S : Finset LatticeVertex) :
    ∀ v : LatticeVertex, Even ((latticeCellBoundaryGraph S).neighborSet v).ncard := by
  classical
  intro ⟨x,y⟩
  rw [latticeBoundary_neighborSet_eq_finset, Set.ncard_coe_finset]
  -- The four incident bonds compare the four cyclically adjacent face indicators.
  let b₀ := ((x,y) ∈ S)
  let b₁ := ((x-1,y) ∈ S)
  let b₂ := ((x-1,y-1) ∈ S)
  let b₃ := ((x,y-1) ∈ S)
  have hpar : Even (
      (if b₀ ↔ b₁ then 0 else 1) + (if b₁ ↔ b₂ then 0 else 1) +
        (if b₂ ↔ b₃ then 0 else 1) + (if b₃ ↔ b₀ then 0 else 1)) := by
    grind
  have hcard : (boundaryNeighborFinset S (x,y)).card =
      (if b₀ ↔ b₁ then 0 else 1) + (if b₁ ↔ b₂ then 0 else 1) +
        (if b₂ ↔ b₃ then 0 else 1) + (if b₃ ↔ b₀ then 0 else 1) := by
    unfold boundaryNeighborFinset
    change (Finset.filter (fun w => (latticeCellBoundaryGraph S).Adj (x,y) w)
      (insert (x+1,y) (insert (x-1,y) (insert (x,y+1) ({(x,y-1)} : Finset LatticeVertex))))).card = _
    rw [Finset.card_filter]
    change Finset.sum
      (insert (x+1,y) (insert (x-1,y) (insert (x,y+1) ({(x,y-1)} : Finset LatticeVertex))))
      (fun w => if (latticeCellBoundaryGraph S).Adj (x,y) w then 1 else 0) = _
    rw [Finset.sum_insert (by simp [Prod.mk.injEq]; omega), Finset.sum_insert (by simp)]
    rw [Finset.sum_insert (by grind), Finset.sum_singleton]
    rw [boundaryAdj_right S x y, boundaryAdj_left S x y,
      boundaryAdj_up S x y, boundaryAdj_down S x y]
    simp [b₀,b₁,b₂,b₃, iff_comm]; omega
  rw [hcard]
  exact hpar

end PottsDiscontinuity.FK
