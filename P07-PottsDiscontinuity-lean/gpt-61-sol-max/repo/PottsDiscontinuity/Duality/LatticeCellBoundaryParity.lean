/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.LatticeCellBoundary
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace PottsDiscontinuity.FK
open Medial
open Medial.LatticeAxis

section

variable (S : Finset LatticeVertex) (x y : ℤ)


private theorem boundaryAdj_right  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x+1,y) ↔
      ((x,y) ∈ S) ≠ ((x,y-1) ∈ S) := by
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · grind [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target, LatticeBond.faceBase]
  · intro h
    refine ⟨?_, ⟨⟨(x,y), horizontal⟩, ?_, ?_⟩⟩
    · simp [squareLattice_adj_iff]
    all_goals aesop

private theorem boundaryAdj_up  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y+1) ↔
      ((x,y) ∈ S) ≠ ((x-1,y) ∈ S) := by
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · grind [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target, LatticeBond.faceBase]
  · intro h
    refine ⟨?_, ⟨⟨(x,y), vertical⟩, ?_, ?_⟩⟩
    · simp [squareLattice_adj_iff]
    all_goals aesop

private theorem boundaryAdj_left  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x-1,y) ↔
      ((x-1,y) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  have h := boundaryAdj_right S (x-1) y
  constructor
  · intro ha
    
    
    simpa  using h.mp (by simpa  using ha.symm)
  · intro hb
    
    
    simpa  using (by simp_all : (latticeCellBoundaryGraph S).Adj (x-1,y) (x-1+1,y)).symm

private theorem boundaryAdj_down  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y-1) ↔
      ((x,y-1) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  have h := boundaryAdj_up S x (y-1)
  constructor
  · intro ha
    
    
    simpa  using h.mp (by simpa  using ha.symm)
  · intro hb
    
    
    simpa  using (by simp_all : (latticeCellBoundaryGraph S).Adj (x,y-1) (x,y-1+1)).symm

end

def latticeFourNeighbors (v : LatticeVertex) : Finset LatticeVertex :=
  {(v.1+1,v.2), (v.1-1,v.2), (v.1,v.2+1), (v.1,v.2-1)}

noncomputable def boundaryNeighborFinset (S : Finset LatticeVertex) (v : LatticeVertex) :
    Finset LatticeVertex := by
  classical
  exact (latticeFourNeighbors v).filter ((latticeCellBoundaryGraph S).Adj v)

private theorem latticeBoundary_neighborSet_eq (S : Finset LatticeVertex) (v : LatticeVertex) :
    (latticeCellBoundaryGraph S).neighborSet v =
      (latticeFourNeighbors v : Set LatticeVertex) ∩
        {w | (latticeCellBoundaryGraph S).Adj v w} := by
  
  ext w
  simp only [SimpleGraph.mem_neighborSet, Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · intro hGraph
    
    rcases v with ⟨x,y⟩
    rcases w with ⟨a,b⟩
    have hcoords := (squareLattice_adj_iff (x,y) (a,b)).mp (latticeCellBoundaryGraph_le S hGraph)
    
    
    simp only [latticeFourNeighbors]
    grind
  · rintro ⟨hw, hadj⟩
    exact hadj

private theorem latticeBoundary_neighborSet_eq_finset (S : Finset LatticeVertex)
    (v : LatticeVertex) :
    (latticeCellBoundaryGraph S).neighborSet v = (boundaryNeighborFinset S v : Set LatticeVertex) := by
  grind [boundaryNeighborFinset, latticeBoundary_neighborSet_eq]

theorem latticeCellBoundaryGraph_even_degree (S : Finset LatticeVertex) :
    ∀ v : LatticeVertex, Even ((latticeCellBoundaryGraph S).neighborSet v).ncard := by
  classical
  intro ⟨x,y⟩
  rw [latticeBoundary_neighborSet_eq_finset, Set.ncard_coe_finset]
  -- The four incident bonds compare the four cyclically adjacent face indicators.
  let b₀ :=  (x,y) ∈ S 
  let b₁ :=  (x-1,y) ∈ S 
  let b₂ :=  (x-1,y-1) ∈ S 
  let b₃ :=  (x,y-1) ∈ S 
  
  have hcard : (boundaryNeighborFinset S (x,y)).card =
      (if b₀ ↔ b₁ then 0 else 1) + (if b₁ ↔ b₂ then 0 else 1) +
        (if b₂ ↔ b₃ then 0 else 1) +  if b₃ ↔ b₀ then 0 else 1  := by
    
    change (Finset.filter  ((latticeCellBoundaryGraph S).Adj (x,y)) 
      (insert (x+1,y) (insert (x-1,y) (insert (x,y+1)  {(x,y-1)} )))).card = _
    rw [Finset.card_filter]
    
    rw [Finset.sum_insert (by simp ; omega)]
    rw [Finset.sum_insert (by simp )]
    rw [Finset.sum_insert (by simp ; omega)]
    rw [Finset.sum_singleton]
    rw [boundaryAdj_right S x y, boundaryAdj_left S x y,
      boundaryAdj_up S x y, boundaryAdj_down S x y]
    simp [b₀,b₁,b₂,b₃, iff_comm]; omega
  
  exact  by
           grind 

end PottsDiscontinuity.FK
