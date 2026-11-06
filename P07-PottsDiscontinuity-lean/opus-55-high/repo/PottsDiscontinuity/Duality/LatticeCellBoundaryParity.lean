/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.LatticeCellBoundary
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

namespace PottsDiscontinuity.FK
open Medial
open Medial.LatticeAxis

section
variable (S : Finset LatticeVertex) (x y : ℤ)
theorem boundaryAdj_right  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x+1,y) ↔
      ((x,y) ∈ S) ≠ ((x,y-1) ∈ S) := by
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · rintro ⟨_, e, he, hfaces⟩
    rcases e with ⟨⟨a,b⟩, ax⟩
    cases ax with
    | horizontal =>
      simp [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target] at he
      have hab : a = x ∧ b = y := by omega
      aesop
    | vertical =>
      grind [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target]
  · intro h
    refine ⟨?_, ⟨⟨(x,y), horizontal⟩, ?_, ?_⟩⟩
    · simp [squareLattice_adj_iff]
    · rfl
    tauto

theorem boundaryAdj_up  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y+1) ↔
      ((x,y) ∈ S) ≠ ((x-1,y) ∈ S) := by
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · rintro ⟨_, e, he, hfaces⟩
    rcases e with ⟨⟨a,b⟩, ax⟩
    cases ax with
    | horizontal =>
      grind [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target]
    | vertical =>
      simp [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target] at he
      have hab : a = x ∧ b = y := by omega
      aesop
  · intro h
    refine ⟨?_, ⟨⟨(x,y), vertical⟩, ?_, ?_⟩⟩
    · simp [squareLattice_adj_iff]
    · rfl
    tauto

theorem boundaryAdj_left  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x-1,y) ↔
      ((x-1,y) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  have h := boundaryAdj_right S (x-1) y
  constructor
  · intro ha
    have ha' : (latticeCellBoundaryGraph S).Adj (x-1,y) (x-1+1,y) := by simpa using ha.symm
    simp_all
  · intro hb
    have ha' : (latticeCellBoundaryGraph S).Adj (x-1,y) (x-1+1,y) := by simp_all
    simpa using ha'.symm

theorem boundaryAdj_down  :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y-1) ↔
      ((x,y-1) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  have h := boundaryAdj_up S x (y-1)
  constructor
  · intro ha
    have ha' : (latticeCellBoundaryGraph S).Adj (x,y-1) (x,y-1+1) := by simpa using ha.symm
    simp_all
  · intro hb
    have ha' : (latticeCellBoundaryGraph S).Adj (x,y-1) (x,y-1+1) := by simp_all
    simpa using ha'.symm
end

def latticeFourNeighbors (v : LatticeVertex) : Finset LatticeVertex :=
  {(v.1+1,v.2), (v.1-1,v.2), (v.1,v.2+1), (v.1,v.2-1)}

section
variable (S : Finset LatticeVertex) (v : LatticeVertex)
noncomputable def boundaryNeighborFinset  :
    Finset LatticeVertex := by
  classical
  exact (latticeFourNeighbors v).filter fun w => (latticeCellBoundaryGraph S).Adj v w

theorem latticeBoundary_neighborSet_eq  :
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
    grind [latticeFourNeighbors]
  · simp

theorem latticeBoundary_neighborSet_eq_finset  :
    (latticeCellBoundaryGraph S).neighborSet v = (boundaryNeighborFinset S v : Set LatticeVertex) := by
  grind [latticeBoundary_neighborSet_eq, boundaryNeighborFinset]
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
    change (Finset.filter (fun w => (latticeCellBoundaryGraph S).Adj (x,y) w)
      (insert (x+1,y) (insert (x-1,y) (insert (x,y+1) ({(x,y-1)} : Finset LatticeVertex))))).card = _
    rw [Finset.card_filter, Finset.sum_insert (by grind), Finset.sum_insert (by simp), Finset.sum_insert (by grind), Finset.sum_singleton]
    rw [boundaryAdj_right S x y, boundaryAdj_left S x y,
      boundaryAdj_up S x y, boundaryAdj_down S x y]
    simp [b₀,b₁,b₂,b₃, iff_comm]; omega
  rwa [hcard]

end PottsDiscontinuity.FK
