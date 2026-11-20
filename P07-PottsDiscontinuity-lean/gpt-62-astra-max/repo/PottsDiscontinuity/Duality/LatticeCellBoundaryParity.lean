/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.LatticeCellBoundary
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace PottsDiscontinuity.FK
open Medial
open Medial.LatticeAxis

variable (S : Finset LatticeVertex) (x y : ℤ) (v : LatticeVertex)

private theorem boundaryAdj_right :
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
      rcases hab with ⟨rfl,rfl⟩
      assumption
    | vertical =>
      grind [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target]
  · intro h
    refine ⟨?_, ⟨⟨(x,y), horizontal⟩, ?_, ?_⟩⟩
    · simp [squareLattice_adj_iff]
    · rfl
    · assumption

private theorem boundaryAdj_up :
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
      rcases hab with ⟨rfl,rfl⟩
      assumption
  · intro h
    refine ⟨?_, ⟨⟨(x,y), vertical⟩, ?_, ?_⟩⟩
    · simp [squareLattice_adj_iff]
    · rfl
    · assumption

private theorem boundaryAdj_left :
    (latticeCellBoundaryGraph S).Adj (x,y) (x-1,y) ↔
      ((x-1,y) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  have h := boundaryAdj_right S (x-1) y
  constructor
  · intro ha
    have hsimp : (x-1)+1=x := by omega
    have ha' : (latticeCellBoundaryGraph S).Adj (x-1,y) (x-1+1,y) := by simpa using ha.symm
    grind
  · intro hb
    have ha' : (latticeCellBoundaryGraph S).Adj (x-1,y) (x-1+1,y) := by grind
    simpa [(by omega)] using ha'.symm

private theorem boundaryAdj_down :
    (latticeCellBoundaryGraph S).Adj (x,y) (x,y-1) ↔
      ((x,y-1) ∈ S) ≠ ((x-1,y-1) ∈ S) := by
  have h := boundaryAdj_up S x (y-1)
  constructor
  · intro ha
    have hsimp : (y-1)+1=y := by omega
    have ha' : (latticeCellBoundaryGraph S).Adj (x,y-1) (x,y-1+1) := by simpa using ha.symm
    grind
  · intro hb
    have ha' : (latticeCellBoundaryGraph S).Adj (x,y-1) (x,y-1+1) := by grind
    simpa [(by omega)] using ha'.symm

include v in
def latticeFourNeighbors : Finset LatticeVertex :=
  {(v.1+1,v.2), (v.1-1,v.2), (v.1,v.2+1), (v.1,v.2-1)}

include S v in
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
    rcases v with ⟨x,y⟩
    rcases w with ⟨a,b⟩
    have hcoords := (squareLattice_adj_iff _ _).mp (latticeCellBoundaryGraph_le S hGraph)
    grind [latticeFourNeighbors, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  · grind

private theorem latticeBoundary_neighborSet_eq_finset :
    (latticeCellBoundaryGraph S).neighborSet v = (boundaryNeighborFinset S v) := by
  classical
  rw [latticeBoundary_neighborSet_eq]
  ext w
  simp [boundaryNeighborFinset]

theorem latticeCellBoundaryGraph_even_degree :
    ∀ v : LatticeVertex, Even ((latticeCellBoundaryGraph S).neighborSet v).ncard := by
  classical
  intro ⟨x,y⟩
  rw [latticeBoundary_neighborSet_eq_finset, Set.ncard_coe_finset]
  -- The four incident bonds compare the four cyclically adjacent face indicators.
  let b₀ := (x,y) ∈ S
  let b₁ := (x-1,y) ∈ S
  let b₂ := (x-1,y-1) ∈ S
  let b₃ := (x,y-1) ∈ S
  have hcard : (boundaryNeighborFinset S (x,y)).card =
      (if b₀ ↔ b₁ then 0 else 1) + (if b₁ ↔ b₂ then 0 else 1) +
        (if b₂ ↔ b₃ then 0 else 1) + (if b₃ ↔ b₀ then 0 else 1) := by
    unfold boundaryNeighborFinset
    rw [Finset.card_filter]
    change Finset.sum
      (insert (x+1,y) (insert (x-1,y) (insert (x,y+1) ({(x,y-1)}))))
      (fun w => if (latticeCellBoundaryGraph S).Adj (x,y) w then 1 else 0) = _
    rw [Finset.sum_insert (by simp [Prod.mk.injEq]; omega)]
    rw [Finset.sum_insert (by simp)]
    rw [Finset.sum_insert (by simp [Prod.mk.injEq]; omega)]
    rw [Finset.sum_singleton, boundaryAdj_right S x y, boundaryAdj_left S x y, boundaryAdj_up S x y, boundaryAdj_down S x y]
    simp [b₀,b₁,b₂,b₃, iff_comm]; omega
  rw [hcard]
  exact (by
    by_cases h₀ : (x,y) ∈ S <;>
      by_cases h₁ : (x-1,y) ∈ S <;>
      by_cases h₂ : (x-1,y-1) ∈ S <;>
      by_cases h₃ : (x,y-1) ∈ S <;>
        simp [b₀,b₁,b₂,b₃,h₀,h₁,h₂,h₃] <;> norm_num)

end PottsDiscontinuity.FK
