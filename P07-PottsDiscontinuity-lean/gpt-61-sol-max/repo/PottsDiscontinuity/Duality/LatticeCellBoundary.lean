/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.LatticePorts
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.FK
open Medial
open Medial.LatticeAxis

 def cellBoundaryBonds (c : LatticeVertex) : Finset LatticeBond :=
  {⟨c, horizontal⟩, ⟨(c.1, c.2 + 1), horizontal⟩,
   ⟨c, vertical⟩, ⟨(c.1 + 1, c.2), vertical⟩}

theorem mem_cellBoundaryBonds_faceBase (c : LatticeVertex) (e : LatticeBond) :
    e ∈ cellBoundaryBonds c ↔ e.faceBase false = c ∨ e.faceBase true = c := by
  rcases c with ⟨x,y⟩
  rcases e with ⟨⟨a,b⟩, ax⟩
  cases ax <;> simp [cellBoundaryBonds, LatticeBond.faceBase] <;> omega

/-- Actual primal bonds separating a selected finite set of unit faces from its complement. -/
def latticeCellBoundaryBonds (S : Finset LatticeVertex) : Finset LatticeBond := by
  classical
  exact (S.biUnion cellBoundaryBonds).filter
     fun e => (e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S) 

theorem mem_latticeCellBoundaryBonds (S : Finset LatticeVertex) (e : LatticeBond) :
    e ∈ latticeCellBoundaryBonds S ↔
       (e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S)  := by
  grind [latticeCellBoundaryBonds, mem_cellBoundaryBonds_faceBase]

theorem latticeCellBoundaryBonds_finite (S : Finset LatticeVertex) :
    (latticeCellBoundaryBonds S : Set LatticeBond).Finite := Finset.finite_toSet _

/-- The graph whose edges are precisely the actual bonds crossing the face boundary. -/
def latticeCellBoundaryGraph (S : Finset LatticeVertex) : SimpleGraph LatticeVertex where
  Adj u v := squareLattice.Adj u v ∧ ∃ e ∈ latticeCellBoundaryBonds S, e.toSym2 = s(u,v)
  symm := ⟨by
    intro u v h
    rcases h with ⟨hadj, e, he, hsym⟩
    exact ⟨hadj.symm, e, he, hsym.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by
    simp_all⟩

theorem latticeCellBoundaryGraph_le (S : Finset LatticeVertex) :
    latticeCellBoundaryGraph S ≤ squareLattice := fun u v h => h.1

theorem latticeCellBoundaryGraph_adj_iff (S : Finset LatticeVertex) (u v : LatticeVertex) :
    (latticeCellBoundaryGraph S).Adj u v ↔
      squareLattice.Adj u v ∧ ∃ e : LatticeBond,
        e.toSym2 = s(u,v) ∧
         (e.faceBase true ∈ S) ≠ (e.faceBase false ∈ S)  := by
  constructor
  · grind +locals
  · rintro ⟨hadj, e, hedge, hfaces⟩
    exact ⟨hadj, e, (mem_latticeCellBoundaryBonds S e).mpr hfaces, hedge⟩

end PottsDiscontinuity.FK
