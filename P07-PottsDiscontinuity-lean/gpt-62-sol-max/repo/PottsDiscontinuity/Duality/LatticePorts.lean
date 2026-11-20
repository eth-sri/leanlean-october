/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.FK.Lattice
public import Mathlib.Tactic

/-! Normalized bonds of the square lattice and their adjacent faces. -/

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

/-- The two axes of a normalized unit lattice bond. -/
inductive LatticeAxis
  | horizontal
  | vertical
  deriving DecidableEq

/-- A unit bond, based at its left endpoint if horizontal or lower endpoint if vertical. -/
structure LatticeBond where
  base : LatticeVertex
  axis : LatticeAxis
  deriving DecidableEq

namespace LatticeBond

open LatticeAxis

section

variable (e : LatticeBond)

def source : LatticeVertex := e.base

def target : LatticeVertex :=
  match e.axis with
  | horizontal => (e.base.1 + 1, e.base.2)
  | vertical => (e.base.1, e.base.2 + 1)

theorem adjacent : squareLattice.Adj e.source e.target := by
  grind [source, target, squareLattice_adj_iff]

theorem source_ne_target : e.source ≠ e.target := e.adjacent.ne

/-- The actual unoriented edge of the original square lattice. -/
def toSym2 : Sym2 LatticeVertex := s(e.source, e.target)

theorem toSym2_mem_edgeSet : e.toSym2 ∈ squareLattice.edgeSet :=
  squareLattice.mem_edgeSet.mpr e.adjacent

end

theorem toSym2_injective : Function.Injective toSym2 := by
  rintro ⟨⟨x, y⟩, ax⟩ ⟨⟨z, w⟩, az⟩ h
  cases ax <;> cases az <;>
    simp only [toSym2, source, target, Sym2.eq_iff, Prod.mk.injEq] at h
  all_goals rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp_all
  all_goals omega

/-- Every actual nearest-neighbor edge has a normalized bond representative. -/
theorem exists_of_adj {u v : LatticeVertex} (h : squareLattice.Adj u v) :
    ∃ e : LatticeBond, e.toSym2 = s(u, v) := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  simp only [squareLattice_adj_iff] at h
  rcases h with ⟨h | h, rfl⟩ | ⟨rfl, h | h⟩
  · subst z
    exact ⟨⟨(x, y), horizontal⟩, rfl⟩
  · subst x
    exact ⟨⟨(z, y), horizontal⟩, Sym2.eq_swap⟩
  · subst w
    exact ⟨⟨(x, y), vertical⟩, rfl⟩
  · subst y
    exact ⟨⟨(x, w), vertical⟩, Sym2.eq_swap⟩

/-- Lower-left corner of an adjacent unit cell. For horizontal bonds `false`
means below and `true` above; for vertical bonds `false` means left and `true` right. -/
def faceBase (e : LatticeBond) (side : Bool) : LatticeVertex :=
  match e.axis, side with
  | horizontal, false => (e.base.1, e.base.2 - 1)
  | horizontal, true => e.base
  | vertical, false => (e.base.1 - 1, e.base.2)
  | vertical, true => e.base

end LatticeBond

end PottsDiscontinuity.FK.Medial
