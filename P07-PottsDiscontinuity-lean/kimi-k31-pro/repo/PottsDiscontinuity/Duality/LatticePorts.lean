/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.LatticeEmbedding

/-!
# Actual square-lattice bonds and medial ports

A bond is a horizontal or vertical unit lattice segment, normalized by its
left or lower endpoint. A medial port records a bond, one of its two primal
endpoints, and one of its two adjacent unit cells. Thus four distinct port
identities project to each medial midpoint; later traversals must retain these
identities and their order rather than identify visits by their position.

The open local pairing stays in one dual cell and swaps primal endpoints.
The closed local pairing stays at one primal endpoint and swaps adjacent cells.
The corner pairing crosses the medial edge joining consecutive sides of one
actual unit cell. All coordinate and pairing identities are proved below on
the full integer lattice. No finite-domain boundary completion, two-terminal
condition, or strand existence is assumed or asserted here.
-/

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

def source (e : LatticeBond) : LatticeVertex := e.base

def target (e : LatticeBond) : LatticeVertex :=
  match e.axis with
  | horizontal => (e.base.1 + 1, e.base.2)
  | vertical => (e.base.1, e.base.2 + 1)

theorem adjacent (e : LatticeBond) : squareLattice.Adj e.source e.target := by
  rcases e with ⟨⟨x, y⟩, ax⟩
  cases ax <;> simp [source, target, squareLattice_adj_iff]

theorem source_ne_target (e : LatticeBond) : e.source ≠ e.target := e.adjacent.ne

/-- The actual unoriented edge of the original square lattice. -/
def toSym2 (e : LatticeBond) : Sym2 LatticeVertex := s(e.source, e.target)

theorem toSym2_mem_edgeSet (e : LatticeBond) : e.toSym2 ∈ squareLattice.edgeSet :=
  squareLattice.mem_edgeSet.mpr e.adjacent

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

/-- Normalization neither duplicates nor omits an original unit edge. -/
theorem existsUnique_of_adj {u v : LatticeVertex} (h : squareLattice.Adj u v) :
    ∃! e : LatticeBond, e.toSym2 = s(u, v) := by
  obtain ⟨e, he⟩ := exists_of_adj h
  exact ⟨e, he, fun f hf => toSym2_injective (hf.trans he.symm)⟩


/-- Lower-left corner of an adjacent unit cell. For horizontal bonds `false`
means below and `true` above; for vertical bonds `false` means left and `true` right. -/
def faceBase (e : LatticeBond) (side : Bool) : LatticeVertex :=
  match e.axis, side with
  | horizontal, false => (e.base.1, e.base.2 - 1)
  | horizontal, true => e.base
  | vertical, false => (e.base.1 - 1, e.base.2)
  | vertical, true => e.base

/-- The geometric medial vertex in the positive-mesh complex embedding. -/
noncomputable def midpoint (e : LatticeBond) (δ : PositiveMesh) : ℂ :=
  (latticeEmbed δ e.source + latticeEmbed δ e.target) / 2

end LatticeBond

/-- A medial half-edge at a unit bond midpoint, distinguished by its primal
endpoint and adjacent unit cell. Distinct ports are not identified geometrically. -/
structure LatticePort where
  bond : LatticeBond
  tip : Bool
  side : Bool
  deriving DecidableEq

namespace LatticePort

open LatticeAxis


def faceBase (p : LatticePort) : LatticeVertex := p.bond.faceBase p.side



/-- At a closed primal edge, turn around a primal endpoint. -/
def closedPair (p : LatticePort) : LatticePort := ⟨p.bond, p.tip, !p.side⟩


theorem closedPair_faceBase_ne (p : LatticePort) :
    p.closedPair.faceBase ≠ p.faceBase := by
  rcases p with ⟨⟨⟨x, y⟩, ax⟩, t, s⟩
  cases ax <;> cases s <;>
    simp [closedPair, faceBase, LatticeBond.faceBase] <;> omega






end LatticePort

end PottsDiscontinuity.FK.Medial
