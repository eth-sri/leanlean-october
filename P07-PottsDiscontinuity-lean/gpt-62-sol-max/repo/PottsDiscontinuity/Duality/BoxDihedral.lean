/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.FK.BoxTranslation

@[expose] public section

namespace PottsDiscontinuity.FK
open MeasureTheory
noncomputable section

/-- The literal counterclockwise quarter-turn `(x,y) ↦ (-y,x)`. -/
def latticeQuarterTurn (v : LatticeVertex) : LatticeVertex := (-v.2, v.1)

/-- The inverse quarter-turn `(x,y) ↦ (y,-x)`. -/
def latticeQuarterTurnInv (v : LatticeVertex) : LatticeVertex := (v.2, -v.1)

@[simp] theorem latticeQuarterTurnInv_quarterTurn (v : LatticeVertex) :
    latticeQuarterTurnInv (latticeQuarterTurn v) = v := by
  ext <;> simp [latticeQuarterTurn, latticeQuarterTurnInv]

@[simp] theorem latticeQuarterTurn_quarterTurnInv (v : LatticeVertex) :
    latticeQuarterTurn (latticeQuarterTurnInv v) = v := by
  ext <;> simp [latticeQuarterTurn, latticeQuarterTurnInv]

lemma squareLattice_adj_quarterTurn_iff (u v : LatticeVertex) :
    squareLattice.Adj (latticeQuarterTurn u) (latticeQuarterTurn v) ↔
      squareLattice.Adj u v := by
  simp only [squareLattice_adj_iff, latticeQuarterTurn]
  omega

/-- The actual graph isomorphism for the literal quarter-turn. -/
def latticeQuarterTurnIso : squareLattice ≃g squareLattice where
  toFun := latticeQuarterTurn
  invFun := latticeQuarterTurnInv
  left_inv := latticeQuarterTurnInv_quarterTurn
  right_inv := latticeQuarterTurn_quarterTurnInv
  map_rel_iff' := by
    intro u v
    exact squareLattice_adj_quarterTurn_iff u v

lemma mem_latticeBox_quarterTurn_iff (c v : LatticeVertex) (r : ℕ) :
    latticeQuarterTurn v ∈ latticeBox (latticeQuarterTurn c) r ↔
      v ∈ latticeBox c r := by
  rw [mem_latticeBox, mem_latticeBox]
  simp only [latticeQuarterTurn]
  omega

end
end PottsDiscontinuity.FK
