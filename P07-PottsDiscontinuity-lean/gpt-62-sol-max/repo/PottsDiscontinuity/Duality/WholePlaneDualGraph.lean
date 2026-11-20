/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.BondStates

@[expose] public section

namespace PottsDiscontinuity.FK.Medial

open PottsDiscontinuity.FK

noncomputable section

/-- The normalized dual bond crossing a primal bond, with lower/left endpoint
as its base. -/
def dualBondOfPrimal (b : LatticeBond) : LatticeBond :=
  match b.axis with
  | .horizontal => ⟨(b.base.1, b.base.2 - 1), .vertical⟩
  | .vertical => ⟨(b.base.1 - 1, b.base.2), .horizontal⟩

/-- The primal bond crossing a normalized dual bond. This is the shifted
inverse of `dualBondOfPrimal`. -/
def primalBondOfDual (d : LatticeBond) : LatticeBond :=
  match d.axis with
  | .horizontal => ⟨(d.base.1 + 1, d.base.2), .vertical⟩
  | .vertical => ⟨(d.base.1, d.base.2 + 1), .horizontal⟩

@[simp] theorem primalBondOfDual_dualBondOfPrimal (b : LatticeBond) :
    primalBondOfDual (dualBondOfPrimal b) = b := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, primalBondOfDual]

@[simp] theorem dualBondOfPrimal_primalBondOfDual (d : LatticeBond) :
    dualBondOfPrimal (primalBondOfDual d) = d := by
  rcases d with ⟨⟨x,y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, primalBondOfDual]

@[simp] theorem dualBondOfPrimal_source (b : LatticeBond) :
    (dualBondOfPrimal b).source = b.faceBase false := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> rfl

@[simp] theorem dualBondOfPrimal_target (b : LatticeBond) :
    (dualBondOfPrimal b).target = b.faceBase true := by
  grind [dualBondOfPrimal, LatticeBond.target, LatticeBond.faceBase]

end
end PottsDiscontinuity.FK.Medial
