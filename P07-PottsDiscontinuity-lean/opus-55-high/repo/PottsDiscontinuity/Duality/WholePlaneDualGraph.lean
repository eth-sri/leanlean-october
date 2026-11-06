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

section
variable (b : LatticeBond)
@[simp] theorem dualBondOfPrimal_source  :
    (dualBondOfPrimal b).source = b.faceBase false := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> rfl

@[simp] theorem dualBondOfPrimal_target  :
    (dualBondOfPrimal b).target = b.faceBase true := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, LatticeBond.target, LatticeBond.faceBase]
end

/-- The literal whole-plane closed-dual graph on face bases. -/
def wholePlaneClosedDualGraph (ω : LatticeConfiguration) : SimpleGraph LatticeVertex where
  Adj u v := ∃ b : LatticeBond,
    latticeConfigurationBondState ω b = false ∧
      (u = b.faceBase false ∧ v = b.faceBase true ∨
       u = b.faceBase true ∧ v = b.faceBase false)
  symm := ⟨by
    grind⟩
  loopless := ⟨by rintro u ⟨⟨⟨x, y⟩, _ | _⟩, _, h | h⟩ <;> simp [LatticeBond.faceBase, Prod.ext_iff] at h <;> omega⟩


section
variable (ω : LatticeConfiguration) (u v : LatticeVertex)
theorem wholePlaneClosedDualGraph_adj_iff  :
    (wholePlaneClosedDualGraph ω).Adj u v ↔
      ∃ b : LatticeBond, latticeConfigurationBondState ω b = false ∧
        (u = b.faceBase false ∧ v = b.faceBase true ∨
         u = b.faceBase true ∧ v = b.faceBase false) := Iff.rfl

/-- Dual graph steps are exactly the normalized nearest-neighbor edges whose
crossing primal bond is closed. -/
theorem wholePlaneClosedDualGraph_adj_iff_dualBond  :
    (wholePlaneClosedDualGraph ω).Adj u v ↔
      ∃ d : LatticeBond,
        latticeConfigurationBondState ω (primalBondOfDual d) = false ∧
        (u = d.source ∧ v = d.target ∨ u = d.target ∧ v = d.source) := by
  constructor
  · rintro ⟨b, hclosed, huv | huv⟩
    · refine ⟨dualBondOfPrimal b, ?_, ?_⟩
      · simp_all
      simp_all
    · refine ⟨dualBondOfPrimal b, ?_, ?_⟩
      · simp_all
      simp_all
  · rintro ⟨d, hclosed, huv | huv⟩
    · refine ⟨primalBondOfDual d, ?_, ?_⟩
      · omega
      grind [primalBondOfDual, dualBondOfPrimal_source, dualBondOfPrimal_primalBondOfDual, dualBondOfPrimal_target]
    · refine ⟨primalBondOfDual d, ?_, ?_⟩
      · omega
      grind [primalBondOfDual, dualBondOfPrimal_source, dualBondOfPrimal_primalBondOfDual, dualBondOfPrimal_target]
end

end
end PottsDiscontinuity.FK.Medial
