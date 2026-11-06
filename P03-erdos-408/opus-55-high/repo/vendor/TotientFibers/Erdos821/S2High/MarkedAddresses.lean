module

public import Erdos821.S2High.PivotAssignments

@[expose] public section

noncomputable section

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m n B : ℕ} {A : Model F P J m}

local notation "PivotAddrFin" => BirthAddressFin P (J + F.ell) n B
local notation "PivotAddr" => Erdos821.S2Core.BirthAddress P (J + F.ell) n B
abbrev PivotBlocks (pi : Finset (Finset PivotAddrFin)) := {C : Finset PivotAddrFin // C ∈ pi}

def performedAddressSet (pi : Finset (Finset PivotAddrFin)) : Finset PivotAddrFin :=
  pi.biUnion id

def blockContaining (pi : Finset (Finset PivotAddrFin))
    (j : PivotAddrFin) (hj : j ∈ performedAddressSet pi) : PivotBlocks pi := by
  classical
  let h := Finset.mem_biUnion.mp hj
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem blockContaining_mem (pi : Finset (Finset PivotAddrFin))
    (j : PivotAddrFin) (hj : j ∈ performedAddressSet pi) :
    j ∈ (blockContaining pi j hj).val := by
  classical
  exact (Classical.choose_spec (Finset.mem_biUnion.mp hj)).2

theorem blockContaining_eq (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (j : PivotAddrFin) (hj : j ∈ performedAddressSet pi)
    (C : Finset PivotAddrFin) (hC : C ∈ pi) (hjC : j ∈ C) :
    blockContaining pi j hj = ⟨C, hC⟩ := by
  apply Subtype.ext
  by_contra hne
  have hdis := hpi.2 (by simp) hC hne
  exact (Finset.disjoint_left.mp hdis (blockContaining_mem pi j hj)) hjC

end Erdos821.S2High
