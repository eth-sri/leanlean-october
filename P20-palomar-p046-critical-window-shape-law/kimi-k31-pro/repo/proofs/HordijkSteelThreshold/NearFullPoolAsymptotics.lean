module

public import proofs.HordijkSteelThreshold.HalfPoolAsymptotics

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology

def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

theorem nearFullPoolSize_le (n m : ℕ) : nearFullPoolSize n m ≤ Fintype.card (Molecule n) := by
  have h1 := Nat.mul_le_mul_right (Fintype.card (Molecule n)/m) (Nat.sub_le m 1)
  have h2 := Nat.div_mul_le_self (Fintype.card (Molecule n)) m
  dsimp [nearFullPoolSize]
  nlinarith

noncomputable def nearFullCatalystPool (n m : ℕ) : Finset (Molecule n) :=
  finiteInitialSegment (Molecule n) (nearFullPoolSize n m)

@[simp] theorem nearFullCatalystPool_card (n m : ℕ) :
    (nearFullCatalystPool n m).card = nearFullPoolSize n m :=
  card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)

end HordijkSteelThreshold
