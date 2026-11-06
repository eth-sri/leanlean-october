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





end HordijkSteelThreshold
