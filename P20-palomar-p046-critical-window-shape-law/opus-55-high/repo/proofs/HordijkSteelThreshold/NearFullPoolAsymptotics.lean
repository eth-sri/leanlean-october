module

public import proofs.HordijkSteelThreshold.FixedPoolReactionLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology

variable (n m : ℕ)

def nearFullPoolSize  : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

theorem nearFullPoolSize_le  : nearFullPoolSize n m ≤ Fintype.card (Molecule n) := by
  have := Nat.div_mul_le_self (Fintype.card $ Molecule n) m
  have := Nat.mul_le_mul_right (Fintype.card (Molecule n)/m) $ Nat.sub_le m 1
  unfold nearFullPoolSize
  linarith

end HordijkSteelThreshold
