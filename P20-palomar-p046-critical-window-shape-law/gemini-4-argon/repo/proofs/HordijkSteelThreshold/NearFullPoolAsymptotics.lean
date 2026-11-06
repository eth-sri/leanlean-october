module

public import proofs.HordijkSteelThreshold.HalfPoolAsymptotics

@[expose] public section

namespace HordijkSteelThreshold
open RAF.Polymer

def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

theorem nearFullPoolSize_le (n m : ℕ) : nearFullPoolSize n m ≤ Fintype.card (Molecule n) :=
  (Nat.mul_le_mul_right _ (Nat.sub_le m 1)).trans (Nat.mul_div_le _ m)

end HordijkSteelThreshold
