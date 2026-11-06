module

public import proofs.HordijkSteelThreshold.PeelingStabilization

public section

namespace RAFEmergenceApprox
open Classical HordijkSteelThreshold

theorem scalar_barrier_subset {X R : Type*} [Fintype X] [Fintype R]
    (O : ℕ → Finset R) (closure : Finset R → Finset X)
    (hO : Monotone O) (hc : Monotone closure) (k : ℕ)
    (hk : k ≤ Fintype.card X) (hkg : k ≤ (closure $ O k).card) (t : ℕ) :
    O k ⊆ peelingActiveAt (fun C : Finset X => O C.card) closure t := by
  induction t with
  | zero => aesop
  | succ t ih => exact hO $ hkg.trans $ Finset.card_le_card $ hc ih

end RAFEmergenceApprox
