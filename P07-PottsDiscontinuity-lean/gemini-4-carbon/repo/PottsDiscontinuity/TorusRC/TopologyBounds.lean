module

public import PottsDiscontinuity.TorusRC.CPrimeEstimate
public import PottsDiscontinuity.TorusRC.ElementaryTail
public import PottsDiscontinuity.TorusTopology.BarrierEvent

/-! # Quantitative reductions with the torus topology premises discharged -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- The proved implication B ∩ C′ ⇒ `U = 1` (`TorusTopology.hBCU_proved`) turns the full
corrected chain bound into an actual U=1 probability bound. -/
theorem torusRCU_one_probability_ge_chain (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (hNdiv : 8 ∣ N) (q : Set.Ici (1 : ℝ)) (n : ℕ)
    (hn : 0 < n) (h8n : 8 * n ≤ N) (hNM : N / 2 < M) :
    (fkOpenEnergy (torusRCBridgeParameters q) ^ (2 * (N / 4 + 2 * n)) *
      liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin
        (N / 4) rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M / (2 * n))) *
      torusRCProbability hN hM q (torusRCBarrier hNp hMp n) ≤
      torusRCProbability hN hM q {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1} :=
  (torusCPrime_mul_barrier_lower_bound hN hM hN4 hM4 hNp hMp hNdiv q n hn h8n hNM).trans
    (torusRCProbability_mono hN hM q fun A hA =>
      TorusTopology.hBCU_proved hN hM hNp hMp hNdiv n h8n hNM A hA.1 hA.2)

end PottsDiscontinuity.TorusRC
