module

public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.Torus.Corollary313Final

@[expose] public section

open Finset

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity

private theorem weightedMass_eq_correctedWeight {N M : ℕ}
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNpos : 0 < N) (hMpos : 0 < M) (A : Torus.RCConfig N M) :
    torusWeightedRCMass hN hM q hNpos hMpos A =
      Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A := by
  simp only [torusWeightedRCMass, torusLoopWeightFactor, Torus.torusCorrectedRCWeight, mul_div_assoc]

theorem contract_cor313_i_proved : contract_cor313_i := by
  intro q hq N M hN hM hNp hMp
  simp only [weightedMass_eq_correctedWeight]
  exact Torus.corollary_313_i_final hN hM q hq _ _

theorem contract_cor313_ii_proved : contract_cor313_ii := by
  intro q hq N M hN hM hNp hMp
  simp only [weightedMass_eq_correctedWeight]
  rw [Finset.sum_subtype (p := fun A => Torus.rcVerticalWinding hN hM ⟨0,hMp⟩ A = 1) _ (by simp)]
  exact Torus.corollary_313_ii_final hN hM q hq _ _

theorem contract_cor313_iii_proved : contract_cor313_iii := by
  intro q hq r N M hr hN hM hNp hMp
  simp only [weightedMass_eq_correctedWeight]
  rw [Finset.sum_subtype (p := fun A => r ≤ Torus.rcVerticalWinding hN hM ⟨0,hMp⟩ A) _ (by simp)]
  exact Torus.corollary_313_iii_final hN hM q hq _ _ r

end PottsDiscontinuity.RCMProof
