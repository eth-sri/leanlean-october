module
public import Mathlib

public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.Torus.Corollary313Final

@[expose] public section

open Finset

namespace PottsDiscontinuity.RCMProof



private theorem weightedMass_eq_correctedWeight {N M : ℕ}
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNpos : 0 < N) (hMpos : 0 < M) (A : Torus.RCConfig N M) :
    torusWeightedRCMass hN hM q hNpos hMpos A =
      Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A := by
  unfold torusWeightedRCMass torusLoopWeightFactor Torus.torusCorrectedRCWeight
  have hloop : Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ A ) =
      (2 / Real.sqrt q.val) ^
        TorusLoops.windingLoopCount hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ A :=
    Real.rpow_natCast _ _
  have hnet : Real.rpow q.val (- Torus.rcNetIndicator hN hM A ) =
      (q.val ^ Torus.rcNetIndicator hN hM A)⁻¹ := by
    simp_all
  rw [hloop, hnet]
  ring

private theorem correspondenceScale_eq_normalization
    (q : Set.Ici (1 : ℝ)) (N M : ℕ) :
    torusCorrespondenceScale q N M = Torus.torusNormalization q N M := rfl

theorem contract_cor313_i_proved : contract_cor313_i := fun q hq N M hN hM hNpos hMpos =>
                                                          Trans.trans
                                                            (Trans.trans (sum_congr rfl fun A a => weightedMass_eq_correctedWeight hN hM q hNpos hMpos A)
                                                              (Torus.corollary_313_i_final hN hM q hq ⟨0, hNpos⟩ ⟨0, hMpos⟩))
                                                            (Eq.mpr
                                                              (congrArg
                                                                (fun _a =>
                                                                  Torus.torusNormalization q N M * SixVertex.Z6V (criticalSixVertexParameter q) N M =
                                                                    _a * SixVertex.Z6V (criticalSixVertexParameter q) N M)
                                                                (correspondenceScale_eq_normalization q N M))
                                                              (Eq.refl (Torus.torusNormalization q N M * SixVertex.Z6V (criticalSixVertexParameter q) N M)))

theorem contract_cor313_ii_proved : contract_cor313_ii := by
  intro q hq N M hN hM hNpos hMpos
  let P  := fun A =>
    Torus.rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1
  have hprovider := Torus.corollary_313_ii_final hN hM q hq ⟨0, hNpos⟩ ⟨0, hMpos⟩
  have hsum :
       ∑ A ∈ Finset.univ.filter P,
        torusWeightedRCMass hN hM q hNpos hMpos A  =
        ∑ A : {A : Torus.RCConfig N M // P A},
          Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A.val := by
    rw [← Finset.sum_subtype (Finset.univ.filter P) (by  simp)
       (Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q) ]
    apply Finset.sum_congr rfl
    intro A hA
    exact weightedMass_eq_correctedWeight hN hM q hNpos hMpos A
  rw [← hsum] at hprovider
  
  exact hprovider

theorem contract_cor313_iii_proved : contract_cor313_iii := by
  intro q hq r N M hr hN hM hNpos hMpos
  let P  := fun A =>
    r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMpos⟩ A
  
  have hsum :
       ∑ A ∈ Finset.univ.filter P,
        torusWeightedRCMass hN hM q hNpos hMpos A  =
        ∑ A : {A : Torus.RCConfig N M // P A},
          Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A.val := by
    rw [← Finset.sum_subtype (Finset.univ.filter P) (by  simp)
       (Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q) ]
    apply Finset.sum_congr rfl
    intro A hA
    exact weightedMass_eq_correctedWeight hN hM q hNpos hMpos A
  rw [hsum]
  exact  Torus.corollary_313_iii_final hN hM q hq ⟨0, hNpos⟩ ⟨0, hMpos⟩ r 

end PottsDiscontinuity.RCMProof
