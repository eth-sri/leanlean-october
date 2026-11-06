module

public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.Torus.Corollary313Final

public section

open Finset

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity

theorem weightedMass_eq_correctedWeight {N M : ℕ}
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNpos : 0 < N) (hMpos : 0 < M) (A : Torus.RCConfig N M) :
    torusWeightedRCMass hN hM q hNpos hMpos A =
      Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A := by
  unfold torusWeightedRCMass torusLoopWeightFactor Torus.torusCorrectedRCWeight
  have hloop : Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ A : ℝ) =
      (2 / Real.sqrt q.val) ^
        TorusLoops.windingLoopCount hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ A :=
    by simp
  have hnet : Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) =
      (q.val ^ Torus.rcNetIndicator hN hM A)⁻¹ := by
    simp
  grind

theorem correspondenceScale_eq_normalization
    (q : Set.Ici (1 : ℝ)) (N M : ℕ) :
    torusCorrespondenceScale q N M = Torus.torusNormalization q N M := rfl

theorem contract_cor313_i_proved : contract_cor313_i := by
  intro q hq N M hN hM hNpos hMpos
  calc
    (∑ A : Torus.RCConfig N M, torusWeightedRCMass hN hM q hNpos hMpos A) =
        ∑ A : Torus.RCConfig N M,
          Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A := by
      simp [weightedMass_eq_correctedWeight]
    _ = Torus.torusNormalization q N M *
        SixVertex.Z6V (criticalSixVertexParameter q) N M := (Torus.corollary_313_i_final hN hM q hq ⟨0, hNpos⟩ ⟨0, hMpos⟩)
    _ = torusCorrespondenceScale q N M *
        SixVertex.Z6V (criticalSixVertexParameter q) N M := by
      rfl

theorem contract_cor313_ii_proved : contract_cor313_ii := by
  intro q hq N M hN hM hNpos hMpos
  let P := fun A =>
    Torus.rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1
  have hprovider := Torus.corollary_313_ii_final hN hM q hq ⟨0, hNpos⟩ ⟨0, hMpos⟩
  have hsum :
      (∑ A ∈ Finset.univ.filter P,
        torusWeightedRCMass hN hM q hNpos hMpos A) =
        ∑ A : {A : Torus.RCConfig N M // P A},
          Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A.val := by
    rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
      (fun A => Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A)]
    simp [weightedMass_eq_correctedWeight]
  rw [← hsum] at hprovider
  tauto

theorem contract_cor313_iii_proved : contract_cor313_iii := by
  intro q hq r N M hr hN hM hNpos hMpos
  let P := fun A =>
    r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMpos⟩ A
  have hprovider := Torus.corollary_313_iii_final hN hM q hq ⟨0, hNpos⟩ ⟨0, hMpos⟩ r
  have hsum :
      (∑ A ∈ Finset.univ.filter P,
        torusWeightedRCMass hN hM q hNpos hMpos A) =
        ∑ A : {A : Torus.RCConfig N M // P A},
          Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A.val := by
    rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
      (fun A => Torus.torusCorrectedRCWeight hN hM ⟨0, hNpos⟩ ⟨0, hMpos⟩ q A)]
    simp [weightedMass_eq_correctedWeight]
  rw [hsum, correspondenceScale_eq_normalization]
  tauto

end PottsDiscontinuity.RCMProof
