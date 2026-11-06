module

public import OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceMask

@[expose] public section

namespace OAI

section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion

variable {ι : Type*} [Fintype ι]


theorem live_divisor_energy (S : (ι ⊕ Fin 2) → Finset (Ideal ActualEisensteinCubic.O))
     B   hB   C R L 
     ν   Wslot   P 
     W₁ W₂   X₁ X₂ Y₁ Y₂   B₁ B₂ 
     f   keep   W   K  :
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
      (fun I => (if L∣I then 1 else 0)*f I) W K=
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

end SevenEighths.CenteredMomentSecondLiveEnergy

end

end OAI
