module

public import OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceMask

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveEnergy
open HeckeFamily
open CenteredMomentRestrictedSource
open CenteredMomentSourceLiveColumn
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_divisor_energy (S : (ι ⊕ Fin 2) → Finset (Ideal ActualEisensteinCubic.O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R L : Ideal ActualEisensteinCubic.O)
    (ν : ι → Ideal ActualEisensteinCubic.O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal ActualEisensteinCubic.O)
    (f : Ideal ActualEisensteinCubic.O → ℂ) (keep : ActualEisensteinCubic.O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
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
