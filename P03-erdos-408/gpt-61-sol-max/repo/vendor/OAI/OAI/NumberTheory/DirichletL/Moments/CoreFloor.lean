module

public import OAI.NumberTheory.DirichletL.Moments.BottomStage

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCoreFloor
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT


 def zeroRow (η:Character) (m A z:HeckeFamily.O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

 def zeroEnergy (η:Character) (m A:HeckeFamily.O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial) :=
  ∑'z:HeckeFamily.O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0

 theorem zero_energy_eq  η   m A   t   W₁ W₂   X₁ X₂   r :
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r=
    energy η m A t W₁ W₂ (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ r.keep r.profile r.scale:=by
  simp [zeroEnergy,energy,zeroRow,positiveSlotRow]

end SevenEighths.CenteredMomentCoreFloor

end

end OAI
