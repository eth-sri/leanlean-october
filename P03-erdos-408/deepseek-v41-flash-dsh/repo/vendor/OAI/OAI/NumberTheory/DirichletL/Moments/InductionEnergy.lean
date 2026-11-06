module

public import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentInductionEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability CenteredMomentCounting CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def energy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (X₁ X₂:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
    (Φ (‖eisEmbedding z‖^2/K)).re else 0

end SevenEighths.CenteredMomentInductionEnergy

end

end OAI
