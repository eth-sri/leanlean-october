module

public import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
public import OAI.NumberTheory.DirichletL.Moments.RetainedEnergy

@[expose] public section

namespace OAI


open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile


section
variable {η : Character} {z : HeckeFamily.O} (F : NaturalRow η z) (R : Ideal HeckeFamily.O) (hR : R≠0)
include η z F R hR

lemma NaturalRow.masked_plain      
         W   t X  :
    rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z W t X=
      twistedIdealSum (excluded F.character R) W t X := rowTwistedSum_eq η (excluded F.character R) (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W t X

lemma NaturalRow.masked_slot      
         S   β   t  :
    rowSlot η (fixedBadMask*idealGenerator R) 1 z S β t=
      ∑I∈S,β I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t) := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR I,one_mul]

end

theorem NaturalRow.masked_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : HeckeFamily.O} (F : NaturalRow η z) (R : Ideal HeckeFamily.O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal HeckeFamily.O))  β 
     P   t X₁ X₂  :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) W₁ t X₁*
          twistedIdealSum (excluded F.character R) W₂ t X₂)*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  simp only [positiveSlotRow,F.masked_plain R hR,F.masked_slot R hR]

end SevenEighths.CenteredMomentNaturalRowSource



end OAI
