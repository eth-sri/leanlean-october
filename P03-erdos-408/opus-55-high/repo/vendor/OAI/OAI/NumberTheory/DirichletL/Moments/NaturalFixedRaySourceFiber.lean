module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePhysical
public import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight
open ProbeHighRowFamily ConcretePrimeRowBridge

lemma rowMaskElement_eq_fixed : rowMaskElement=fixedBadMask := by
  unfold rowMaskElement fixedBadMask
  ring

lemma excluded_one_ideal (χ : Character) (I : Ideal HeckeFamily.O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : HeckeFamily.O} (F : NaturalRow η z) (I : Ideal HeckeFamily.O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : HeckeFamily.O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal HeckeFamily.O)) (β : ι→Ideal HeckeFamily.O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

variable {M : Ideal HeckeFamily.O} [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (HeckeFamily.O⧸M)ˣ} (hH : RayOrthogonality.globalUnits M≤H)
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
