module

public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalPhysical
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
public import OAI.NumberTheory.DirichletL.Moments.SecondSupportedChildren
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open RayFourExpansion CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns
open CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondDyadicRowSupport
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalCommonHarmonic

def canonicalRadial (τ:Character)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)

lemma sourceRadial_eq_canonical {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (hm:m≠0)(hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)(n:Fin 4→ℤ):
    sourceRadial (nonexceptional η χ Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))
      ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)=
      canonicalRadial (τ χ) Q n:=by
  have he:nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z):=by
    funext z
    exact propext (h.nonexceptional_iff χ Q m z hm hml hm2)
  simp only [canonicalRadial,he]

end SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock

end

end OAI
