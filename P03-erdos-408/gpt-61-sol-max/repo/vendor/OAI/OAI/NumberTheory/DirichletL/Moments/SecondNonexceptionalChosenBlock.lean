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
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound


open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]


open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock  
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost   CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic  

def canonicalRadial (τ:Character)(Q:Ideal ActualEisensteinCubic.O)(n:Fin 4→ℤ):=
  sourceRadial (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)

lemma sourceRadial_eq_canonical {η:Character}{C D:Ideal ActualEisensteinCubic.O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ) χ  Q  m 
    (hm:m≠0)(hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:ActualEisensteinCubic.O)∣m) n :
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
