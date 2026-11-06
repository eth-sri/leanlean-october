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
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound Filter CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren CenteredMomentSecondPhysicalBlock CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel CenteredMomentSecondPhysicalCost CenteredMomentExceptionalAmplitudePair CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice CenteredMomentOriginalCommonHarmonic




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
