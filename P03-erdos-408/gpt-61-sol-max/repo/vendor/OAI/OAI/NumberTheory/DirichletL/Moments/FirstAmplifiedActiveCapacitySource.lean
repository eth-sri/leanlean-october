module

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacitySource
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondActiveErrorGates
public import OAI.NumberTheory.DirichletL.Moments.SecondCapacitySourceShift
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
public import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius

variable {ι:Type*}[Fintype ι]


open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput

theorem active_error_volume (s : Input ι)  C R 
     B   τ   t 
     Q  (hQ : Q≠0)  k 
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
     Bp 
     υ   v  :
    volume (errorInput s C R B τ t Q k Bp υ v)=
      volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [errorInput,child_volume _ Q hQ k hslot,active_volume,common_volume]
  ring

end SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource

end

end OAI
