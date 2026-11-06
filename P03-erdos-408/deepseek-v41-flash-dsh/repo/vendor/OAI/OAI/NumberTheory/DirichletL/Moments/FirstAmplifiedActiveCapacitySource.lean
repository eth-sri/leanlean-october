module

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedCapacitySource
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondActiveErrorGates
public import OAI.NumberTheory.DirichletL.Moments.SecondCapacitySourceShift
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
public import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic CenteredMomentSourceLiveColumn CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

theorem active_error_volume (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (errorInput s C R B τ t Q k Bp υ v)=
      volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [errorInput,child_volume _ Q hQ k hslot,active_volume,common_volume]
  ring

end SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource

end

end OAI
