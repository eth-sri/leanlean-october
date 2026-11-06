module
public import OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentFirstMaskedFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRemainingBox CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentFirstMaskedInput

end

end OAI
