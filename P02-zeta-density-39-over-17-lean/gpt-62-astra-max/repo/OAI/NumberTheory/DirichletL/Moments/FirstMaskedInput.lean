module
public import OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstMaskedFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRemainingBox
open CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentFirstMaskedInput

end

end OAI
