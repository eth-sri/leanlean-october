module
public import OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
public import OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonSectorColumn
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearSource CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource RayFourExpansion ActualEisensteinCubic CenteredMomentSourceRow CompletedGauss
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentCommonSectorColumn

end

end OAI
