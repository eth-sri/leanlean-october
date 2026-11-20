module
public import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
public import OAI.NumberTheory.DirichletL.Moments.AmplificationLiveMask

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSourceMask
open CanonicalQuadraticSieve CenteredMomentSecondSectorColumns CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentSecondSourceMask

end

end OAI
