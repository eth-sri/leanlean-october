module
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityLedger
public import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm CenteredMomentSectorLocalization
local notation "O"=>ActualEisensteinCubic.O

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
