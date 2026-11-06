module

public import OAI.NumberTheory.DirichletL.Moments.RankinLabels

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinScale
open IdealMobiusDivisorSum CenteredMomentRankinRadical CenteredMomentRankinLabels
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentRankinScale

end

end OAI
