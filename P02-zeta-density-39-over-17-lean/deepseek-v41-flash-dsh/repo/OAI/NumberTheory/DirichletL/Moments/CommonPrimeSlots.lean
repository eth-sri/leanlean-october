module
public import OAI.NumberTheory.DirichletL.Moments.CommonAllocationSum

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPrimeSlots
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentSupport IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

end SevenEighths.CenteredMomentCommonPrimeSlots

end

end OAI
