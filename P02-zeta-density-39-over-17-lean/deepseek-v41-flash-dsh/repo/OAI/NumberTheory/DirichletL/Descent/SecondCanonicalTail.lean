module
public import OAI.NumberTheory.DirichletL.Descent.SecondMarkedTail
public import OAI.NumberTheory.DirichletL.Descent.SecondFreshTruncation
public import OAI.NumberTheory.DirichletL.Descent.SecondCutoffScale

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

end
end SevenEighths.InverseMoment

end OAI
