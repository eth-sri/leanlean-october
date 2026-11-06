module
public import OAI.NumberTheory.DirichletL.Descent.WholePriorityBranches

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O"=>ActualEisensteinCubic.O

end SevenEighths.InverseMoment

end

end OAI
