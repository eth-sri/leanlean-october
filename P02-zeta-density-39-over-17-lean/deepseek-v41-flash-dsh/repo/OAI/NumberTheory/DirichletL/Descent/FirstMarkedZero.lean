module
public import OAI.NumberTheory.DirichletL.Descent.FirstMarkedColumns

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

end
end SevenEighths.InverseMoment

end OAI
