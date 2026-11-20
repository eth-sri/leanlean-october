module

public import OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseSecondFibers CompletedGauss
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.InverseMoment
end

end OAI
