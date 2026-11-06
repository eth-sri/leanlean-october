module
public import OAI.NumberTheory.DirichletL.Moments.AmplificationRectangle

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationMask
open CenteredMomentRectangle CenteredMomentAmplificationRectangle CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentAmplificationMask

end

end OAI
