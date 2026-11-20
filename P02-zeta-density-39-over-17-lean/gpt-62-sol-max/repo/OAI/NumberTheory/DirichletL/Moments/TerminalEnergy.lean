module
public import OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentTerminalEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentTerminalEnergy

end

end OAI
