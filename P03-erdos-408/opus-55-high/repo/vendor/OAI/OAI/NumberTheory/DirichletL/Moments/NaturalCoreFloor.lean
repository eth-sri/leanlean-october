module

public import OAI.NumberTheory.DirichletL.Moments.PlainGlobalEnergy
public import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentNaturalCoreFloor
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O"=>HeckeFamily.O

end SevenEighths.CenteredMomentNaturalCoreFloor

end

end OAI
