module
public import OAI.NumberTheory.DirichletL.Moments.PairedEligibleEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentPairedEligibleEnergy
open CenteredMomentUniformDivisorShell CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentUniformEligibleEnergy

end

end OAI
