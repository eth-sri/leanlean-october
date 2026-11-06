module
public import OAI.NumberTheory.DirichletL.Moments.EligibleEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPairedEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentPairedEligibleEnergy

end

end OAI
