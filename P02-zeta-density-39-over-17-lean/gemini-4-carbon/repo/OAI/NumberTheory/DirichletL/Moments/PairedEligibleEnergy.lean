module
public import OAI.NumberTheory.DirichletL.Moments.EligibleEnergy


@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPairedEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.CenteredMomentPairedEligibleEnergy

end

end OAI
