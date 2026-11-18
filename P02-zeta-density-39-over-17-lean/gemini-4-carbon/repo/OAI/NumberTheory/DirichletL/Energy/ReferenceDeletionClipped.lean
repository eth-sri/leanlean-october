module
public import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionCapacity

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionClipped
open HeckeFamily CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget

local notation "O" => HeckeFamily.O

end SevenEighths.CenteredMomentEnergyReferenceDeletionClipped

end

end OAI
