module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
public import OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow
local notation "O"=>HeckeFamily.O

end SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometry

end

end OAI
