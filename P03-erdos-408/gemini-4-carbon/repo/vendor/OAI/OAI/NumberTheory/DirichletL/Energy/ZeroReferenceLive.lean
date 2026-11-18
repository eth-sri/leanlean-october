module

public import OAI.NumberTheory.DirichletL.Energy.ZeroReferencePower
public import OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceLive
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePower CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

end SevenEighths.CenteredMomentEnergyZeroReferenceLive

end

end OAI
