module
public import OAI.NumberTheory.DirichletL.Moments.PlainGlobalEnergy
public import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalCoreFloor
open HeckeFamily HeckeRowClosure CenteredMomentCoreFloor CenteredMomentPlainGlobalEnergy
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

end SevenEighths.CenteredMomentNaturalCoreFloor

end

end OAI
