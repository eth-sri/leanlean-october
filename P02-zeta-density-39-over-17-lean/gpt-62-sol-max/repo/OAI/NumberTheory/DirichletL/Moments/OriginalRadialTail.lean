module
public import OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison
public import OAI.NumberTheory.DirichletL.Moments.InductionEnergy

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentOriginalRadialTail
open HeckeFamily ConcreteTraceCRT CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability CenteredMomentOriginalRadialComparison QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

end SevenEighths.CenteredMomentOriginalRadialTail

end

end OAI
