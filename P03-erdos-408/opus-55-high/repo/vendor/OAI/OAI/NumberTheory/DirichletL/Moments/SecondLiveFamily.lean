module

public import OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondBlockSupport
public import OAI.NumberTheory.DirichletL.Moments.SecondReducedPredicate

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondLiveFamily
local notation "O" => HeckeFamily.O

end SevenEighths.CenteredMomentSecondLiveFamily

end

end OAI
