module

public import OAI.NumberTheory.DirichletL.Moments.Bridge

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentInitial
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentBridge

variable {ι : Type*}

end SevenEighths.CenteredMomentInitial
end

end OAI
