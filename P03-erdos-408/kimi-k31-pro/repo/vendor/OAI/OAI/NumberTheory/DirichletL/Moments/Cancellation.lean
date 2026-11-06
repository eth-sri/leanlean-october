module

public import OAI.NumberTheory.DirichletL.Moments.MaskedVolume

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCancellation
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum UniqueFactorizationMonoid QuadraticInitialBound
open CenteredMomentPrimary

end SevenEighths.CenteredMomentCancellation
end

end OAI
