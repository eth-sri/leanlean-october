module
public import OAI.NumberTheory.DirichletL.Moments.Primary
public import OAI.NumberTheory.DirichletL.Moments.Mask

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMaskedVolume
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson IdealMobiusDivisorSum UniqueFactorizationMonoid QuadraticInitialBound CenteredMomentPrimary CenteredMomentMask

end SevenEighths.CenteredMomentMaskedVolume
end

end OAI
