module
public import OAI.NumberTheory.DirichletL.Moments.FirstPoisson
public import OAI.NumberTheory.DirichletL.Moments.Primitive

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson

end SevenEighths.CenteredMomentBridge
end

end OAI
