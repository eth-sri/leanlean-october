module
public import OAI.NumberTheory.DirichletL.Moments.HeckeExpansion
public import OAI.NumberTheory.DirichletL.Moments.Forcing

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExceptionalEnergy
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

end SevenEighths.CenteredMomentHeckeExceptionalEnergy

end

end OAI
