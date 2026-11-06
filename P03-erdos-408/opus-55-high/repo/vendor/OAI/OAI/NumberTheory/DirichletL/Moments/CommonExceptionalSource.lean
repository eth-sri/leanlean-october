module

public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalMass
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonExceptionalSource
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentCommonExceptionalSource

end

end OAI
