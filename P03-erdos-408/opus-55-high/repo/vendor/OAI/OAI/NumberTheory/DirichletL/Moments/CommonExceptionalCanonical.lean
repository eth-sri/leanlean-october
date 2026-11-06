module

public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricCanonical

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonExceptionalCanonical
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentCommonExceptionalCanonical

end

end OAI
