module

public import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalHeight
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalCanonical

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonExceptionalCanonicalWindow
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentCommonExceptionalCanonicalWindow

end

end OAI
