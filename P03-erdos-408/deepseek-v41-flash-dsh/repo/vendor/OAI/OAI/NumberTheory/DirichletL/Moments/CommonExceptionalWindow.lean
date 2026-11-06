module

public import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalHeight
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section



namespace SevenEighths.CenteredMomentCommonExceptionalWindow

local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentCommonExceptionalWindow

end

end OAI
