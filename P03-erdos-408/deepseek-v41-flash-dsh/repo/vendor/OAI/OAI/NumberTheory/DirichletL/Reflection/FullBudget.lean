module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalFull
public import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase


noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
