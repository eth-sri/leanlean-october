module

public import OAI.NumberTheory.DirichletL.Reflection.DyadicTail
public import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase


noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
