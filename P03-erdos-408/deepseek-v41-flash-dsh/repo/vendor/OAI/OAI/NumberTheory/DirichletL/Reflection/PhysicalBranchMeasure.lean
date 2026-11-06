module

public import OAI.NumberTheory.DirichletL.Reflection.PhysicalIntegral
public import OAI.NumberTheory.DirichletL.Reflection.SumMeasure

set_option linter.privateModule false

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase


noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
